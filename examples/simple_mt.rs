use ark_bn254::{Bn254 as E, Fr as F};
use ark_crypto_primitives::merkle_tree::Path;
use ark_ff::Zero;
use ark_groth16::Groth16;
use ark_r1cs_std::{eq::EqGadget, fields::fp::FpVar, prelude::Boolean};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, Result as ArkResult, ToConstraintField,
};
use ark_snark::SNARK;
use incrementalmerkletree_testing::{
    Tree, incremental_int_tree::IntTreePath, tree_util::PoseidonTreeConfig,
};
use rand::thread_rng;
use std::time::SystemTime;
use zk_callbacks::{
    generic::{
        bulletin::{CallbackBul, JoinableBulletin, UserBul},
        interaction::{
            Callback, Interaction, generate_keys_for_statement_in,
            generate_keys_for_statement_in_mt,
        },
        object::{Id, Time},
        scan::{PubScanArgs, get_scan_interaction},
        service::ServiceProvider,
        user::{User, UserVar},
    },
    impls::{
        centralized::{
            crypto::{FakeSigPrivkey, FakeSigPubkey, NoSigOTP, PlainTikCrypto},
            ds::sigstore::{GRSchnorrCallbackStore, GRSchnorrObjStore, GRSchnorrStore},
        },
        decentralized::ds::treestore::{DeCentralStore, IMTObjStore, MTCallbackStore},
        hash::Poseidon,
    },
    scannable_zk_object,
};

const INT_TREE_DEPTH: u8 = 8;

// Initialize a zk-object!
#[scannable_zk_object(F)]
#[derive(Default)]
pub struct TestData {
    pub token1: F,
    pub token2: F,
}

// How many callbacks we'll be scanning in when we go to the server for a scan (this can vary! In
// this example its constant, you will just have to generate multiple proving keys for different #
// of callbacks).
const NUMSCANS: usize = 1;

// Argument for the callback (we only have a single callback here, and the argument is a single
// field element.
type CBArg = F;
type CBArgVar = FpVar<F>;

// The wrapper "User" type around our zk-object.
type U = User<F, TestData>;
type UV = UserVar<F, TestData>;

// The crypto we are using for authenticity and argument hiding.
type Cr = PlainTikCrypto<F>;

// The type for the callback (what data it takes in: a user and an argument, in this case a field
// element).
type CB = Callback<F, TestData, CBArg, CBArgVar>;

// The first type of interaction (doing a method update, which does nothing so far)
type Int1 = Interaction<F, TestData, (), (), (), (), CBArg, CBArgVar, 1>;

// The scanning type: Most of this is unneccessary to understand, but really what it states is
//  - The field and user (F, TestUserData2)
//  - The callback argument (F, FpVar<F>)
//  - The method of providing ticket authenticity and hiding arguments (NoSigOTP<F>)
//  - The callback bulletin (GRSchnorrCallbackStore<F>)
//  - The number of callbacks
//
//  Note that the NoSigOTP in this case is centralized: there is no need to provide
//  authenticity, so signatures are (), and encryption is via a OTP
//
//  The actual type consists of membership data and the current time (public data).
type PubScan =
    PubScanArgs<F, TestData, F, FpVar<F>, Cr, MTCallbackStore<F, INT_TREE_DEPTH, F>, NUMSCANS>;

// Two types of interactions: updating the user normally with Int1, or updating the user with a
// scan through IntScan.

// The user is incrementing the token by 1 each time the method is called.
fn int_meth<'a>(tu: &'a U, _pub_args: (), _priv_args: ()) -> U {
    let mut a = tu.clone();
    a.data.token1 += F::from(1);

    // We could update token2 here! If you want :), there's nothing enforcing we need to keep it
    // the same.
    a
}

// Enforce that token1 in [0, 1, 2] (user can pretty much pick token2). Additionally, enforce
// that token1 is identical to (before + 1). This is effectively a rate limit: The user can
// only do an interaction twice before being unable to produce a proof.
//
// Note that there are no enforcements on token2, so it can be whatever the user wants.
fn int_meth_pred<'a>(
    tu_old: &'a UV,
    tu_new: &'a UV,
    _pub_args: (),
    _priv_args: (),
) -> ArkResult<Boolean<F>> {
    let l0 = tu_new.data.token1.is_eq(&FpVar::Constant(F::from(0)))?;
    let l1 = tu_new.data.token1.is_eq(&FpVar::Constant(F::from(1)))?;
    let l2 = tu_new.data.token1.is_eq(&FpVar::Constant(F::from(2)))?;
    let o2 = tu_old.data.token1.clone() + FpVar::Constant(F::from(1));
    let b2 = tu_new.data.token1.is_eq(&o2)?;
    Ok((l0 | l1 | l2) & b2)
}

// We can also prove arbitrary predicates to the server. Here, we just prove that our token2 value
// is 3. Could be for some kind of lottery or something?
fn some_pred<'a, 'b>(
    tu: &'a UV,
    _com: &'b FpVar<F>,
    _pub_args: (),
    _priv_args: (),
) -> ArkResult<Boolean<F>> {
    tu.data.token2.is_eq(&FpVar::Constant(F::from(3)))
}

// The callback method here allows the *server* to call a method on the user: Here the argument (F)
// being passed in can be selected by the server, and the user is forced to set their token1 to
// `args`.
fn cb_meth<'a>(tu: &'a U, args: F) -> U {
    let mut out = tu.clone();
    out.data.token2 = tu.data.token2 + args;
    out
}

// The proof that enforces the callback that the server calls.
fn cb_pred<'a>(tu_old: &'a UV, args: FpVar<F>) -> ArkResult<UV> {
    let mut tu_new = tu_old.clone();
    tu_new.data.token2 = tu_new.data.token2 + args;
    Ok(tu_new)
}

fn main() {
    // SERVER SETUP
    let mut rng = thread_rng();

    // create a single callback type
    let cb: CB = Callback {
        method_id: Id::from(0),
        expirable: false,
        expiration: Time::from(300),
        method: cb_meth,
        predicate: cb_pred,
    };

    // irrelevant callback type, we create it to test the checks
    let cb2: CB = Callback {
        method_id: Id::from(1),
        expirable: true,
        expiration: Time::from(1),
        method: cb_meth,
        predicate: cb_pred,
    };

    println!("[SERVER] INIT...");
    // The store for user objects

    let start = SystemTime::now();

    let mut store: DeCentralStore<F, INT_TREE_DEPTH, F> = DeCentralStore::new(&mut rng);

    println!(
        "\t (time) Generated data structures: {:?}",
        start.elapsed().unwrap()
    );

    // The list of valid callback methods
    let cb_methods = vec![cb.clone(), cb2.clone()];

    // The first type of allowed interaction: a standard interaction
    let interaction: Int1 = Interaction {
        meth: (int_meth, int_meth_pred),
        callbacks: [cb.clone()],
    };

    // Generate keys for interaction 1, callback interaction, and proving a specific statement
    // about users

    //let test = PlainTikCrypto::new(store.callback_bul.memb_tree.get_root());
    // For circuit generation
    let ex: PubScanArgs<
        F,
        TestData,
        F,
        FpVar<F>,
        Cr,
        MTCallbackStore<F, INT_TREE_DEPTH, F>,
        NUMSCANS,
    > = PubScanArgs {
        memb_pub: [store.callback_bul.memb_tree.get_root().into(); NUMSCANS],
        is_memb_data_const: false,
        nmemb_pub: [store.callback_bul.nmemb_tree.get_root().into(); NUMSCANS],
        is_nmemb_data_const: false,
        cur_time: F::from(0),
        bulletin: store.callback_bul.clone(),
        cb_methods: cb_methods.clone(),
    };

    println!("[SERVER] PROOF KEY GENERATION...");

    let start = SystemTime::now();

    let path_default: IntTreePath<F> = IntTreePath {
        0: Path {
            leaf_sibling_hash: F::default(),
            auth_path: vec![F::zero(); INT_TREE_DEPTH as usize - 1],
            leaf_index: 0,
        },
    };

    // generate keys for the method described initially
    let (pk, vk) =
        interaction // see interaction
            .generate_keys_mt::<Poseidon<2>, Groth16<E>, Cr, IMTObjStore<F, INT_TREE_DEPTH>>(
                &mut rng,
                None,
                (),
                false,
                path_default.clone(),
            );
    // generate keys for the callback scan
    let (pks, vks) = get_scan_interaction::<
        _,
        _,
        _,
        _,
        _,
        MTCallbackStore<F, INT_TREE_DEPTH, F>,
        Poseidon<2>,
        NUMSCANS,
    >()
    .generate_keys_mt::<Poseidon<2>, Groth16<E>, Cr, IMTObjStore<F, INT_TREE_DEPTH>>(
        &mut rng,
        None,
        ex,
        true,
        path_default.clone(),
    );

    // generate keys for the arbitrary predicate
    let (pki, vki) = generate_keys_for_statement_in_mt::<
        F,
        Poseidon<2>,
        TestData,
        (),
        (),
        (),
        (),
        Groth16<E>,
        IMTObjStore<F, INT_TREE_DEPTH>,
    >(&mut rng, some_pred, None, (), path_default.clone());
    //>(&mut rng, some_pred, Some(store.obj_bul.get_root()), ());

    println!(
        "\t (time) Generated proof keys: {:?}",
        start.elapsed().unwrap()
    );
    println!("[SERVER] Init done! \n\n");

    // END SERVER, START USER

    // Create a single user

    println!("[USER] Creation... ");
    let mut u = User::create(
        TestData {
            token1: F::from(0), // Try changing this to 1 or 2 to see what happens!
            token2: F::from(3), // Try changing this off of 3 to see what happens!
        },
        &mut rng,
    );
    println!("[USER] Created! User: {:o}", u);

    println!("MT root before user is {:?}", store.obj_bul.get_root());
    // Join in as a user
    let _ = <IMTObjStore<F, INT_TREE_DEPTH> as JoinableBulletin<F, TestData>>::join_bul(
        &mut store.obj_bul,
        u.commit::<Poseidon<2>>(),
        (),
    );
    println!("[USER] joined! \n\n");
    println!("MT root after user is {:?}", store.obj_bul.get_root());
    store.obj_bul.tree.merkle_tree.checkpoint(0);

    println!("leaves are {:?}", store.obj_bul.tree.leaves);
    println!("user commit is {:?}", u.commit::<Poseidon<2>>());
    let path = store.obj_bul.get_path_of(&u.commit::<Poseidon<2>>());
    println!("user path is {:?}", path);
    println!("user path len is {:?}", path.unwrap().0.auth_path.len());

    println!("[USER] Generating proof... ");
    let start = SystemTime::now();
    // Prove a statement about itself (and how it lies within the store)
    let proof = u
        .prove_statement_and_in::<Poseidon<2>, (), (), (), (), Groth16<E>, IMTObjStore<F, INT_TREE_DEPTH>>(
            &mut rng,
            some_pred, // Specifically, this statement here (see some_pred above)
            &pki,
            (
                store
                    .obj_bul
                    .get_path_of(&u.commit::<Poseidon<2>>()) // private membership data (for
                    // the user)
                    .unwrap(),
                store.obj_bul.get_root(), // public membership data (the sig pubkey)
            ),
            false,
            (),
            (),
        )
        .unwrap();

    println!(
        "\t (time) Generated proof in + statement: {:?}",
        start.elapsed().unwrap()
    );
    println!("[USER] Proof generated! \n\n");

    println!("[SERVER] Verifying proof... ");
    let start = SystemTime::now();

    let mut pub_inputs = vec![];
    pub_inputs.extend::<Vec<F>>(().to_field_elements().unwrap()); // pub args
    pub_inputs.extend::<Vec<F>>(store.obj_bul.get_root().to_field_elements().unwrap()); // pub membership data (if not constant)
    println!("public_inputs is {:?}", pub_inputs);
    // The public membership data in this case is constant, so we don't need to pass it in as an
    // argument
    let out = Groth16::<E>::verify(&vki, &pub_inputs, &proof);

    println!("\t (time) Verified proof: {:?}", start.elapsed().unwrap());
    println!("[SERVER] Verified proof Output: {:?} \n\n", out);

    assert!(out.is_ok());

    println!("[USER] Interacting (proving)...");
    let start = SystemTime::now();
    // Update the user in accordance with the first interaction
    println!("before user commit: {:?}", u.commit::<Poseidon<2>>());
    let exec_method = u
        .exec_method_create_cb::<Poseidon<2>, (), (), (), (), F, FpVar<F>, Cr, Groth16<E>, IMTObjStore<F, INT_TREE_DEPTH>, 1>(
            &mut rng,
            interaction.clone(), // see interaction
            [FakeSigPubkey::pk()],
            Time::from(0),
            &store.obj_bul,
            false,
            &pk,
            (),
            (),
        )
        .unwrap();

    /*
     let exec_method_const = u
         .constraint_exec_method_create_cb::<Poseidon<2>, (), (), (), (), F, FpVar<F>, Cr, IMTObjStore<F, INT_TREE_DEPTH>, 1>(
             &mut rng,
             interaction.clone(), // see interaction
             [FakeSigPubkey::pk()],
             Time::from(0),
             &store.obj_bul,
             false,
             (),
             (),
         );

    println!("exec_method_const is_satisfied: {:?}", exec_method_const.unwrap().is_satisfied());

        */
    /*
      let exec_method_circ = u
         .circuit_exec_method_create_cb::<Poseidon<2>, (), (), (), (), F, FpVar<F>, Cr, IMTObjStore<F, INT_TREE_DEPTH>, 1>(
             &mut rng,
             interaction.clone(), // see interaction
             [FakeSigPubkey::pk()],
             Time::from(0),
             &store.obj_bul,
             false,
             (),
             (),
         )
         .unwrap();
      let new_cs = ConstraintSystem::<F>::new_ref();
      exec_method_circ.clone().generate_constraints(new_cs.clone()).unwrap();
      new_cs.is_satisfied().unwrap();

    */

    println!(
        "\t (time) Interaction (proving) time: {:?}",
        start.elapsed().unwrap()
    );
    println!("[USER] Executed interaction! New user: {:o} \n\n", u);

    println!("[BULLETIN / SERVER] Verifying and storing...");
    let start = SystemTime::now();

    let mut old_root = store.obj_bul.get_root();
    println!("root: {:?}", old_root);
    let out = <IMTObjStore<F, INT_TREE_DEPTH> as UserBul<F, TestData>>::verify_interact_and_append::<
        (),
        Groth16<E>,
        1,
    >(
        &mut store.obj_bul,
        exec_method.new_object.clone(),
        exec_method.old_nullifier.clone(),
        (),
        exec_method.cb_com_list.clone(),
        exec_method.proof.clone(),
        Some(old_root),
        &vk,
    );
    println!("---out: {:?}", out);

    println!("---leaves are {:?}", store.obj_bul.tree.leaves);

    let s1 = start.elapsed().unwrap();
    // Server checks proof on interaction with the verification key, approves it, and stores the new object into the store

    let start = SystemTime::now();

    let root = store.obj_bul.get_root();
    println!("root: {:?}", root);
    let res = store
         .approve_interaction_and_store::<TestData, Groth16<E>, (), IMTObjStore<F, INT_TREE_DEPTH>, Poseidon<2>, 1>(
             exec_method,          // output of interaction
             FakeSigPrivkey::sk(), // for authenticity: verify rerandomization of key produces
             // proper tickets (here it doesn't matter)
             (),
             &store.obj_bul.clone(),
             cb_methods.clone(),
             Time::from(0),
             old_root,
             false,
             &vk,
             332, // interaction number
         );
    store
        .obj_bul
        .tree
        .merkle_tree
        .checkpoint(store.obj_bul.tree.merkle_tree.checkpoint_count());
    println!("res: {:?}", res);

    println!("\t (time) Verify + append: {:?}", s1);
    println!(
        "\t (time) Verify + store interaction: {:?}",
        start.elapsed().unwrap()
    );
    println!(
        "[BULLETIN] Checked proof and stored user... Output: {:?}",
        out
    );
    println!(
        "[SERVER] Checking proof and storing interaction... Output: {:?} \n\n",
        res
    );

    // User now updates its object again, again in accordance with the first interaction (each of
    // these two interactions have added callbacks to the user)
    //

    println!("[USER] Interacting (proving)...");
    let start = SystemTime::now();
    let exec_method2 = u
              .exec_method_create_cb::<Poseidon<2>, (), (), (), (), F, FpVar<F>, Cr, Groth16<E>, IMTObjStore<F, INT_TREE_DEPTH>, 1>(
                  &mut rng,
                  interaction.clone(),
                  [FakeSigPubkey::pk()],
                  Time::from(0),
                  &store.obj_bul,
                  false,
                  &pk,
                  (),
                  (),
              )
              .unwrap();

    /*
    println!("leaves are {:?}", store.obj_bul.tree.leaves);
    println!("user commit is {:?}", u.commit::<Poseidon<2>>());
    println!(
        "path are {:?}",
        store.obj_bul.get_path_of(&u.commit::<Poseidon<2>>())
    );
    let exec_method_const = u
        .constraint_exec_method_create_cb::<Poseidon<2>, (), (), (), (), F, FpVar<F>, Cr, IMTObjStore<F, INT_TREE_DEPTH>, 1>(
            &mut rng,
            interaction.clone(), // see interaction
            [FakeSigPubkey::pk()],
            Time::from(0),
            &store.obj_bul,
            false,
            (),
            (),
        );

    println!(
        "exec_method_const is_satisfied: {:?}",
        exec_method_const.unwrap().is_satisfied()
    );

     */
    println!(
        "\t (time) Interaction (proving) time: {:?}",
        start.elapsed().unwrap()
    );

    println!("[USER] Executed interaction! New user: {:o} \n\n", u);

    println!("[BULLETIN / SERVER] Verifying and storing...");
    let start = SystemTime::now();

    let out = <IMTObjStore<F, INT_TREE_DEPTH> as UserBul<F, TestData>>::verify_interact_and_append::<
        (),
        Groth16<E>,
        1,
    >(
        &mut store.obj_bul,
        exec_method2.new_object.clone(),
        exec_method2.old_nullifier.clone(),
        (),
        exec_method2.cb_com_list.clone(),
        exec_method2.proof.clone(),
        Some(root),
        &vk,
    );
    println!("---out: {:?}", out);

    let s1 = start.elapsed().unwrap();
    let start = SystemTime::now();

    // The server approves the interaction and stores it again
    let res = store
           .approve_interaction_and_store::<TestData, Groth16<E>, (), IMTObjStore<F, INT_TREE_DEPTH>, Poseidon<2>, 1>(
               exec_method2,
               FakeSigPrivkey::sk(),
               (),
               &store.obj_bul.clone(),
               cb_methods.clone(),
               Time::from(0),
               root,
               false,
               &vk,
               389,
           );
    store
        .obj_bul
        .tree
        .merkle_tree
        .checkpoint(store.obj_bul.tree.merkle_tree.checkpoint_count());
    println!("---res: {:?}", res);

    println!("\t (time) Verify + append: {:?}", s1);
    println!(
        "\t (time) Verify + store interaction: {:?}",
        start.elapsed().unwrap()
    );
    println!(
        "[BULLETIN] Checking proof and storing new user... Output: {:?}",
        out
    );
    println!(
        "[SERVER] Checking proof and storing interaction... Output: {:?} \n\n",
        res
    );

    let called = store
        .call(
            store.get_ticket_ind(0, 0).0,
            F::from(35),
            FakeSigPrivkey::sk(),
        )
        .unwrap();
    <MTCallbackStore<F, INT_TREE_DEPTH, F> as CallbackBul<F, F, Cr>>::verify_call_and_append(
        &mut store.callback_bul,
        called.0,
        called.1,
        called.2,
        Time::from(0),
    )
    .unwrap();
    println!("called: {:?}", store.callback_bul.memb_tree.leaves);
    println!("nmem: {:?}", store.callback_bul.nmemb_tree.leaves);
    store.callback_bul.memb_tree.merkle_tree.checkpoint(0);
    //store.callback_bul.update_epoch(&mut rng);

    println!("[USER] Scanning a ticket... ");
    // Setup a scan for a single callback (the first one in the list)

    let start = SystemTime::now();

    old_root = store.obj_bul.get_root();
    /*
    let scan_one_const = u.constraint_scan_callbacks::<Poseidon<2>, F, FpVar<F>, Cr, MTCallbackStore<F, INT_TREE_DEPTH, F>, IMTObjStore<F, INT_TREE_DEPTH>, NUMSCANS>
    (&mut rng,
     &store.obj_bul,
     false,
     &store.callback_bul,
     (false, false),
     F::zero(),
     cb_methods.clone(),
    )
        .unwrap();
    println!("scan_one_const: {:?}", scan_one_const.1.is_satisfied());

     */

    let (ps, scan_one) = u.scan_callbacks::<Poseidon<2>, F, FpVar<F>, Cr, MTCallbackStore<F, INT_TREE_DEPTH, F>, Groth16<E>, IMTObjStore<F, INT_TREE_DEPTH>, NUMSCANS>
           (&mut rng,
               &store.obj_bul,
               false,
               &pks,
               &store.callback_bul,
               (false, false),
               F::zero(),
               cb_methods.clone(),
           )
           .unwrap();
    store
        .obj_bul
        .tree
        .merkle_tree
        .checkpoint(store.obj_bul.tree.merkle_tree.checkpoint_count());
    println!(
        "\t (time) Scanning (interaction proving) time: {:?}",
        start.elapsed().unwrap()
    );

    println!("[USER] Scanned single ticket... {:o} \n\n", u);

    println!("[BULLETIN / SERVER] Verifying and storing scan...");
    let start = SystemTime::now();

    old_root = store.obj_bul.get_root();
    let out = <IMTObjStore<F, INT_TREE_DEPTH> as UserBul<F, TestData>>::verify_interact_and_append::<
        PubScan,
        Groth16<E>,
        0,
    >(
        &mut store.obj_bul,
        scan_one.new_object.clone(),
        scan_one.old_nullifier.clone(),
        ps.clone(),
        scan_one.cb_com_list.clone(),
        scan_one.proof.clone(),
        Some(old_root),
        &vks,
    );
    println!("Out: {:?}", out);
    /*
       let s1 = start.elapsed().unwrap();

       let start = SystemTime::now();

       let res = store
           .approve_interaction_and_store::<TestData, Groth16<E>, PubScan, GRSchnorrObjStore, Poseidon<2>, 0>(
               scan_one,
               FakeSigPrivkey::sk(),
               ps.clone(),
               &store.obj_bul.clone(),
               cb_methods.clone(),
               store.callback_bul.get_epoch(),
               store.obj_bul.get_pubkey(),
               true,
               &vks,
               442,
           );

       println!("\t (time) Verify + append: {:?}", s1);
       println!(
           "\t (time) Verify + store scan: {:?}",
           start.elapsed().unwrap()
       );

       println!(
           "[BULLETIN] Checking proof and storing new user... Output: {:?}",
           out
       );
       println!(
           "[SERVER] Checking proof for first scan... Output: {:?} \n\n",
           res
       );

       println!("[SERVER] Calling *the second callback*... ");

       let called = store
           .call(
               store.get_ticket_ind(1, 0).0,
               F::from(41),
               FakeSigPrivkey::sk(),
           )
           .unwrap();
       <GRSchnorrCallbackStore<F> as CallbackBul<F, F, Cr>>::verify_call_and_append(
           &mut store.callback_bul,
           called.0,
           called.1,
           called.2,
           Time::from(0),
       )
       .unwrap();
       store.callback_bul.update_epoch(&mut rng);

       println!("[SERVER] Called!... \n\n");

       println!("[USER] Scanning the second ticket... ");

       // Setup a scan for the second callback

       let start = SystemTime::now();

       let (ps, scan_second) = u
           .scan_callbacks::<Poseidon<2>, F, FpVar<F>, Cr, GRSchnorrCallbackStore<F>, Groth16<E>, GRSchnorrObjStore, NUMSCANS>(
               &mut rng,
               &store.obj_bul,
               true,
               &pks,
               &store.callback_bul,
               (true, true),
               store.callback_bul.get_epoch(),
               cb_methods.clone(),
           )
           .unwrap();

       println!("\t (time) Scanning time: {:?}", start.elapsed().unwrap());
       println!("[USER] Scanning the second ticket... {:o} \n\n", u);

       println!("[BULLETIN / SERVER] Verifying and storing scan...");
       let start = SystemTime::now();

       let out = <GRSchnorrObjStore as UserBul<F, TestData>>::verify_interact_and_append::<
           PubScan,
           Groth16<E>,
           0,
       >(
           &mut store.obj_bul,
           scan_second.new_object.clone(),
           scan_second.old_nullifier.clone(),
           ps.clone(),
           scan_second.cb_com_list.clone(),
           scan_second.proof.clone(),
           None,
           &vks,
       );
       let s1 = start.elapsed().unwrap();

       let start = SystemTime::now();

       let res = store
           .approve_interaction_and_store::<TestData, Groth16<E>, PubScan, GRSchnorrObjStore, Poseidon<2>, 0>(
               scan_second,
               FakeSigPrivkey::sk(),
               ps.clone(),
               &store.obj_bul.clone(),
               cb_methods.clone(),
               store.callback_bul.get_epoch(),
               store.obj_bul.get_pubkey(),
               true,
               &vks,
               441,
           );

       println!("\t (time) Verify + append: {:?}", s1);
       println!(
           "\t (time) Verify + store scan: {:?}",
           start.elapsed().unwrap()
       );
       println!(
           "[BULLETIN] Checking proof and storing new user... Output: {:?}",
           out
       );
       println!(
           "[SERVER] Checking proof for second scan... Output: {:?} \n\n",
           res
       );

       println!("{:?}", u);

    */
}
