module Part5.Meta

// let pow2_bound_19 (x:nat{x <= 19}) : Lemma (pow2 x < 1000000) =
//   assert (forall (x y : nat). x <= y ==> pow2 x <= pow2 y);
//   assert (pow2 19 == 524288);
//   assert (pow2 x < 1000000);
//   ()

open FStar.Math
open FStar.Tactics

// let pow2_bound_19' (x:nat{x <= 19}) : Lemma (pow2 x < 1000000) =
//   FStar.Math.Lemmas.pow2_le_compat 19 x;
//   assert (pow2 19 == 524288);
//   assert (pow2 x < 1000000);
//   ()

let pow2_bound_19'' (x:nat{x <= 19}) : Lemma (pow2 x < 1000000) =
  FStar.Math.Lemmas.pow2_le_compat 19 x;
  assert (pow2 19 == 524288) by compute ();
  assert (pow2 x < 1000000);
  ()

let pow2_bound_19''' (x:nat{x <= 19}) : Lemma (pow2 x < 1000000) =
  FStar.Math.Lemmas.pow2_le_compat 19 x;
  assert (pow2 19 == 524288) by (compute (); dump "after compute");
  assert (pow2 x < 1000000);
  ()

let pow2_bound_19'''' (x:nat{x <= 19}) : Lemma (pow2 x < 1000000) =
  FStar.Math.Lemmas.pow2_le_compat 19 x;
  assert (pow2 19 == 524288) by (
    compute (); 
    trivial();
    qed();
    dump "after trivial"
  );
  assert (pow2 x < 1000000);
  ()

// # The Tac effect

// # Goals

assume val p : prop
assume val q : prop
assume val r : prop
assume val s : prop

assume val p_q : unit -> Lemma (requires p) (ensures q)
assume val p_r : squash p -> Lemma r
assume val qr_s : unit -> Lemma (q ==> r ==> s)

let test () : Lemma (requires p) (ensures s) =
  assert s by (
    mapply (`qr_s);
    focus (fun () ->
      mapply (`p_q);
      smt());
    focus (fun () ->
      mapply (`p_r);
      smt());
    ()
  )


