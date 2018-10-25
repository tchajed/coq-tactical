Require Import Tactical.Propositional.

Module DeexTests.

  Theorem chooses_name :
    (exists (foo:unit), foo=foo) ->
    True.
  Proof.
    intros.
    deex.
    destruct foo.
    trivial.
  Qed.

  Theorem chooses_fresh_name :
    forall (foo:bool),
      (exists (foo:unit), foo=foo) -> True.
  Proof.
    intros.
    deex.
    (* fresh name for exists witness *)
    destruct foo0.
    trivial.
  Qed.

End DeexTests.
