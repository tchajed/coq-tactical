Require Import Tactical.SimplMatch.

Module SimplMatchTests.

  (** test simpl_match failure when match does not go away *)
  Theorem fails_if_match_not_removed :
    forall (vd m: nat -> option nat) a,
      vd a = m a ->
      vd a = match (m a) with
             | Some v => Some v
             | None => None
             end.
  Proof.
    intros.
    (simpl_match; fail "should not work here")
    || idtac.
    rewrite H.
    destruct (m a); auto.
  Qed.

  Theorem removes_match :
    forall (vd m: nat -> option nat) a v v',
      vd a = Some v ->
      m a = Some v' ->
      vd a = match (m a) with
             | Some _ => Some v
             | None => None
             end.
  Proof.
    intros.
    simpl_match; now auto.
  Qed.

  (** hypothesis replacement should remove the match or fail *)
  Theorem fails_on_hyp_if_match_not_removed :
    forall (vd m: nat -> option nat) a,
      vd a = m a ->
      m a = match (m a) with
            | Some v => Some v
            | None => None
            end ->
      True.
  Proof.
    intros.
    (simpl_match; fail "should not work here")
    || idtac.
    trivial.
  Qed.

End SimplMatchTests.

Module DestructMatchesTests.

  Theorem removes_absurdities :
    forall b1 b2,
      b1 = b2 ->
      match b1 with
      | true => match b2 with
               | true => True
               | false => False
               end
      | false => match b2 with
                | true => False
                | false => True
                end
      end.
  Proof.
    intros.
    destruct_all_matches.
  Qed.

  Theorem destructs_innermost_match :
    forall b1 b2,
      match (match b2 with
             | true => b1
             | false => false
             end) with
      | true => b1 = true
      | false => b1 = false \/ b2 = false
      end.
  Proof.
    intros.
    destruct_goal_matches.
  Qed.

End DestructMatchesTests.
