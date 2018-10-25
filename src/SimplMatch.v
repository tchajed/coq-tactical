(** ** Simplify matches when possible *)

Ltac simpl_match :=
  let repl_match_goal d d' :=
      replace d with d';
      lazymatch goal with
      | [ |- context[match d' with _ => _ end] ] => fail
      | _ => idtac
      end in
  let repl_match_hyp H d d' :=
      replace d with d' in H;
      lazymatch type of H with
      | context[match d' with _ => _ end] => fail
      | _ => idtac
      end in
  match goal with
  | [ Heq: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
    repl_match_goal d d'
  | [ Heq: ?d' = ?d |- context[match ?d with _ => _ end] ] =>
    repl_match_goal d d'
  | [ Heq: ?d = ?d', H: context[match ?d with _ => _ end] |- _ ] =>
    repl_match_hyp H d d'
  | [ Heq: ?d' = ?d, H: context[match ?d with _ => _ end] |- _ ] =>
    repl_match_hyp H d d'
  end.

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

(** ** Find and destruct matches *)

Ltac destruct_matches_in e :=
  lazymatch e with
  | context[match ?d with | _ => _ end] =>
    destruct_matches_in d
  | _ => destruct e eqn:?; intros
  end.

Ltac destruct_all_matches :=
  repeat (try simpl_match;
          try match goal with
              | [ |- context[match ?d with | _ => _ end] ] =>
                destruct_matches_in d
              | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                destruct_matches_in d
              end);
  subst;
  try congruence;
  auto.

Ltac destruct_nongoal_matches :=
  repeat (try simpl_match;
           try match goal with
           | [ H: context[match ?d with | _ => _ end] |- _ ] =>
             destruct_matches_in d
               end);
  subst;
  try congruence;
  auto.

Ltac destruct_goal_matches :=
  repeat (try simpl_match;
           match goal with
           | [ |- context[match ?d with | _ => _ end] ] =>
              destruct_matches_in d
           end);
  try congruence;
  auto.

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

Ltac destruct_tuple :=
  match goal with
  | [ H: context[let '(a, b) := ?p in _] |- _ ] =>
    let a := fresh a in
    let b := fresh b in
    destruct p as [a b]
  | [ |- context[let '(a, b) := ?p in _] ] =>
    let a := fresh a in
    let b := fresh b in
    destruct p as [a b]
  end.

Tactic Notation "destruct" "matches" "in" "*" := destruct_all_matches.
Tactic Notation "destruct" "matches" "in" "*|-" := destruct_nongoal_matches.
Tactic Notation "destruct" "matches" := destruct_goal_matches.
