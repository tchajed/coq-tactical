(** ** Other proof automation helpers *)

(** substitute variables that are let bindings (these can be created with [set
(x:=value)] and appear in the context as [v := def]) *)
Ltac subst_var :=
  repeat match goal with
  | [ v := _ |- _ ] => subst v
  end.

Create HintDb false.

Ltac solve_false :=
  solve [ exfalso; eauto with false ].

Ltac rename_by_type type name :=
  match goal with | x : type |- _ => rename x into name end.

Ltac is_one_goal := let n := numgoals in guard n = 1.

Ltac add_hypothesis pf :=
  let P := type of pf in
  lazymatch goal with
  | [ H: P |- _ ] => fail "already known"
  | _ => pose proof pf
  end.

(* borrowed from Software Foundations' LibTactics
https://softwarefoundations.cis.upenn.edu/plf-current/LibTactics.html *)
Tactic Notation "gen" constr(X1) :=
  generalize dependent X1.
Tactic Notation "gen" constr(X1) constr(X2) :=
  gen X2; gen X1.
Tactic Notation "gen" constr(X1) constr(X2) constr(X3) :=
  gen X3; gen X2; gen X1.
Tactic Notation "gen" constr(X1) constr(X2) constr(X3) constr(X4) :=
  gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" constr(X1) constr(X2) constr(X3) constr(X4) constr(X5) :=
  gen X5; gen X4; gen X3; gen X2; gen X1.
