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
