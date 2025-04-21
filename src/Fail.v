Definition le_inv_ret (n m : nat) (e : le n m) : True : Prop :=
  match e
  with
  | le_n _ => I
  | le_S _ m' ha  => I
  end.

Fail Definition le_inv_ret_lifted (n m : nat) (e : le n m) : Prop : Type :=
match e return Prop
with
| le_n _ => True
| le_S _ m' ha  => False
end.

(*
  
The command has indeed failed with message:
Incorrect elimination of "e" in the inductive type
"le":
the return type has sort "Type"
while it should be SProp or Prop.
Elimination of an inductive object of sort Prop
is not allowed on a predicate in sort "Type"
because proofs can be eliminated only to build proofs.

*)
