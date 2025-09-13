(* code from Thomas Lamiaux *)
Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).

Arguments vnil {_}.
Arguments vcons {_} _ _ _.

(* Two β-ι cuts !
1. => not forget n = m
2. => not forget n = m
*)


(* Fails without Equations *)
Fail Fixpoint map2vec {A B C : Set} (f : A -> B -> C) n (vA : vec A n) (vB : vec B n) : vec C n :=
  match vA, vB with
  | vnil, vnil => vnil
  | vcons a _ tA, vcons b _ tB => vcons (f a b) _ (map2vec f _ tA tB)
  end.

(* opti in the elaboration *)
Definition tail {A} n (v : vec A (S n)) : vec A n :=
  match v as v' in vec _ n' return 
    match n' return Type 
    with 
    | 0 =>  IDProp 
    | S n'' => vec A n''
    end  
  with
  | vcons _ _ v => v
  end.
Print tail.

Print tail.
Print IDProp.


(* work thanks to beta-iota for vB *)
Definition map2vec1 {A B C : Set} (f : A -> B -> C) : forall n, vec A n -> vec B n -> vec C n :=
  fix fn (n : nat) (vA : vec A n) (vB : vec B n) {struct vB} : vec C n :=
  match vA in vec _ k return vec B k -> vec C k with
    | vnil => fun (_ : vec B 0) => vnil
    | vcons a k tA => 
      (* tA : vec A k *)
      fun vB : vec B (S k) =>
      match vB in vec _ p return 
        (match p return Type 
        with 
        | 0 => True 
        | S p => vec A p -> vec C (S p) 
        end) 
      with
      | vnil => I
      | vcons b p tB => fun tA => vcons (f a b) p (fn p tA tB)
      end tA
  end vB.

(* no beta-iota for tA => obfuscated by the match *)
Fail Definition map2vec2 {A B C : Set} (f : A -> B -> C) : forall n, vec A n -> vec B n ->vec C n :=
  fix rec (n : nat) (vA : vec A n) {struct vA} : vec B n -> vec C n :=
  match vA in vec _ k return vec B k -> vec C k with
    | vnil => fun (_ : vec B 0) => vnil
    | vcons a k tA => (
      fun vB : vec B (S k) =>
      match vB in vec _ p return (match p with 0 => True | S p => vec A p -> vec C (S p) end) with
      | vnil => I
      | vcons b p tB => fun ta => vcons (f a b) p (rec p tA tB)
      end tA
    )
  end.

Definition map2vec3 {A B C : Set} (f : A -> B -> C) : forall n, vec A n -> vec B n ->vec C n :=
  fix rec (n : nat) (vA : vec A n) {struct vA} : vec B n -> vec C n :=
  match vA in vec _ k return vec B k -> vec C k with
    | vnil => fun (_ : vec B 0) => vnil
    | vcons a k tA => (
      fun vB : vec B (S k) =>
      match vB in vec _ p return 
        (vec A 
          (match p with 
          | 0 => 0 
          | S p' => p' 
          end) -> vec C p) 
      with
      | vnil => fun _ => vnil
      | vcons b p tB => fun tA => vcons (f a b) p (rec p tA tB)
      end tA
    )
  end.

(* works as rec is *)
Definition map2vec4 {A B C : Set} (f : A -> B -> C) : forall n, vec A n -> vec B n -> vec C n :=
  fix rec (n : nat) (vA : vec A n) {struct vA} : vec B n -> vec C n :=
  match vA in vec _ k return vec B k -> vec C k with
    | vnil => fun (_ : vec B 0) => vnil
    | vcons a k tA => (fun vB : vec B (S k) =>
      match vB in vec _ p return (match p with 0 => True | S p => (vec B p -> vec C p) -> vec C (S p) end) with
      | vnil => I
      | vcons b p tB => fun rec' => vcons (f a b) p (rec' tB)
      end (rec k tA)
    )
    end.

Definition map2vec5 {A B C : Set} (f : A -> B -> C) : forall n, vec A n -> vec B n -> vec C n :=
  vec_rect A (fun n (v : vec A n) => vec B n -> vec C n)
    (fun _ => vnil)
    (fun a k tA IHtA =>
      fun vB => (
      vec_rect B (fun n v => match n with 0 => True | S n => (vec B n -> vec C n) -> vec C (S n) end)
      I
      (fun b p tB _ => fun rec => vcons (f a b) _ (rec tB))
      (S k) vB
    ) IHtA
    ).
