From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.

Require Import Coq.Logic.Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma oStar_perm_choiceTT : 
  forall (T : finType) (u : {set T}) (o : T) (o2 : {o | o \in u}) (ot : o \in u),
  o = sval ((if o \in u as y return ((o \in u) = y → {o : T | o \in u})
             then [eta exist (λ o : T, o \in u) o]
             else fun=> o2)
              (erefl (o \in u))).
Proof.
  move=> T u o.
  case=> o2 p ou.
  have foo : o = sval (exist (fun o => o \in u) o ou) by [].
  rewrite [LHS]foo.
  apply/eq_sig_hprop_iff => /=; first by move=> x; apply: Classical_Prop.proof_irrelevance.
  set (fn := fun (ofn1 ofn2 : T) (ufn : {set T}) (pfa : ofn1 \in ufn) 
    (pfb : ofn2 \in ufn) (b : bool) 
    (pfc :  (ofn1 \in ufn) = b) => 
    (if b as y return ((ofn1  \in ufn) = y → {o0 : T | o0  \in ufn})
    then [eta exist (λ o0 : T, o0  \in ufn) ofn1]
    else fun=> exist (λ o0 : T, o0  \in ufn) ofn2 pfb) pfc).
  enough (forall (ofn1 ofn2 : T) (ufn : {set T}) pfa pfb b pfc,
    exist (λ o0 : T, o0  \in ufn) ofn1 pfa = 
    fn ofn1 ofn2 ufn pfa pfb b pfc) as ha.
  eapply ha.
  intros *.
  destruct b; cbn.
  f_equal.
  eapply Classical_Prop.proof_irrelevance.
  congruence.
Qed.
