(* Inductive False := . *)

Module MLCoq.

SearchAbout (_ + _).
Print bool.
Print conj.
Print and_ind.
Print nat_ind.
Print plus_n_Sm.
Print plus_Sn_m.

Set Printing All.

Print IF_then_else.

Inductive and' (A B:Prop) : Prop :=
  conj' : forall (x : A), forall (y : B), and' A B.

Print and'_ind.
Inductive ex1 (A : Type) (P : forall (x : A), Prop) : Prop :=
  ex_intro1 : forall x : A, forall (y : (P x)), ex1 A P.

Set Implicit Arguments.

Inductive ex2 (A : Type) (P : forall (x : A), Prop) : Prop :=
  ex_intro2 : forall (x : A), forall (y : (P x)), ex2 P.

Inductive ex3 (A : Type) (P : forall (x : A), Prop) : Prop :=
  ex_intro3 : forall (x : A), forall (y : (P x)), ex3 (A:=A) P.

Inductive ex4 (A : Type) (P : forall (x : A), Prop) : Prop :=
  ex_intro4 : forall (x : A), forall (y : (P x)), @ ex4 A P.

Check conj.
Check conj'.

Print conj.

Print nat.
Print nat_ind.

Print False_ind.
Print Nat.add.
Print and_ind.

Print True.
Print True_ind.

Definition False_ind := 
fun (P : Prop) (f : False) => match f return P with
                              end .

Definition add_ind' :=
  fix add (n m : nat) : nat := match n with
                                        | 0 => m
                                        | S p => S (add p m)
                                        end .

Print nat.
Definition nat_ind' := 
fun (P : nat -> Prop) (f : P 0) (f0 : forall n : nat, P n -> P (S n)) =>
fix F (n : nat) := match n with
                         | 0 => f
                         | S n0 => f0 n0 (F n0)
                         end .


Print eq.
Print eq_ind.

Lemma AddZero : forall n, n + 0 = n.
Proof.
  intros.
  induction n. simpl. apply eq_refl.
  simpl. rewrite IHn.
  apply eq_refl.
Qed.

Set Printing All.
Print AddZero.
Check AddZero.

Print eq_refl.
Print eq_ind.

Lemma AndComm : forall A B, A /\ B -> B /\ A .
Proof.
  intros.
  destruct H. split; auto.
Qed.

Set Printing All. 
Print AndComm.
Print not.

Definition AndComm' := 
fun (A B : Prop) (H : and A B) =>
match H return (and B A) with
| conj H0 H1 => @conj B A H1 H0
end  .

(* ask brandon if way to get term out of proof *)

Lemma AndComm'' : forall A B : Prop, A /\ B -> B /\ A .
Proof.
  exact AndComm'.
Qed.
  
Print AndComm'.

Print nat_ind.
Print or.

Definition test :=
  fun (A : Prop) =>
    match A with
    | False => True
    end .

Print test.



Definition and_rect' := forall (A B : Prop) (P : Type), (A -> B -> P) -> and A B -> P.
Definition and_ind := forall A B P : Prop, (A -> B -> P) -> and A B -> P .
Definition and_rec := forall (A B : Prop) (P : Set), (A -> B -> P) -> and A B -> P .

Lemma AndCom : forall A B, A /\ B -> B /\ A. 
Proof.
  intros A B H.
  destruct H.
  constructor. apply H0. apply H.
Qed.

Print AndCom.

Definition AndCom' := 
fun (A B : Prop) (H : A /\ B) => match H with
                                 | conj H0 H1 => conj H1 H0
                                 end.


Print All.

End MLCoq.

(* Require Import dpdgraph.dpdgraph. *)
(* Print FileDependGraph MLCoq. *)

(* Print MLCoq.AndCom'. *)