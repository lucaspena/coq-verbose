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

Inductive and' (A B : Prop) : Prop :=
    conj' : forall (_ : A) (_ : B), and' A B .
Print and'_ind.
Inductive ex1 (A : Type) (P : forall _ : A, Prop) : Prop :=
    ex_intro1 : forall (x : A) (_ : P x), ex1 A P .

Set Implicit Arguments.

Inductive ex2 (A : Type) (P : forall _ : A, Prop) : Prop :=
    ex_intro2 : forall (x : A) (_ : P x), @ex2 A P .

Inductive ex3 (A : Type) (P : forall _ : A, Prop) : Prop :=
    ex_intro3 : forall (x : A) (_ : P x), @ex3 A P .

Inductive ex4 (A : Type) (P : forall _ : A, Prop) : Prop :=
    ex_intro4 : forall (x : A) (_ : P x), @ex4 A P .

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

Definition False_ind : forall (P : Prop) (_ : False), P := 
fun (P : Prop) (f : False) => match f return P with
                              end .

Definition add_ind' : forall (_ : nat) (_ : nat), nat := 
fix add (n m : nat) {struct n} : nat :=
  match n return nat with
  | O => m
  | S p => S (add p m)
  end .

Print nat.
Definition nat_ind' : forall (P : forall _ : nat, Prop) (_ : P O)(_ : forall (n : nat) (_ : P n), P (S n))(n : nat), P n := 
fun (P : forall _ : nat, Prop) (f : P O)
  (f0 : forall (n : nat) (_ : P n), P (S n)) =>
fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
  | O => f
  | S n0 => f0 n0 (F n0)
  end .


Print eq.
Print eq_ind.

Definition AddZero : forall n : nat, @eq nat (Nat.add n O) n := 
fun n : nat =>
nat_ind (fun n0 : nat => @eq nat (Nat.add n0 O) n0)
  (@eq_refl nat O : @eq nat (Nat.add O O) O)
  (fun (n0 : nat) (IHn : @eq nat (Nat.add n0 O) n0) =>
   @eq_ind_r nat n0 (fun n1 : nat => @eq nat (S n1) (S n0))
     (@eq_refl nat (S n0)) (Nat.add n0 O) IHn
   :
   @eq nat (Nat.add (S n0) O) (S n0)) n .

Set Printing All.
Print AddZero.
Check AddZero.

Print eq_refl.
Print eq_ind.

Definition AndComm : forall (A B : Prop) (_ : and A B), and B A := 
fun (A B : Prop) (H : and A B) =>
match H return (and B A) with
| conj H0 H1 => @conj B A H1 H0
end .

Set Printing All. 
Print AndComm.
Print not.

Definition AndComm' : forall (A B : Prop) (_ : and A B), and B A := 
fun (A B : Prop) (H : and A B) =>
match H return (and B A) with
| conj H0 H1 => @conj B A H1 H0
end .

(* ask brandon if way to get term out of proof *)

Definition AndComm'' : forall (A B : Prop) (_ : and A B), and B A := 
AndComm' .
  
Print AndComm'.

Print nat_ind.
Print or.

Definition test : forall _ : Prop, Prop := fun _ : Prop => True .

Print test.



Definition and_rect' : Type := 
forall (A B : Prop) (P : Type) (_ : forall (_ : A) (_ : B), P) (_ : and A B),
P .
Definition and_ind : Prop := 
forall (A B P : Prop) (_ : forall (_ : A) (_ : B), P) (_ : and A B), P .
Definition and_rec : Type := 
forall (A B : Prop) (P : Set) (_ : forall (_ : A) (_ : B), P) (_ : and A B),
P .

Definition AndCom : forall (A B : Prop) (_ : and A B), and B A := 
fun (A B : Prop) (H : and A B) =>
match H return (and B A) with
| conj H0 H1 => @conj B A H1 H0
end .

Print AndCom.

Definition AndCom' : forall (A B : Prop) (_ : and A B), and B A := 
fun (A B : Prop) (H : and A B) =>
match H return (and B A) with
| conj H0 H1 => @conj B A H1 H0
end .


Print All.

End MLCoq.

(* Require Import dpdgraph.dpdgraph. *)
(* Print FileDependGraph MLCoq. *)

(* Print MLCoq.AndCom'. *)