(* A very cute demo of smart constructors for pure λ-calculus (some sort of
   HOAS to intrinsically scoped De-Bruijn transform) by Conor McBride.

   Ported to Coq from Conor's original Agda version by Lapinot.
*)

Set Implicit Arguments.
From Equations Require Import Equations.

Inductive nat : Type :=
| ze : nat
| su : nat -> nat .

Equations add : nat -> nat -> nat :=
  add ze     m := m ;
  add (su n) m := su (add n m) .
Infix "+" := (add).

Inductive Fin : nat -> Type :=
| Fze {n} : Fin (su n)
| Fsu {n} : Fin n -> Fin (su n)
.

Equations Femb (n : nat) : Fin (su n) :=
  Femb ze     := Fze ;
  Femb (su n) := Fsu (Femb n) .
Coercion Femb : nat >-> Fin .

Equations Flift {n} : Fin n -> Fin (su n) :=
  Flift Fze     := Fze ;
  Flift (Fsu n) := Fsu (Flift n) .
Coercion Flift : Fin >-> Fin .

Inductive Tm (n : nat) : Type :=
| V : Fin n -> Tm n
| A : Tm n -> Tm n -> Tm n
| L : Tm (su n) -> Tm n
.
Infix "$" := (A) (at level 42).

Equations var (m : nat) {n : nat} : Fin (m + su n) :=
  @var ze     n := n ;
  @var (su m) n := var m .

Definition lam {m : nat} (f : (forall n, Tm (m + su n)) -> Tm (su m)) : Tm m :=
  L (f (fun n => V (var m))) .
Arguments lam {_} & _ .
Notation "'λ' x ⋅ U" := (lam (fun arg => let x := arg _ in U)) (at level 43).

Definition test : Tm ze := λ f⋅ λ x⋅ f $ (f $ x) .
Compute test.
(* = L (L (V (Fsu Fze) $ (V (Fsu Fze) $ V Fze))) *)
