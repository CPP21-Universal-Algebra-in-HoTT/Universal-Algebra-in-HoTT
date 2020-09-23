(** This file defines [Algebra]. *)

Require Export
  Coq.Unicode.Utf8
  HoTT.Basics.

Require Import
  HoTT.Types
  HoTT.Spaces.Finite
  HoTT.HProp
  HoTT.HSet
  HoTT.Classes.implementations.list
  HoTT.Classes.implementations.ne_list.

Declare Scope Algebra_scope.

Delimit Scope Algebra_scope with Algebra.

Open Scope Algebra_scope.

Record SymbolTypeOf {Sort : Type} := Build_SymbolTypeTo
  { Arity : Type
  ; sorts_dom : Arity -> Sort
  ; sort_cod : Sort }.

Arguments SymbolTypeOf : clear implicits.
Arguments Build_SymbolTypeTo {Sort}.

(** A [Signature] is used to characterise [Algebra]s. In particular
    a signature specifies which operations (functions) an algebra for
    the signature is expected to provide. A signature consists of
    - A type of [Sort]s. An algebra for the signature must provide
      a type for each [s : Sort].
    - A type of function symbols [Symbol]. For each function symbol
      [u : Symbol], an algebra for the signature must provide a
      corresponding operation.
    - The field [symbol_types σ u] indicates which type the operation
      corresponding to [u] should have. *)

Record Signature := Build_Signature
  { Sort : Type
  ; Symbol : Type
  ; symbol_types : Symbol -> SymbolTypeOf Sort
  ; hset_sort : IsHSet Sort
  ; hset_symbol : IsHSet Symbol }.

Notation SymbolType σ := (SymbolTypeOf (Sort σ)).

Global Existing Instance hset_sort.

Global Existing Instance hset_symbol.

Global Coercion symbol_types : Signature >-> Funclass.

(** An [Algebra] must provide a family of [Carriers σ] indexed by
    [Sort σ]. These carriers are the "objects" (types) of the algebra. *)

(* [Carriers] is a notation because it will be used for an implicit
   coercion [Algebra >-> Funclass] below. *)

Notation Carriers σ := (Sort σ → Type).

Notation DomOperation A w
  := (∀ X : Arity w, A (sorts_dom w X)) (only parsing).

Notation CodOperation A w := (A (sort_cod w)) (only parsing).

Definition Operation {σ} (A : Carriers σ) (w : SymbolType σ) : Type
  := DomOperation A w -> CodOperation A w.

Global Instance trunc_operation `{Funext} {σ : Signature}
  (A : Carriers σ) {n} `{!∀ s, IsTrunc n (A s)} (u : SymbolType σ)
  : IsTrunc n (Operation A u).
Proof.
  apply trunc_forall.
Defined.

Fixpoint CurriedOperation {σ} (A : Carriers σ) (n : nat)
  : (Fin n.+1 → Sort σ) → Type :=
  match n with
  | O => fun sorts => A (sorts (inr tt))
  | S n' => fun sorts =>
      A (sorts (inr tt)) → CurriedOperation A n' (sorts o inl)
  end.

Fixpoint OperationUncurry {σ} (A : Carriers σ) (n : nat)
  : ∀ (sorts : Fin n.+1 → Sort σ),
    CurriedOperation A n sorts →
    Operation A
      {| Arity := Fin n
       ; sorts_dom := sorts o fin_finS_inject n
       ; sort_cod := sorts (fin_max n) |}
  := match n with
     | O => fun _ op _ => op
     | S n' =>
        fun sorts op a =>
          OperationUncurry A n' (sorts o inl) (op (a (inr tt))) (a o inl)
     end.

(** An [Algebra σ] for a signature [σ] consists of a family [carriers :
    Carriers σ] indexed by the sorts [s : Sort σ], and for each symbol
    [u : Symbol σ], an operation of type [Operation carriers (σ u)],
    where [σ u : SymbolType σ] is the symbol type of [u]. *)

Record Algebra {σ : Signature} : Type := Build_Algebra
  { carriers : Carriers σ
  ; operations : ∀ (u : Symbol σ), Operation carriers (σ u)
  ; hset_algebra : ∀ (s : Sort σ), IsHSet (carriers s) }.

Arguments Algebra : clear implicits.

Arguments Build_Algebra {σ} carriers operations {hset_algebra}.

Global Existing Instance hset_algebra.

(** We have a convenient implicit coercion from an algebra to the
    family of carriers. *)
Global Coercion carriers : Algebra >-> Funclass.

Definition SigAlgebra (σ : Signature) : Type
  := {c : Carriers σ
        | { _ : ∀ (u : Symbol σ), Operation c (σ u)
              | ∀ (s : Sort σ), IsHSet (c s) } }.

Lemma issig_algebra (σ : Signature) : SigAlgebra σ <~> Algebra σ.
Proof.
  issig.
Defined.

(** To find a path between two algebras [A B : Algebra σ] it suffices
    to find paths between the carriers and the operations. *)

Lemma path_algebra `{Funext} {σ : Signature} (A B : Algebra σ)
  (p : carriers A = carriers B)
  (q : transport (λ X, ∀ u, Operation X (σ u)) p (operations A)
       = operations B)
  : A = B.
Proof.
  apply (ap (issig_algebra σ)^-1)^-1; cbn.
  apply (path_sigma' _ p).
  refine (transport_sigma p _ @ _).
  apply path_sigma_hprop.
  exact q.
Defined.

Arguments path_algebra {_} {_} (A B)%Algebra_scope (p q)%path_scope.

Lemma path_ap_carriers_path_algebra `{Funext} {σ} (A B : Algebra σ)
  (p : carriers A = carriers B)
  (q : transport (λ X, ∀ u, Operation X (σ u)) p (operations A)
       = operations B)
  : ap carriers (path_algebra A B p q) = p.
Proof.
  unfold path_algebra, path_sigma_hprop, path_sigma_uncurried.
  destruct A as [A a ha], B as [B b hb]; cbn in *.
  destruct p, q; cbn.
  now destruct (center (ha = hb)).
Defined.

Arguments path_ap_carriers_path_algebra {_} {_} (A B)%Algebra_scope (p q)%path_scope.

(** Suppose [p],[q] are paths in [Algebra σ]. To show that [p = q] it
    suffices to find a path [r] between the paths corresponding to
    [p] and [q] in [SigAlgebra σ]. *)

Lemma path_path_algebra_issig {σ : Signature} {A B : Algebra σ} (p q : A = B)
  (r : ap (issig_algebra σ)^-1 p = ap (issig_algebra σ)^-1 q)
  : p = q.
Proof.
  set (e := (equiv_ap (issig_algebra σ)^-1 A B)).
  by apply (@equiv_inv _ _ (ap e) (Equivalences.isequiv_ap _ _)).
Defined.

Arguments path_path_algebra_issig {_} {A B}%Algebra_scope (p q r)%path_scope.

(** If [p q : A = B], then [ap carriers p = ap carriers q] implies [p = q]. *)

Lemma path_path_algebra `{Funext} {σ} {A B : Algebra σ}
  (p q : A = B) (r : ap carriers p = ap carriers q)
  : p = q.
Proof.
  apply path_path_algebra_issig.
  unshelve eapply path_path_sigma.
  - transitivity (ap carriers p); [by destruct p |].
    transitivity (ap carriers q); [exact r | by destruct q].
  - apply hprop_allpath. apply hset_path2.
Defined.

Arguments path_path_algebra {_} {σ} {A B}%Algebra_scope (p q r)%path_scope.

Module algebra_notations.

(** Given [A : Algebra σ] and function symbol [u : Symbol σ], we use
    the notation [u ^^ A] to refer to the corresponding algebra
    operation of type [Operation A (σ u)]. *)

  Global Notation "u ^^ A" := (operations A u)
                              (at level 60, no associativity)
                              : Algebra_scope.

End algebra_notations.
