(** This file implements [IsHomomorphism] and [IsIsomorphism].
    It developes basic algebra homomorphisms and isomorphims. The main
    theorem in this file is the [path_isomorphism] theorem, which
    states that there is a path between isomorphic algebras. *)

Require Export HoTT.Algebra.UniversalAlgebra.Infinitary.ua_algebra.

Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.Fibrations
  HoTT.HProp
  HoTT.HSet
  HoTT.Tactics
  UnivalenceImpliesFunext.

Import algebra_notations.

Section is_homomorphism.
  Context {σ} {A B : Algebra σ} (f : ∀ (s : Sort σ), A s → B s).

(** The family of functions [f] above is [OpPreserving α β] with
    respect to operations [α : A s1 → A s2 → ... → A sn → A t] and
    [β : B s1 → B s2 → ... → B sn → B t] if

    <<
      f t (α x1 x2 ... xn) = β (f s1 x1) (f s2 x2) ... (f sn xn)
    >>
*)

  Definition OpPreserving {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w) : Type
    := ∀ a : DomOperation A w,
        f (sort_cod w) (α a) = β (fun X => f (sorts_dom w X) (a X)).

  Global Instance hprop_oppreserving `{Funext} {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w)
    : IsHProp (OpPreserving α β).
  Proof.
    apply trunc_forall.
  Qed.

(** The family of functions [f : ∀ (s : Sort σ), A s → B s] above is
    a homomorphism if for each function symbol [u : Symbol σ], it is
    [OpPreserving (u^^A) (u^^B)] with respect to the algebra
    operations [u^^A] and [u^^B] corresponding to [u]. *)

  Class IsHomomorphism : Type
    := oppreserving_hom : ∀ (u : Symbol σ), OpPreserving (u^^A) (u^^B).

  Global Instance hprop_is_homomorphism `{Funext}
    : IsHProp IsHomomorphism.
  Proof.
    apply trunc_forall.
  Qed.
End is_homomorphism.

Record Homomorphism {σ} {A B : Algebra σ} : Type := Build_Homomorphism
  { def_hom : ∀ (s : Sort σ), A s → B s
  ; is_homomorphism_hom : IsHomomorphism def_hom }.

Arguments Homomorphism {σ}.

Arguments Build_Homomorphism {σ A B} def_hom {is_homomorphism_hom}.

(** We the implicit coercion from [Homomorphism A B] to the family
    of functions [∀ s, A s → B s]. *)

Global Coercion def_hom : Homomorphism >-> Funclass.

Global Existing Instance is_homomorphism_hom.

Lemma apD10_homomorphism {σ} {A B : Algebra σ} {f g : Homomorphism A B}
  : f = g → ∀ s, f s == g s.
Proof.
  intro p. by destruct p.
Defined.

Definition SigHomomorphism {σ} (A B : Algebra σ) : Type :=
  { def_hom : ∀ s, A s → B s | IsHomomorphism def_hom }.

Lemma issig_homomorphism {σ} (A B : Algebra σ)
  : SigHomomorphism A B <~> Homomorphism A B.
Proof.
  issig.
Defined.

Global Instance hset_homomorphism `{Funext} {σ} (A B : Algebra σ)
  : IsHSet (Homomorphism A B).
Proof.
  apply (trunc_equiv _ (issig_homomorphism A B)).
Qed.

(** To find a path between two homomorphisms [f g : Homomorphism A B]
    it suffices to find a path between the defining families of
    functions and the [is_homomorphism_hom] witnesses. *)

Lemma path_homomorphism `{Funext} {σ} {A B : Algebra σ}
  (f g : Homomorphism A B) (p : def_hom f = def_hom g)
  : f = g.
Proof.
  apply (ap (issig_homomorphism A B)^-1)^-1.
  unfold issig_homomorphism; cbn.
  apply path_sigma_hprop.
  exact p.
Defined.

(** A family of functions [f : ∀ s, A s → B s] is an isomorphism if it is
    a homomorphism, and for each [s : Sort σ], [f s] is an equivalence. *)

(* We make [IsHomomorphism] an argument here, rather than a field, so
   having both [f : Homomorphism A B] and [X : IsIsomorphism f] in
   context does not result in having two proofs of [IsHomomorphism f]
   in context. *)

Class IsIsomorphism {σ : Signature} {A B : Algebra σ}
  (f : ∀ s, A s → B s) `{!IsHomomorphism f}
  := isequiv_isomorphism : ∀ (s : Sort σ), IsEquiv (f s).

Global Existing Instance isequiv_isomorphism.

Definition equiv_isomorphism {σ : Signature} {A B : Algebra σ}
  (f : ∀ s, A s → B s) `{IsIsomorphism σ A B f}
  : ∀ (s : Sort σ), A s <~> B s.
Proof.
  intro s. rapply (Build_Equiv _ _ (f s)).
Defined.

Global Instance hprop_is_isomorphism `{Funext} {σ : Signature}
  {A B : Algebra σ} (f : ∀ s, A s → B s) `{!IsHomomorphism f}
  : IsHProp (IsIsomorphism f).
Proof.
  apply trunc_forall.
Qed.

(** The next section shows that the family of identity functions,
    [λ s x, x] is an isomorphism. *)

Section hom_id.
  Context {σ} (A : Algebra σ).

  Global Instance is_homomorphism_id
    : IsHomomorphism (λ s (x : A s), x).
  Proof.
    intros u a. reflexivity.
  Defined.

  Global Instance is_isomorphism_id
    : IsIsomorphism (λ s (x : A s), x).
  Proof.
    intro s. exact _.
  Qed.

  Definition hom_id : Homomorphism A A
    := Build_Homomorphism (λ s x, x).

End hom_id.

(** Suppose [f : ∀ s, A s → B s] is an isomorphism. The following
    section shows that the family of inverse functions, [λ s, (f s)^-1]
    is an isomorphism. *)

Section hom_inv.
  Context
    `{Funext} {σ} {A B : Algebra σ}
    (f : ∀ s, A s → B s) `{IsIsomorphism σ A B f}.

  Global Instance is_homomorphism_inv : IsHomomorphism (λ s, (f s)^-1).
  Proof.
   intros u a.
   apply (ap (f (sort_cod (σ u))))^-1.
   rewrite (oppreserving_hom f).
   refine (eisretr _ _ @ _).
   f_ap.
   funext X.
   symmetry; apply eisretr.
  Qed.

  Global Instance is_isomorphism_inv : IsIsomorphism (λ s, (f s)^-1).
  Proof.
    intro s. exact _.
  Qed.

  Definition hom_inv : Homomorphism B A
    := Build_Homomorphism (λ s, (f s)^-1).

End hom_inv.

(** Let [f : ∀ s, A s → B s] and [g : ∀ s, B s → C s]. The
    next section shows that composition given by [λ (s : Sort σ),
    g s o f s] is again a homomorphism. If both [f] and [g] are
    isomorphisms, then the composition is an isomorphism. *)

Section hom_compose.
  Context {σ} {A B C : Algebra σ}.

  Global Instance is_homomorphism_compose
    (g : ∀ s, B s → C s) `{!IsHomomorphism g}
    (f : ∀ s, A s → B s) `{!IsHomomorphism f}
    : IsHomomorphism (λ s, g s o f s).
  Proof.
    intros u a.
    by rewrite <- (oppreserving_hom g), (oppreserving_hom f).
  Qed.

  Global Instance is_isomorphism_compose
    (g : ∀ s, B s → C s) `{IsIsomorphism σ B C g}
    (f : ∀ s, A s → B s) `{IsIsomorphism σ A B f}
    : IsIsomorphism (λ s, g s o f s).
  Proof.
    intro s. apply isequiv_compose.
  Qed.

  Definition hom_compose
    (g : Homomorphism B C) (f : Homomorphism A B)
    : Homomorphism A C
    := Build_Homomorphism (λ s, g s o f s).

End hom_compose.

(** The following section shows that there is a path between
    isomorphic algebras. *)

Section path_isomorphism.
  Context `{Univalence} {σ : Signature} {A B : Algebra σ}.

(** Let [F G : I → Type]. If [f : ∀ (i:I), F i <~> G i] is a family of
    equivalences, then by function extensionality composed with
    univalence there is a path [F = G]. *)

  Local Notation path_equiv_family f
    := (path_forall _ _ (λ i, path_universe (f i))).

(** Given a family of equivalences [f : ∀ (s : Sort σ), A s <~> B s]
    which is [OpPreserving f α β] with respect to algebra operations

    <<
      α : A s1 → A s2 → ... → A sn → A t
      β : B s1 → B s2 → ... → B sn → B t
    >>

    By transporting [α] along the path [path_equiv_family f] we
    find a path from the transported operation [α] to [β]. *)

  Lemma path_operations_equiv {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w)
    (f : ∀ (s : Sort σ), A s <~> B s) (P : OpPreserving f α β)
    : transport (λ C, Operation C w) (path_equiv_family f) α = β.
  Proof.
    unfold Operation.
    funext a.
    transport_path_forall_hammer.
    rewrite transport_arrow_toconst.
    rewrite transport_forall_constant.
    rewrite transport_idmap_path_universe.
    rewrite P.
    f_ap.
    funext X.
    rewrite transport_forall_constant.
    rewrite <- path_forall_V.
    transport_path_forall_hammer.
    rewrite (transport_path_universe_V (f _)).
    apply eisretr.
  Qed.

(** Suppose [u : Symbol σ] is a function symbol. Recall that
    [u^^A] is notation for [operations A u : Operation A (σ u)]. This
    is the algebra operation corresponding to function symbol [u]. *)

(** An isomorphism [f : ∀ s, A s → B s] induces a family of
    equivalences [e : ∀ (s : Sort σ), A s <~> B s]. Let [u : Symbol σ]
    be a function symbol. Since [f] is a homomorphism, the induced
    family of equivalences [e] satisfies [OpPreserving e (u^^A) (u^^B)].
    By [path_operations_equiv] above, we can then transport [u^^A] along
    the path [path_equiv_family e] and obtain a path to [u^^B]. *)

  Lemma path_operations_isomorphism (f : ∀ s, A s → B s)
    `{IsIsomorphism σ A B f}
    : transport (λ C, forall u, Operation C (σ u))
        (path_equiv_family (equiv_isomorphism f)) (operations A)
      = operations B.
  Proof.
    funext u.
    refine (transport_forall_constant _ _ u @ _).
    now apply path_operations_equiv.
  Qed.

(** If there is an isomorphism [f : ∀ s, A s → B s] then [A = B]. *)

  Theorem path_isomorphism (f : ∀ s, A s → B s) `{IsIsomorphism σ A B f}
    : A = B.
  Proof.
    apply (path_algebra _ _ (path_equiv_family (equiv_isomorphism f))).
    apply path_operations_isomorphism.
  Defined.
End path_isomorphism.
