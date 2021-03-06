(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import Fibrations EquivalenceVarieties Extensions Factorization NullHomotopy HProp Pullback.
Require Export ReflectiveSubuniverse. (* [Export] because many of the lemmas and facts about reflective subuniverses are equally important for modalities. *)
Require Import HoTT.Tactics.

Local Open Scope path_scope.

(** * Modalities *)

Module Type Modalities.

  Parameter Modality@{u a} : Type2@{u a}.

  (** These are the same as for a reflective subuniverse. *)

  Parameter O_reflector@{u a i} : forall (O : Modality@{u a}),
                            Type2le@{i a} -> Type2le@{i a}.

  Parameter In@{u a i} : forall (O : Modality@{u a}),
                            Type2le@{i a} -> Type2le@{i a}.

  Parameter O_inO@{u a i} : forall (O : Modality@{u a}) (T : Type@{i}),
                               In@{u a i} O (O_reflector@{u a i} O T).

  Parameter to@{u a i} : forall (O : Modality@{u a}) (T : Type@{i}),
                   T -> O_reflector@{u a i} O T.

  Parameter inO_equiv_inO@{u a i j k} :
      forall (O : Modality@{u a}) (T : Type@{i}) (U : Type@{j})
             (T_inO : In@{u a i} O T) (f : T -> U) (feq : IsEquiv f),
        (** We add an extra universe parameter that's bigger than both [i] and [j].  This seems to be necessary for the proof of repleteness in some examples, such as easy modalities. *)
        let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
        let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
        In@{u a j} O U.

  Parameter hprop_inO@{u a i}
  : Funext -> forall (O : Modality@{u a}) (T : Type@{i}),
                IsHProp (In@{u a i} O T).

  Parameter IsSepFor@{u a} : forall (O' O : Modality@{u a}), Type@{u}.

  Parameter inO_paths_from_inSepO@{u a i iplus}
    : forall (O' O : Modality@{u a}) (sep : IsSepFor O' O)
             (A : Type@{i}) (A_inO : In@{u a i} O' A) (x y : A),
      let gt := (Type1@{i} : Type@{iplus}) in
      In@{u a i} O (x = y).

  Parameter inSepO_from_inO_paths@{u a i iplus}
    : forall (O' O : Modality@{u a}) (sep : IsSepFor O' O)
             (A : Type@{i}),
      let gt := (Type1@{i} : Type@{iplus}) in
      (forall (x y : A), In@{u a i} O (x = y)) -> In@{u a i} O' A.

  (** Now instead of [extendable_to_O], we have an ordinary induction principle. *)

  (** Unfortunately, we have to define these parameters as [_internal] versions and redefine them later.  This is because eventually we want the [In] fields of [O_ind] and [O_ind_beta] to refer to the [In] typeclass defined for [ReflectiveSubuniverse]s, but in order to prove that modalities *are* reflective subuniverses we need to already have [O_ind] and [O_ind_beta]. *)
  Parameter O_ind_internal@{u a i j k}
  : forall (O : Modality@{u a})
           (A : Type2le@{i a})
           (B : O_reflector@{u a i} O A -> Type2le@{j a})
           (B_inO : forall oa, In@{u a j} O (B oa)),
      (** We add an extra unused universe parameter [k] that's [>= max(i,j)].  This seems to be necessary for some examples, such as [Nullification], which are constructed by way of an operation that requires such a universe.  *)
      let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
      let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
      (forall a, B (to O A a)) -> forall a, B a.

  Parameter O_ind_beta_internal@{u a i j k}
  : forall (O : Modality@{u a})
           (A : Type@{i}) (B : O_reflector O A -> Type@{j})
           (B_inO : forall oa, In@{u a j} O (B oa))
           (f : forall a : A, B (to O A a)) (a:A),
      O_ind_internal@{u a i j k} O A B B_inO f (to O A a) = f a.

  Parameter minO_paths@{u a i}
  : forall (O : Modality@{u a})
           (A : Type2le@{i a}) (A_inO : In@{u a i} O A) (z z' : A),
      In@{u a i} O (z = z').

End Modalities.

(** ** Modalities are reflective subuniverses *)

(** We show that modalities have underlying reflective subuniverses.  It is important in some applications, such as [Trunc], that this construction uses the general [O_ind] given as part of the modality data.  For instance, this ensures that [O_functor] reduces to simply an application of [O_ind].

  Note also that our choice of how to define reflective subuniverses differently from the book, using [ooExtendableAlong] enables us to prove this without using funext. *)

Module Modalities_to_ReflectiveSubuniverses
       (Os : Modalities) <: ReflectiveSubuniverses.

  Import Os.

  Fixpoint O_extendable@{u a i j k} (O : Modality@{u a})
           (A : Type@{i}) (B : O_reflector O A -> Type@{j})
           (B_inO : forall a, In@{u a j} O (B a)) (n : nat)
  : ExtendableAlong@{i i j k} n (to O A) B.
  Proof.
    destruct n as [|n].
    - exact tt.
    - split.
      + intros g.
        exists (O_ind_internal@{u a i j k} O A B B_inO g); intros x.
        apply O_ind_beta_internal.
      + intros h k.
        apply O_extendable; intros x.
        apply minO_paths; trivial.
  Defined.

  Definition ReflectiveSubuniverse := Modality.

  Definition O_reflector@{u a i} := O_reflector@{u a i}.
  (** Work around https://coq.inria.fr/bugs/show_bug.cgi?id=3807 *)
  Definition In@{u a i} : forall (O : ReflectiveSubuniverse@{u a}),
                   Type2le@{i a} -> Type2le@{i a}
    := In@{u a i}.
  Definition O_inO@{u a i} : forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                               In@{u a i} O (O_reflector@{u a i} O T)
    := O_inO@{u a i}.
  Definition to@{u a i} := to@{u a i}.
  Definition inO_equiv_inO@{u a i j k} :
      forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}) (U : Type@{j})
             (T_inO : In@{u a i} O T) (f : T -> U) (feq : IsEquiv f),
        In@{u a j} O U
    := inO_equiv_inO@{u a i j k}.
  Definition hprop_inO@{u a i}
  : Funext -> forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
                IsHProp (In@{u a i} O T)
    := hprop_inO@{u a i}.
  Definition IsSepFor@{u a} := IsSepFor@{u a}.
  Definition inO_paths_from_inSepO@{u a i iplus} := inO_paths_from_inSepO@{u a i iplus}.
  Definition inSepO_from_inO_paths@{u a i iplus} := inSepO_from_inO_paths@{u a i iplus}.

  (** Corollary 7.7.8, part 1 *)
  Definition extendable_to_O@{u a i j k} (O : ReflectiveSubuniverse@{u a})
             {P : Type2le@{i a}} {Q : Type2le@{j a}} {Q_inO : In@{u a j} O Q}
  : ooExtendableAlong@{i i j k} (to O P) (fun _ => Q)
    := fun n => O_extendable O P (fun _ => Q) (fun _ => Q_inO) n.

End Modalities_to_ReflectiveSubuniverses.


(** Conversely, if a reflective subuniverse is closed under sigmas, it is a modality.  This is a bit annoying to state using modules, but it is not really a problem in practice: in most or all examples, constructing [O_ind] directly is just as easy, and preferable because it sometimes gives a judgmental computation rule. *)

Module Type SigmaClosed (Os : ReflectiveSubuniverses).

  Import Os.

  Parameter inO_sigma@{u a i j k}
  : forall (O : ReflectiveSubuniverse@{u a})
           (A:Type@{i}) (B:A -> Type@{j})
           (A_inO : In@{u a i} O A)
           (B_inO : forall a, In@{u a j} O (B a)),
      In@{u a k} O {x:A & B x}.

End SigmaClosed.

Module ReflectiveSubuniverses_to_Modalities
       (Os : ReflectiveSubuniverses) (OsSigma : SigmaClosed Os)
  <: Modalities.

  Import Os OsSigma.
  Module Import Os_Theory := ReflectiveSubuniverses_Theory Os.

  Definition Modality := ReflectiveSubuniverse.

  Definition O_reflector@{u a i} := O_reflector@{u a i}.
  (** Work around https://coq.inria.fr/bugs/show_bug.cgi?id=3807 *)
  Definition In@{u a i} := In@{u a i}.
  Definition O_inO@{u a i} := @O_inO@{u a i}.
  Definition to@{u a i} := to@{u a i}.
  Definition inO_equiv_inO@{u a i j k} := @inO_equiv_inO@{u a i j k}.
  Definition hprop_inO@{u a i} := hprop_inO@{u a i}.
  Definition IsSepFor@{u a} := IsSepFor@{u a}.
  Definition inO_paths_from_inSepO@{u a i iplus} := inO_paths_from_inSepO@{u a i iplus}.
  Definition inSepO_from_inO_paths@{u a i iplus} := inSepO_from_inO_paths@{u a i iplus}.

  Definition O_ind_internal@{u a i j k} (O : Modality@{u a})
             (A : Type@{i}) (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa, In@{u a j} O (B oa))
  : (forall a, B (to O A a)) -> forall a, B a
  := fun g => pr1 ((O_ind_from_inO_sigma@{u a i j k} O (inO_sigma O))
                     A B B_inO g).

  Definition O_ind_beta_internal@{u a i j k} (O : Modality@{u a})
             (A : Type@{i}) (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa, In@{u a j} O (B oa))
             (f : forall a : A, B (to O A a)) (a:A)
  : O_ind_internal O A B B_inO f (to O A a) = f a
  := pr2 ((O_ind_from_inO_sigma@{u a i j k} O (inO_sigma O))
                     A B B_inO f) a.

  Definition minO_paths@{u a i} (O : Modality@{u a})
             (A : Type@{i}) (A_inO : In@{u a i} O A) (z z' : A)
  : In O (z = z')
  := @inO_paths@{u a i i} O A A_inO z z'.

End ReflectiveSubuniverses_to_Modalities.


(** ** Easy modalities *)

(** Our definition of modality is slightly different from the one in the book, which requires an induction principle only into families of the form [fun oa => O (B oa)], and similarly only that path-spaces of types [O A] are modal, where "modal" means that the unit is an equivalence.  This is equivalent, roughly since every modal type [A] (in this sense) is equivalent to [O A].

However, our definition is more convenient in formalized applications because in some examples (such as [Trunc] and closed modalities), there is a naturally occurring [O_ind] into all modal types that is not judgmentally equal to the one that can be constructed by passing through [O] and back again.  Thus, when we apply general theorems about modalities to a particular modality such as [Trunc], the proofs will reduce definitionally to "the way we would have proved them directly" if we didn't know about general modalities.

On the other hand, in other examples (such as [~~] and open modalities) it is easier to construct the latter weaker induction principle.  Thus, we now show how to get from that to our definition of modality. *)

Module Type EasyModalities.

  Parameter Modality@{u a} : Type2@{u a}.

  Parameter O_reflector@{u a i} : forall (O : Modality@{u a}),
                            Type2le@{i a} -> Type2le@{i a}.

  Parameter to@{u a i} : forall (O : Modality@{u a}) (T : Type@{i}),
                   T -> O_reflector@{u a i} O T.

  Parameter O_indO@{u a i j}
  : forall (O : Modality@{u a}) (A : Type@{i})
           (B : O_reflector@{u a i} O A -> Type@{j}),
      (forall a, O_reflector@{u a j} O (B (to O A a)))
      -> forall z, O_reflector@{u a j} O (B z).

  Parameter O_indO_beta@{u a i j}
  : forall (O : Modality@{u a}) (A : Type@{i})
           (B : O_reflector@{u a i} O A -> Type@{j})
           (f : forall a, O_reflector@{u a j} O (B (to O A a))) a,
      O_indO O A B f (to O A a) = f a.

  Parameter minO_pathsO@{u a i}
  : forall (O : Modality@{u a}) (A : Type@{i})
           (z z' : O_reflector@{u a i} O A),
      IsEquiv (to@{u a i} O (z = z')).

End EasyModalities.

Module EasyModalities_to_Modalities (Os : EasyModalities)
<: Modalities.

  Import Os.

  Definition Modality := Modality.
  (** Work around https://coq.inria.fr/bugs/show_bug.cgi?id=3807 *)
  Definition O_reflector@{u a i} := O_reflector@{u a i}.
  Definition to@{u a i} := to@{u a i}.

  Definition In@{u a i}
  : forall (O : Modality@{u a}), Type@{i} -> Type@{i}
  := fun O A => IsEquiv@{i i} (to O A).

  Definition hprop_inO@{u a i} `{Funext} (O : Modality@{u a})
             (T : Type@{i})
  : IsHProp (In@{u a i} O T).
  Proof.
    unfold In.
    exact (hprop_isequiv (to O T)).
  Defined.

  Definition O_ind_internal@{u a i j k} (O : Modality@{u a})
             (A : Type@{i}) (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa, In@{u a j} O (B oa))
  : let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
    let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
    (forall a, B (to O A a)) -> forall oa, B oa.
  Proof.
    simpl; intros f oa.
    pose (H := B_inO oa); unfold In in H.
    apply ((to O (B oa))^-1).
    apply O_indO.
    intros a; apply to, f.
  Defined.

  Definition O_ind_beta_internal@{u a i j k} (O : Modality@{u a})
             (A : Type@{i}) (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa, In@{u a j} O (B oa))
             (f : forall a : A, B (to O A a)) (a:A)
  : O_ind_internal@{u a i j k} O A B B_inO f (to O A a) = f a.
  Proof.
    unfold O_ind_internal.
    apply moveR_equiv_V.
    apply @O_indO_beta with (f := fun x => to O _ (f x)).
  Qed.

  Definition O_inO@{u a i} (O : Modality@{u a}) (A : Type@{i})
  : In@{u a i} O (O_reflector@{u a i} O A).
  Proof.
    refine (isequiv_adjointify (to O (O_reflector O A))
             (O_indO O (O_reflector O A) (fun _ => A) idmap) _ _).
    - intros x; pattern x; apply O_ind_internal.
      + intros oa; apply minO_pathsO.
      + intros a; apply ap.
        exact (O_indO_beta O (O_reflector O A) (fun _ => A) idmap a).
    - intros a.
      exact (O_indO_beta O (O_reflector O A) (fun _ => A) idmap a).
  Defined.

  (** It seems to be surprisingly hard to show repleteness (without univalence).  We basically have to manually develop enough functoriality of [O] and naturality of [to O]. *)
  Definition inO_equiv_inO@{u a i j k} (O : Modality@{u a}) (A : Type@{i}) (B : Type@{j})
    (A_inO : In@{u a i} O A) (f : A -> B) (feq : IsEquiv f)
  : In@{u a j} O B.
  Proof.
    simple refine (isequiv_commsq (to O A) (to O B) f
             (O_ind_internal O A (fun _ => O_reflector O B) _ (fun a => to O B (f a))) _).
    - intros; apply O_inO.
    - intros a; refine (O_ind_beta_internal@{u a i j k} O A (fun _ => O_reflector O B) _ _ a).
    - apply A_inO.
    - simple refine (isequiv_adjointify _
               (O_ind_internal O B (fun _ => O_reflector O A) _ (fun b => to O A (f^-1 b))) _ _);
        intros x.
      + apply O_inO.
      + pattern x; refine (O_ind_internal O B _ _ _ x); intros.
        * apply minO_pathsO.
        * simpl; abstract (repeat rewrite O_ind_beta_internal; apply ap, eisretr).
      + pattern x; refine (O_ind_internal O A _ _ _ x); intros.
        * apply minO_pathsO.
        * simpl; abstract (repeat rewrite O_ind_beta_internal; apply ap, eissect).
  Defined.

  Definition minO_paths@{u a i} (O : Modality@{u a})
             (A : Type@{i}) (A_inO : In@{u a i} O A) (a a' : A)
  : In@{u a i} O (a = a').
  Proof.
    simple refine (inO_equiv_inO O (to O A a = to O A a') _ _
                          (@ap _ _ (to O A) a a')^-1 _).
    - apply minO_pathsO.
    - refine (@isequiv_ap _ _ _ A_inO _ _).
    - apply isequiv_inverse.
  Defined.

  (** We don't bother including separatedness for modalities constructed in this way.  (We could.)  *)
  Definition IsSepFor@{u a} (O' O : Modality@{u a}) : Type@{u}
    := Empty.

  Definition inO_paths_from_inSepO@{u a i iplus}
            (O' O : Modality@{u a}) (sep : IsSepFor O' O)
            (A : Type@{i}) (A_inO : In@{u a i} O' A) (x y : A)
    : In@{u a i} O (x = y)
    := Empty_rec sep.

  Definition inSepO_from_inO_paths@{u a i iplus}
             (O' O : Modality@{u a}) (sep : IsSepFor O' O)
             (A : Type@{i}) (op : forall (x y : A), In@{u a i} O (x = y))
    : In@{u a i} O' A
    := Empty_rec sep.

End EasyModalities_to_Modalities.

(** We now move on to the general theory of modalities. *)

Module Modalities_Theory (Os : Modalities).

Export Os.
Module Export Os_ReflectiveSubuniverses
  := Modalities_to_ReflectiveSubuniverses Os.
Module Export RSU
  := ReflectiveSubuniverses_Theory Os_ReflectiveSubuniverses.

(** As with reflective subuniverses, we put this in a module so it can be exported separately (and it should be). *)
Module Export Coercions.
  Coercion modality_to_reflective_subuniverse
    := idmap : Modality -> ReflectiveSubuniverse.
End Coercions.

(** As promised, we redefine [O_ind] and [O_ind_beta] so that their [In] hypotheses refer to the typeclass [RSU.In]. *)
Definition O_ind@{u a i j e0 e1 e2} {O : Modality@{u a}}
           {A : Type@{i}} (B : O A -> Type@{j})
           {B_inO : forall oa, In O (B oa)}
           (f : forall a, B (to O A a)) (oa : O A)
: B oa
:= O_ind_internal@{u a e0 e1 e2} O A B B_inO f oa.

Definition O_ind_beta {O : Modality@{u a}}
           {A : Type@{i}} (B : O A -> Type@{j})
           {B_inO : forall oa, In O (B oa)}
           (f : forall a : A, B (to O A a)) (a : A)
: @O_ind O A B B_inO f (to O A a) = f a
:= O_ind_beta_internal O A B B_inO f a.

(** ** The induction principle [O_ind], like most induction principles, is an equivalence. *)
Section OIndEquiv.
  Context {fs : Funext} (O : Modality).

  Section OIndEquivData.

    Context {A : Type} (B : O A -> Type) `{forall a, In O (B a)}.

    Global Instance isequiv_O_ind : IsEquiv (O_ind B).
    Proof.
      apply isequiv_adjointify with (g := fun h => h oD to O A).
      - intros h. apply path_forall.
        refine (O_ind (fun oa => O_ind B (h oD to O A) oa = h oa) _).
        exact (O_ind_beta B (h oD to O A)).
      - intros f. apply path_forall.
        exact (O_ind_beta B f).
    Defined.

    Definition equiv_O_ind
    : (forall a, B (to O A a)) <~> (forall oa, B oa)
    := Build_Equiv _ _ (O_ind B) _.

    (** Theorem 7.7.7 *)
    Definition isequiv_oD_to_O
    : IsEquiv (fun (h : forall oa, B oa) => h oD to O A)
    := equiv_isequiv equiv_O_ind^-1.

  End OIndEquivData.

  Local Definition isequiv_o_to_O (A B : Type) (B_inO : In O B)
  : IsEquiv (fun (h : O A -> B) => h o to O A)
    := isequiv_oD_to_O (fun _ => B).

End OIndEquiv.

(** Two modalities are the same if they have the same modal types. *)
Class OeqO (O1 O2 : Modality)
  := inO_OeqO : forall A, In O1 A <-> In O2 A.

Global Instance reflexive_OeqO : Reflexive OeqO | 10.
Proof.
  intros O A; reflexivity.
Defined.

Global Instance symmetric_OeqO : Symmetric OeqO | 10.
Proof.
  intros O1 O2 O12 A.
  specialize (O12 A).
  symmetry; assumption.
Defined.

Global Instance transitive_OeqO : Transitive OeqO | 10.
Proof.
  intros O1 O2 O3 O12 O23 A; split.
  - intros A1.
    apply (@inO_OeqO O2 O3 O23).
    apply (@inO_OeqO O1 O2 O12).
    exact A1.
  - intros A3.
    apply (@inO_OeqO O1 O2 O12).
    apply (@inO_OeqO O2 O3 O23).
    exact A3.
Defined.

(** Two equivalent modalities have the same connected types. *)
Global Instance isconnected_OeqO {O1 O2 : Modality} `{OeqO O1 O2}
       (A : Type) `{IsConnected O1 A}
  : IsConnected O2 A.
Proof.
  apply isconnected_from_elim.
  intros C C2 f.
  apply (isconnected_elim O1); apply inO_OeqO; exact _.
Defined.

(** We prove some useful consequences of [O_ind] that enhance the behavior of reflective subuniverses. *)
Section Enhancements.
  Context {O : Modality}.

  (** Corollary 7.5.8: The unit maps [to O A] are connected. *)
  Global Instance conn_map_to_O (A : Type) : IsConnMap O (to O A).
  Proof.
    apply conn_map_from_extension_elim; intros P ? d.
    exists (O_ind P d); intros a.
    apply O_ind_beta.
  Defined.

  (** Corollary 7.7.8, part 2 *)
  Global Instance inO_sigma (A:Type) (B:A -> Type)
         `{In O A} `{forall a, In O (B a)}
  : In O {x:A & B x}.
  Proof.
    generalize dependent A.
    refine (inO_sigma_from_O_ind _ _).
    intros A B ? g.
    exists (O_ind B g).
    apply O_ind_beta.
  Defined.

  (** This implies that the composite of modal maps is modal. *)
  Global Instance mapinO_compose {A B C : Type} (f : A -> B) (g : B -> C)
         `{MapIn O _ _ f} `{MapIn O _ _ g}
  : MapIn O (g o f).
  Proof.
    intros c.
    refine (inO_equiv_inO _ (hfiber_compose f g c)^-1).
  Defined.

  (** Corollary 7.3.10.  (Theorem 7.3.9 is true for any reflective subuniverse.) *)
  Corollary equiv_sigma_inO_O {A} `{In O A} (P : A -> Type)
  : {x:A & O (P x)} <~> O {x:A & P x}.
  Proof.
    transitivity (O {x:A & O (P x)}).
    - apply equiv_to_O; exact _.
    - apply equiv_O_sigma_O.
  Defined.

End Enhancements.

(** An enhancement of Corollary 2.29 of CORS: when O (hence also O') is a modality, the map between fibers is not just an O-equivalence but is O-connected. *)
Global Instance conn_map_functor_hfiber `{Univalence} {O O' : Modality} `{IsSepFor O' O}
       {Y X : Type} (f : Y -> X) (x : X)
  : IsConnMap O (functor_hfiber (fun y => (to_O_natural O' f y)^) x).
Proof.
  intros [oy p].
  rewrite <- (inv_V p).
  ntc_refine (isconnected_equiv' O _
               (hfiber_functor_hfiber (to_O_natural O' f) oy x p^) _).
  ntc_refine (isconnected_hfiber_conn_map
                (f := (functor_hfiber (to_O_natural O' f) oy)) (x;p^)).
  apply conn_map_SepO_inverts.
  (* Actually typeclasss search can do the rest by itself, but to help the human reader we show what's going on.  (As a byproduct this makes it marginally faster too). *)
  apply O_inverts_isconnected. 
  - apply conn_map_to_O.
  - apply conn_map_to_O.
Defined.

(** ** The modal factorization system *)

Section ModalFact.
  Context `{fs : Funext} (O : Modality).

  (** Lemma 7.6.4 *)
  Definition image {A B : Type} (f : A -> B)
  : Factorization (@IsConnMap O) (@MapIn O) f.
  Proof.
    refine (Build_Factorization {b : B & O (hfiber f b)}
                                (fun a => (f a ; to O _ (a;1)))
                                pr1
                                (fun a => 1)
                                _ _).
    - exact (conn_map_compose O
              (equiv_fibration_replacement f)
              (functor_sigma idmap (fun b => to O (hfiber f b)))).
  Defined.

  Global Instance conn_map_factor1_image {A B : Type} (f : A -> B)
  : IsConnMap O (factor1 (image f))
    := inclass1 (image f).

  Global Instance inO_map_factor1_image {A B : Type} (f : A -> B)
  : MapIn O (factor2 (image f))
    := inclass2 (image f).

  (** This is the composite of the three displayed equivalences at the beginning of the proof of Lemma 7.6.5.  Note that it involves only a single factorization of [f]. *)
  Lemma O_hfiber_O_fact {A B : Type} {f : A -> B}
        (fact : Factorization (@IsConnMap O) (@MapIn O) f) (b : B)
  : O (hfiber (factor2 fact o factor1 fact) b)
      <~> hfiber (factor2 fact) b.
  Proof.
    refine (_ oE
             (equiv_O_functor O
               (hfiber_compose (factor1 fact) (factor2 fact) b))).
    refine (equiv_sigma_contr (fun w => O (hfiber (factor1 fact) w.1)) oE _).
    - intros w; exact (inclass1 fact w.1).
    - refine ((equiv_sigma_inO_O (fun w => hfiber (factor1 fact) w.1))^-1)%equiv.
      exact (inclass2 fact b).
  Defined.

  (** This is the corresponding first three of the displayed "mapsto"s in proof of Lemma 7.6.5, and also the last three in reverse order, generalized to an arbitrary path [p].  Note that it is much harder to prove than in the book, because we are working in the extra generality of a modality where [O_ind_beta] is only propositional. *)
  Lemma O_hfiber_O_fact_inverse_beta {A B : Type} {f : A -> B}
        (fact : Factorization (@IsConnMap O) (@MapIn O) f)
        (a : A) (b : B) (p : factor2 fact (factor1 fact a) = b)
  : (O_hfiber_O_fact fact b)^-1
      (factor1 fact a ; p) = to O _ (a ; p).
  Proof.
    set (g := factor1 fact); set (h := factor2 fact).
    apply moveR_equiv_V.
    unfold O_hfiber_O_fact.
    ev_equiv.
    apply moveL_equiv_M.
    transitivity (existT (fun (w : hfiber h b) => O (hfiber g w.1))
                         (g a; p) (to O (hfiber g (g a)) (a ; 1))).
    - apply moveR_equiv_V; reflexivity.
    - apply moveL_equiv_V.
      transitivity (to O _ (existT (fun (w : hfiber h b) => (hfiber g w.1))
                         (g a; p) (a ; 1))).
      + simpl; repeat rewrite O_rec_beta; reflexivity.
      + symmetry; apply to_O_natural.
  Qed.

  Section TwoFactorizations.
    Context {A B : Type} (f : A -> B)
            (fact fact' : Factorization (@IsConnMap O) (@MapIn O) f).

    Let H := fun x => fact_factors fact x @ (fact_factors fact' x)^.

    (** Lemma 7.6.5, part 1. *)
    Definition equiv_O_factor_hfibers (b:B)
    : hfiber (factor2 fact) b <~> hfiber (factor2 fact') b.
    Proof.
      refine (O_hfiber_O_fact fact' b oE _).
      refine (_ oE (O_hfiber_O_fact fact b)^-1).
      apply equiv_O_functor.
      apply equiv_hfiber_homotopic.
      exact H.
    Defined.

    (** Lemma 7.6.5, part 2. *)
    Definition equiv_O_factor_hfibers_beta (a : A)
    : equiv_O_factor_hfibers (factor2 fact (factor1 fact a))
                             (factor1 fact a ; 1)
      = (factor1 fact' a ; (H a)^).
    Proof.
      unfold equiv_O_factor_hfibers.
      ev_equiv.
      apply moveR_equiv_M.
      do 2 rewrite O_hfiber_O_fact_inverse_beta.
      unfold equiv_fun, equiv_O_functor.
      transitivity (to O _
                       (equiv_hfiber_homotopic
                          (factor2 fact o factor1 fact)
                          (factor2 fact' o factor1 fact') H
                          (factor2 fact (factor1 fact a)) (a;1))).
      - refine (to_O_natural O _ _).
      - apply ap.
        simpl.
        apply ap; auto with path_hints.
    Qed.

  End TwoFactorizations.

  (** Theorem 7.6.6.  Recall that a lot of hard work was done in [Factorization.path_factorization]. *)
  Definition O_factsys : FactorizationSystem.
  Proof.
    refine (Build_FactorizationSystem
              (@IsConnMap O) _ _ _
              (@MapIn O) _ _ _
              (@image) _).
    intros A B f fact fact'.
    simple refine (Build_PathFactorization fact fact' _ _ _ _).
    - refine (_ oE equiv_fibration_replacement (factor2 fact)).
      refine ((equiv_fibration_replacement (factor2 fact'))^-1 oE _).
      refine (equiv_functor_sigma' 1 _); intros b; simpl.
      apply equiv_O_factor_hfibers.
    - intros a; exact (pr1_path (equiv_O_factor_hfibers_beta f fact fact' a)).
    - intros x.
      exact ((equiv_O_factor_hfibers f fact fact' (factor2 fact x) (x ; 1)).2 ^).
    - intros a.
      apply moveR_pM.
      refine ((inv_V _)^ @ _ @ inv_V _); apply inverse2.
      refine (_ @ pr2_path (equiv_O_factor_hfibers_beta f fact fact' a)).
      refine (_ @ (transport_paths_Fl _ _)^).
      (** Apparently Coq needs a little help to see that these paths are the same. *)
      match goal with
          |- ((?p)^ @ ?q)^ = _ @ _ => change ((p^ @ q)^ = q^ @ p)
      end.
      refine (inv_pp _ _ @ (1 @@ inv_V _)).
  Defined.

End ModalFact.

End Modalities_Theory.

(** ** Restriction of a family of modalities *)

(** This is just like restriction of reflective subuniverses. *)
Module Type Modalities_Restriction_Data (Os : Modalities).

  Parameter New_Modality : Type2@{u a}.

  Parameter Modalities_restriction
  : New_Modality -> Os.Modality.

End Modalities_Restriction_Data.

Module Modalities_Restriction
       (Os : Modalities)
       (Res : Modalities_Restriction_Data Os)
<: Modalities.

  Definition Modality := Res.New_Modality.

  Definition O_reflector (O : Modality@{u a})
    := Os.O_reflector@{u a i} (Res.Modalities_restriction O).
  Definition In (O : Modality@{u a})
    := Os.In@{u a i} (Res.Modalities_restriction O).
  Definition O_inO (O : Modality@{u a})
    := Os.O_inO@{u a i} (Res.Modalities_restriction O).
  Definition to (O : Modality@{u a})
    := Os.to@{u a i} (Res.Modalities_restriction O).
  Definition inO_equiv_inO (O : Modality@{u a})
    := Os.inO_equiv_inO@{u a i j k} (Res.Modalities_restriction O).
  Definition hprop_inO (H : Funext) (O : Modality@{u a})
    := Os.hprop_inO@{u a i} H (Res.Modalities_restriction O).
  Definition O_ind_internal (O : Modality@{u a})
    := Os.O_ind_internal@{u a i j k} (Res.Modalities_restriction O).
  Definition O_ind_beta_internal (O : Modality@{u a})
    := Os.O_ind_beta_internal@{u a i j k} (Res.Modalities_restriction O).
  Definition minO_paths (O : Modality@{u a})
    := Os.minO_paths@{u a i} (Res.Modalities_restriction O).
  Definition IsSepFor@{u a} (O' O : Modality@{u a})
    := @Os.IsSepFor@{u a} (Res.Modalities_restriction@{u a} O') (Res.Modalities_restriction@{u a} O).
  Definition inO_paths_from_inSepO@{u a i iplus} (O' O : Modality@{u a})
    := @Os.inO_paths_from_inSepO@{u a i iplus} (Res.Modalities_restriction@{u a} O') (Res.Modalities_restriction@{u a} O).
  Definition inSepO_from_inO_paths@{u a i iplus} (O' O : Modality@{u a})
    := @Os.inSepO_from_inO_paths@{u a i iplus} (Res.Modalities_restriction@{u a} O') (Res.Modalities_restriction@{u a} O).

End Modalities_Restriction.

(** ** Union of families of modalities *)

Module Modalities_FamUnion (Os1 Os2 : Modalities)
       <: Modalities.

  Definition Modality : Type2@{u a}
    := Os1.Modality@{u a} + Os2.Modality@{u a}.

  Coercion Mod_inl := inl : Os1.Modality -> Modality.
  Coercion Mod_inr := inr : Os2.Modality -> Modality.

  Definition O_reflector : forall (O : Modality@{u a}),
                            Type2le@{i a} -> Type2le@{i a}.
  Proof.
    intros [O|O]; [ exact (Os1.O_reflector@{u a i} O)
                  | exact (Os2.O_reflector@{u a i} O) ].
  Defined.

  Definition In : forall (O : Modality@{u a}),
                            Type2le@{i a} -> Type2le@{i a}.
  Proof.
    intros [O|O]; [ exact (Os1.In@{u a i} O)
                  | exact (Os2.In@{u a i} O) ].
  Defined.

  Definition O_inO : forall (O : Modality@{u a}) (T : Type@{i}),
                               In@{u a i} O (O_reflector@{u a i} O T).
  Proof.
    intros [O|O]; [ exact (Os1.O_inO@{u a i} O)
                  | exact (Os2.O_inO@{u a i} O) ].
  Defined.

  Definition to : forall (O : Modality@{u a}) (T : Type@{i}),
                   T -> O_reflector@{u a i} O T.
  Proof.
    intros [O|O]; [ exact (Os1.to@{u a i} O)
                  | exact (Os2.to@{u a i} O) ].
  Defined.

  Definition inO_equiv_inO :
      forall (O : Modality@{u a}) (T : Type@{i}) (U : Type@{j})
             (T_inO : In@{u a i} O T) (f : T -> U) (feq : IsEquiv f),
        In@{u a j} O U.
  Proof.
    intros [O|O]; [ exact (Os1.inO_equiv_inO@{u a i j k} O)
                  | exact (Os2.inO_equiv_inO@{u a i j k} O) ].
  Defined.

  Definition hprop_inO
  : Funext -> forall (O : Modality@{u a}) (T : Type@{i}),
                IsHProp (In@{u a i} O T).
  Proof.
    intros ? [O|O]; [ exact (Os1.hprop_inO@{u a i} _ O)
                    | exact (Os2.hprop_inO@{u a i} _ O) ].
  Defined.

  Definition O_ind_internal
  : forall (O : Modality@{u a})
           (A : Type2le@{i a}) (B : O_reflector O A -> Type2le@{j a})
           (B_inO : forall oa, In@{u a j} O (B oa)),
      (forall a, B (to O A a)) -> forall a, B a.
  Proof.
    intros [O|O]; [ exact (Os1.O_ind_internal@{u a i j k} O)
                  | exact (Os2.O_ind_internal@{u a i j k} O) ].
  Defined.

  Definition O_ind_beta_internal
  : forall (O : Modality@{u a})
           (A : Type@{i}) (B : O_reflector O A -> Type@{j})
           (B_inO : forall oa, In@{u a j} O (B oa))
           (f : forall a : A, B (to O A a)) (a:A),
      O_ind_internal@{u a i j k} O A B B_inO f (to O A a) = f a.
  Proof.
    intros [O|O]; [ exact (Os1.O_ind_beta_internal@{u a i j k} O)
                  | exact (Os2.O_ind_beta_internal@{u a i j k} O) ].
  Defined.

  Definition minO_paths
  : forall (O : Modality@{u a})
           (A : Type2le@{i a}) (A_inO : In@{u a i} O A) (z z' : A),
      In@{u a i} O (z = z').
  Proof.
    intros [O|O]; [ exact (Os1.minO_paths@{u a i} O)
                  | exact (Os2.minO_paths@{u a i} O) ].
  Defined.

  Definition IsSepFor@{u a}
    : forall (O' O : Modality@{u a}), Type@{u}.
  Proof.
    intros [O'|O'] [O|O];
      [ exact (@Os1.IsSepFor@{u a} O' O)
      | exact Empty
      | exact Empty
      | exact (@Os2.IsSepFor@{u a} O' O) ].
  Defined.

  Definition inO_paths_from_inSepO@{u a i iplus}
    : forall (O' O : Modality@{u a}) (sep : IsSepFor O' O)
             (A : Type@{i}) (A_inO : In@{u a i} O' A) (x y : A),
      In@{u a i} O (x = y).
  Proof.
    intros [O'|O'] [O|O];
      [ exact (@Os1.inO_paths_from_inSepO@{u a i iplus} O' O)
      | contradiction
      | contradiction
      | exact (@Os2.inO_paths_from_inSepO@{u a i iplus} O' O) ].
  Defined.

  Definition inSepO_from_inO_paths@{u a i iplus}
    : forall (O' O : Modality@{u a}) (sep : IsSepFor O' O)
             (A : Type@{i}),
      (forall (x y : A), In@{u a i} O (x = y)) -> In@{u a i} O' A.
  Proof.
    intros [O'|O'] [O|O];
      [ exact (@Os1.inSepO_from_inO_paths@{u a i iplus} O' O)
      | contradiction
      | contradiction
      | exact (@Os2.inSepO_from_inO_paths@{u a i iplus} O' O) ].
  Defined.

End Modalities_FamUnion.

(** For examples of modalities, see the files Notnot, Identity, Nullification, PropositionalFracture, and Localization. *)
