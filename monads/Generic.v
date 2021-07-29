Require Import StdLib.
Import StandardLib.

Open Scope type_scope.
Module EvenMoreGenerally.

(* We'll do enriched categories later, ok *)
(* Class Category (U:Type) (A : U) (arr : A -> A -> U) := *)
Class Category (A : Type) (arr : A -> A -> Type) :=
  { cat_id : forall {a}, arr a a
  ; cat_comp : forall {a b c}, arr b c -> arr a b -> arr a c
  (* Ha ha! No =1 for us! 'cause arbitrary arrows are not functions. *)
  (* And to get Instance Category Type without fun_ext *)
  (* we'll need to weaken it to setoids, right? *)
  (* Ok, let's do that slightly later. *)
  ; cat_id_left {a b} (f : arr a b) : cat_comp cat_id f = f
  ; cat_id_right {a b} (f : arr a b) : cat_comp f cat_id = f
  ; cat_assoc :
      forall {a b c d} (f : arr c d) (g : arr b c) (h : arr a b),
      cat_comp (cat_comp f g) h = cat_comp f (cat_comp g h)
  }
.

(* Notation "a ~> b" := (arr a b) (at level 50). *)
Notation "f \o g" := (cat_comp f g)
  (at level 50, left associativity).

Generalizable Variables C arrc D arrd.

(* Section Functors. *)

Class Functor {C D arrc arrd}
  `(Category C arrc) `(Category D arrd)
  (F : C -> D) :=
  { fmap {x y} : arrc x y -> arrd (F x) (F y)
  ; functor_id_law {x} : @fmap x _ cat_id = cat_id
  ; functor_comp_law {x y z} :
      forall (f: arrc y z) (g : arrc x y),
        fmap (f \o g) = fmap f \o fmap g

  }
.

Definition prod_arrow {C D}
  (arrc : C -> C -> Type) (arrd : D -> D -> Type) :
    (C * D) -> (C * D) -> Type
:= fun '(c, c') '(d, d') => arrc c d * arrd c' d'.

(* Definition pair_arrow {C D}
  {arrc : C -> C -> Type} {arrd : D -> D -> Type}
  c c' d d' (f : arrc c c') (g : arrd d d')
    : prod_arrow arrc arrd (c, d) (c', d')
:= (f, g).
*)


#[refine] Instance cat_product `(Category C arrc) `(Category D arrd) :
    Category (C * D) (prod_arrow arrc arrd) :=
  { cat_id := fun '(_, _) => (cat_id, cat_id) }
.
Proof.
  (* all: unfold prod_arrow. *)
  (* { intros. destruct a as [c d]. constructor; exact cat_id. } *)
  (* cat_comp *)
  { intros [a a'] [b b'] [c c'] [f f'] [g g']. constructor.
    exact (cat_comp f g).
    exact (cat_comp f' g').
  }
  1, 2: intros [a a'] [b b'] [f f'].
  { rewrite 2 cat_id_left. reflexivity. }
  { rewrite 2 cat_id_right. reflexivity. }
  { intros [a a'] [b b'] [c c'] [d d'] [f f'] [g g'] [h h'].
    rewrite 2 cat_assoc. reflexivity.
  }
Defined.

(* End Functors. *)

Notation "c × d" := (cat_product c d)
  (at level 50, left associativity).

Generalizable Variables E arre.

Section Bifunctors.

Variables
  (C D E : Type)
  (F : C * D -> E)
  (arrc: _)
  (arrd: _)
  (arre: _)
  (catc : Category C arrc)
  (catd : Category D arrd)
  (cate : Category E arre)
  .

(* Definition Bifunctor  :=
  Functor (cat_product catc catd) cate. *)

#[refine] Instance fix_left
  (B: Functor (catc × catd) cate F) :
    forall c:C, Functor catd cate (fun d => F (c, d)) := {}.
  { intros x y f. simpl. apply fmap.
    exact (cat_id, f).
  }
  all: simpl.
  { intro d. rewrite <- functor_id_law. reflexivity. }
  { intros x y z f g.
    rewrite <- functor_comp_law; simpl.
    rewrite cat_id_left. reflexivity.
  }
Defined.

#[refine] Instance fix_right
  (B: Functor (catc × catd) cate F) :
    forall d:D, Functor catc cate (fun c => F (c, d)) := {}.
  { intros x y f. simpl. apply fmap.
    exact (f, cat_id).
  }
  all: simpl.
  { intro c. rewrite <- functor_id_law. reflexivity. }
  { intros x y z f g.
    rewrite <- functor_comp_law; simpl.
    rewrite cat_id_left. reflexivity.
  }
Defined.

End Bifunctors.

(* Import StandardCat. *)
(* nnnnope, we'll need category-aware morphisms! *)

Class NatTrans {C arrc D arrd F G}
  {catc : Category C arrc} {catd : Category D arrd}
    (Func : Functor catc catd F)
    (Gunc : Functor catc catd G)
  :=
  { component x : arrd (F x) (G x)
  ; diagram {x y} f : component y \o fmap f = fmap f \o component x
  }
.

Generalizable Variables Func Gunc.

Definition is_iso `{Category C arrc} {x y} (f : arrc x y) :=
  exists g, f \o g = cat_id /\ exists h, h \o f = cat_id.

Definition ex_iso `{Category C arrc} x y :=
  exists (f: arrc x y), is_iso f.

Definition are_iso `{Category C arrc} {x y}
  (f : arrc x y) (g: arrc y x) :=
    f \o g = cat_id /\ g \o f = cat_id.

Record Iso `{Category C arrc} x y :=
  { left : arrc x y
  ; right : arrc y x
  ; iso_law_left : left \o right = cat_id
  ; iso_law_right : right \o left = cat_id
  }
.
(* Definition unwrap `{Category C arrc} {x y} : ex_iso x y -> arrc x y. *)

Class NatIso {C arrc D arrd F G}
  {catc : Category C arrc} {catd : Category D arrd}
  (Func : Functor catc catd F)
  (Gunc : Functor catc catd G) :=
  { iso_component x : Iso (F x) (G x)
  ; diagram_left {x y} (f : arrc x y) :
      @left _ _ _ _ _ (iso_component y) \o fmap f
      = fmap f \o @left _ _ _ _ _ (iso_component x)
  ; diagram_right {x y} f :
      @right _ _ _ _ _ (iso_component y) \o fmap f
      = fmap f \o @right _ _ _ _ _ (iso_component x)
  }
.

#[refine] Instance Id :
  forall (cat : Category C arrc),
    Functor cat cat id := { fmap x y := id }.
Proof. all: trivial. Defined.

Arguments fix_left {C D E F arrc arrd arre catc catd cate}.
Arguments fix_right {C D E F arrc arrd arre catc catd cate}.

(* Generalizable Variables E arre F G. *)

#[refine] Instance Comp {C D E arrc arrd arre F G}
  {catc : Category C arrc}
  {catd : Category D arrd}
  {cate : Category E arre}
  (Func : Functor catc catd F)
  (Gunc : Functor catd cate G) :
    Functor catc cate (fun c => G (F c))
    := { }.
Proof.
  { intros x y f. exact (fmap (fmap f)). }
  all: simpl.
  { intro x. eapply eq_trans.
    rewrite functor_id_law. reflexivity.
    exact functor_id_law.
  }
  { intros x y z f g.
    rewrite functor_comp_law. apply functor_comp_law.
  }
Defined.

Notation "G ° F" := (Comp G F) (at level 50).

#[refine] Instance functor_prod {A B C D arra arrb arrc arrd F G}
  {cata : Category A arra}
  {catb : Category B arrb}
  {catc : Category C arrc}
  {catd : Category D arrd}
  (Func : Functor cata catc F)
  (Gunc : Functor catb catd G) :
    Functor (cata × catb) (catc × catd)
      (fun '(a, b) => (F a, G b)) := {}.
Proof.
  { intros [a b] [a' b'] [f f']. exact (fmap f, fmap f'). }
  { intros [a b]. simpl. rewrite 2 functor_id_law. reflexivity. }
  { intros [xa xb] [ya yb] [za zb] [fa fb] [ga gb]. simpl.
    rewrite 2 functor_comp_law. reflexivity.
  }
Defined.

Notation "G ⋅ F" := (functor_prod G F) (at level 50).
(*
#[refine] Instance AB_D {A B C D E arra arrb arrc arrd arre F G}
  (cata : Category A arra)
  (catb : Category B arrb)
  (catc : Category C arrc)
  (catd : Category D arrd)
  (cate : Category E arre)
  (Func : Functor (cata × catb) catc F)
  (Gunc : Functor (catc × catd) cate G) :
    Functor ((cata × catb) × catd) cate
      (* (fun '(ab, d) => G (F ab, d)) := *)
      (* for some reason Coq fails to unify those. w/e. *)
      _ :=
      (Func ⋅ Id catd) ° Gunc. *)

(* #[refine] Instance C_DE *)

Record IsoFunctor {C arrc D arrd F G}
  {catc : Category C arrc}
  {catd : Category D arrd}
  (Func : Functor catc catd F)
  (Gunc : Functor catd catc G) :=
  { left_iso : NatIso (Func ° Gunc) (Id _)
  ; right_iso : NatIso (Gunc ° Func) (Id _)
  }
.

#[refine] Instance SwapR _ :
  Functor ((C × D) × E) (C × (D × E)) := {}.
(* #[refine] Instance SwapL _ :
  Functor (C × (D × E)) ((C × D) × E) := {}.

Definition Swap C D E :
  IsoFunctor (SwapL C D E) (SwapR C D E). *)


Class MonoidalCat {C arrc F} (cat : Category C arrc) (I : C)
  (cross : Functor (cat × cat) cat F)
  :=
  { lambda x : NatIso (fix_left cross I) (Id cat)
  ; rho    x : NatIso (fix_right cross I) (Id cat)
  ; alpha x y z : let F := uncurry F in
      NatIso ((cross ⋅ Id cat) ° cross) (SwapR ° (Id cat ⋅ cross) ° cross)
  (* ; triangle x y :
  ; pentagon : *)
  }
.

Section Instances.

Definition type_arr A B := A -> B.

Hypothesis fun_ext :
  forall {A B} (f g : A -> B),
    (forall x, f x = g x) -> f = g.

#[refine] Instance type_is_category : Category Type type_arr :=
  { cat_id := @id
  ; cat_comp := @comp
  }
.
Proof. 1,2: intros; apply fun_ext. all: trivial. Defined.

End Instances.

End EvenMoreGenerally.