
Check eq_rect.

Variable A : Type.
Variable P : A -> Type.

Definition transp {x y : A} (p: x = y) (px : P x) : P y :=
  eq_rect _ _ px _ p.

Lemma lift (x y:A) (u : P x) (p : x = y) : 
  existT P x u = existT P y (transp p u).
  subst. reflexivity.
Defined.

Lemma apd (x y : A) (f : forall x, P x) (p : x = y) : 
  (transp p (f x)) = f y.
  subst. reflexivity.
Defined.

Lemma dep_eq x y (f : forall x, P x) (p : x = y) : 
  existT P x (f x) = existT P y (f y).
  subst. reflexivity.

  (* eapply eq_trans. apply (lift _ _ _ p).
  rewrite apd. reflexivity. *)
Defined.


Lemma Contractible_eq_bool : 
  (forall (b: bool) (q : b = b), eq_refl = q).
intro b; case b. 
all: exact (fun q => 
  match q 
  with eq_refl => eq_refl end
).
Qed.

Print Contractible_eq_bool.

Lemma IsProp_bool : forall (b: bool) (p q: b = b), p = q.
intros b p; case p. apply Contractible_eq_bool. 
Qed.

Definition IsContr (A : Prop) :=
  exists (a:A), forall b, a = b.

Definition IsProp (A : Prop) :=
  forall (a b : A), a = b.

Definition IsSet (A : Type) :=
  forall a b : A, IsProp (a = b).

Definition Dec_Eq (A : Type) :=
  forall a b : A, {a = b} + {a <> b}.

(* Theorem smth {A}: IsSet A -> Dec_Eq A.
intros H a b. Check (H a b). *)

Theorem contr_list : forall A, IsSet A -> IsSet (list A).
  unfold IsSet, IsProp. intros A setA la. elim la.
  { intros b p. case p. exact (fun q => match q with eq_refl => eq_refl end).
  }
  { clear la; intros a la H lb p. case p.
      exact (fun q => 
        match q as q' in (_ = lb')
        return (
          ( match lb' as lb'' 
            return ((a :: la)%list = lb'' -> Type)
            with
            | (a' :: la')%list => 
              (* we want to somehow convert a into a' and la into la'
              , but how *)
              fun (q'' : _) => eq_refl = q''
            | _ => fun _ => IDProp
            end
          ) q')
        with eq_refl => eq_refl 
        end
      ).
      - intros c. inversion c.
    - clear lb; intros b lb p. case p.
      exact (fun q => match q with eq_refl => _ end).


  }