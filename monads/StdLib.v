Module StandardLib.

Definition comp {A B C} (f: B -> C) (g: A -> B) := fun x => f (g x).
Definition id {A:Type} : A -> A := fun a => a.

Definition curry {A B C} : (A -> B -> C) -> (A * B) -> C :=
  fun f '(a, b) => f a b.
Definition uncurry {A B C} : (A * B -> C) -> A -> B -> C :=
  fun f a b => f (a, b).

Definition fun_eq {A B} (f g: A -> B) := forall a, f a = g a.

Notation "f \o g" := (comp f g)
  (at level 50, left associativity).

Notation "f =1 g" := (fun_eq f g) (at level 50).

End StandardLib.

Module StandardCat.
Import StandardLib.

Definition iso {A B} (f: A -> B) :=
  exists g, f \o g =1 id /\ exists h, h \o f =1 id.

Definition eiso A B := exists f, @iso A B f.

End StandardCat.