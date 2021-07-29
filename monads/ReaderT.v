Require Import StdLib.
Import StandardLib StandardCat.

Module ReaderT.
Open Scope type_scope.

Section Classes.

Generalizable Variables F.

Class Functor (F : Type -> Type) :=
  { fmap {A B} : (A -> B) -> F A -> F B
  
  ; functor_id_law {A} : fmap id = @id (F A)
  ; functor_comp_law {A B C} : 
      forall (f: B -> C) (g : A -> B), 
        fmap (f \o g) = fmap f \o fmap g
  }
.

Notation "()" := True.

Class Monoidal `(Functor F) :=
  { unit : F ()
  ; joinA {A B} : F A -> F B -> F (A * B)
  ; is_monoidal {A B} : iso (curry (@joinA A B))
  (* ; lambda {A} : eiso (F A) (F (A * ())) *)
  ; lambda {A} :
      iso (fun fa => @fmap F _ _ A fst (joinA fa unit))
  ; rho {A} : iso (
      fun fa => @fmap F _ _ A snd (joinA unit fa)
    )
  }
.

Class Applicative `(Functor F) (F : Type -> Type) :=
  { pure {A} : F A
  ; ap {A B} : F (A -> B) -> F A -> F B (* <*> *)
  
  ; 
  }
.

Notation "a <*> b" := (ap a b) 
  (at level 50, left associativity).

End Classes.

End ReaderT.