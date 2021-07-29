Inductive Decision : Set :=
  | Cooperate
  | Defect
.

Inductive Maybe A :=
  | Nothing : Maybe A
  | Just : A -> Maybe A
.
Arguments Nothing {A}.
Arguments Just {A}.

Unset Positivity Checking.
Inductive Agent : Type :=
  {ag_dec : (Agent -> Decision)}
.

Set Positivity Checking.

Definition ProofSearch {A : Type} (P: A -> Type) := 
  forall (a : A), Maybe (P a)
.

Definition CooperationSearch := 
  forall (self : Agent), 
    ProofSearch (
      fun other => 
        ag_dec other self = Cooperate
    )
.

Unset Guard Checking.
Fixpoint FairBotAlgo
  (search : CooperationSearch) 
  (other : Agent) {struct other} : Decision  
  :=
    match search (Build_Agent (FairBotAlgo search)) other with
    | Just _ => Cooperate
    | Nothing => Defect
    end
  .
Set Guard Checking.


Definition FairBot search := 
  Build_Agent (FairBotAlgo search).

