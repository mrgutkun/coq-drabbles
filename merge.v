From Coq Require Import Lists.List.
From Coq Require Program.
From Coq Require Import Psatz.
From Coq Require Import Arith.PeanoNat.

Check Nat.leb.
Check length _.

Program Fixpoint merge (xs ys: list nat) {measure (length xs + length ys)} : list nat :=
    match xs, ys with
        | xs, nil => xs
        | nil, ys => ys
        | (cons x xs'), (cons y ys') =>
            if Nat.leb x y 
            then x :: merge xs' ys
            else y :: merge xs ys'
    end.
Next Obligation.
    simpl. lia.
Qed.

Inductive Sorted : list nat -> Prop :=
    | nilSorted : Sorted nil
    | singlSorted {n} : Sorted (cons n nil)
    | indSorted {n m : nat} {rest : list nat} : 
        Sorted (cons m rest) -> n <= m -> Sorted (cons n (cons m rest))
.

Lemma div2_le: forall n m, n <= m -> Nat.div2 n <= Nat.div2 m.
Proof. Admitted.


(* Require Import Recdef.

Function mergesort (ns : list nat) {measure length ns} : list nat :=
    match ns with
        | nil => nil
        | cons n nil => cons n nil
        | ns => let half_l := Nat.div2 (length ns) in
                    merge (mergesort (firstn half_l ns)) (mergesort (skipn half_l ns))
    end
.

Proof.
{
    intros.
    assert (2 <= length ns). {
        destruct ns. inversion teq.
        destruct ns. inversion teq.
        simpl. lia.
    }
    assert (1 <= Nat.div2 (length ns)) by exact (div2_le _ _ H).
    rewrite skipn_length. subst ns. lia.
}
{   
    intros.
    destruct ns. inversion teq.
    
    assert (Nat.div2 (length (n1 :: ns)) < length (n1 :: ns)).
        apply Nat.lt_div2. simpl. lia.
    rewrite firstn_length_le.
    all: inversion teq; subst n ns; lia.
}
Qed.

Check mergesort_ind. *)

Program Fixpoint mergesort (ns : list nat) {measure (length ns)} : list nat :=
    match ns with
        | nil => nil
        | cons n nil => cons n nil
        | ns => let half_l := Nat.div2 (length ns) in
                    merge (mergesort (firstn half_l ns)) (mergesort (skipn half_l ns))
    end
.
Next Obligation.
    destruct ns0. contradiction. clear H. 
    assert (Nat.div2 (length (n :: ns0)) < length (n :: ns0)).
        apply Nat.lt_div2. simpl. lia.
    rewrite firstn_length_le.
    all: lia.
Qed.


Next Obligation.
    assert (2 <= length ns0). {
        destruct ns0. contradiction.
        destruct ns0. contradiction (H n). trivial.
        simpl. lia.
    }
    assert (1 <= Nat.div2 (length ns0)) by exact (div2_le _ _ H1).
    (* destruct ns0. contradiction. *)

    rewrite skipn_length. lia.
Qed.
Next Obligation.
    split. intros. intro. inversion H3.
    intro. inversion H3.
Qed.
Check mergesort.

Lemma merge_preserves_sort :
    forall xs ys, Sorted xs -> Sorted ys -> Sorted (merge xs ys).
Admitted.

Program Theorem mergesort_sorts : 
    forall ns : list nat, Sorted (mergesort ns).
Proof.
    intro. destruct ns.
    { constructor. }
    destruct ns.
    { cbv. constructor. }
    replace (mergesort (n :: n0 :: ns)) with 
        (merge 
            (mergesort (firstn (Nat.div2 (length (n :: n0 :: ns))) (n :: n0 :: ns))) 
            (mergesort (skipn (Nat.div2 (length (n :: n0 :: ns))) (n :: n0 :: ns)))).
    eapply merge_preserves_sort. admit. admit.
    

    

Qed.

Theorem merge_preserves_elements : 
    forall (ns: list nat) (n: nat), 
        (count_occ eq_nat_dec ns n) = (count_occ eq_nat_dec (mergesort ns) n).