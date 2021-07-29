Axiom J : forall T : Type,
    forall (P : forall (x y : T), forall (p: x = y), Type), 
      (forall x, P x x eq_refl) -> 
        forall (x y : T), forall (p: x = y), P x y p.

Variable T : Type.

Theorem UIP: forall (x y : T), forall (p q : x = y), p = q.
Proof.
  (* Check (fun (x y : T), (p : x = y), fun ) *)
  eenough (H:_).
  exact (J T (fun x y p => (forall (q:x=y), p = q)) H).
  simpl.
  Abort.
