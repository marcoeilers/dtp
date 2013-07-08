(*
 * Two proofs that complement the equivalence proof 
 * in Agda.
 *)

(* Some basic definitions and functions on booleans, nats and lists *)
Require Export Misc.
Require Import List.

Theorem filterConjunction : forall (A : Type) (b : list A) (p1 p2 p3 : A -> bool),
  filter p1 (filter p2 (filter p3 b)) = filter (fun x => andb (p3 x) (andb (p2 x) (p1 x))) b.
Proof with simpl.
  intros A b p1 p2 p3.
  induction b as [ | b' bs]...
  * reflexivity.
  * destruct (p3 b')...
    destruct (p2 b')...
    destruct (p1 b')...
      rewrite IHbs. 
      reflexivity.
      apply IHbs.
      apply IHbs.
      apply IHbs.
Qed.

Theorem filterSwap : forall (A : Type) (b : list A) (p1 p2 : A -> bool),
  filter p1 (filter p2 b) = filter p2 (filter p1 b).
Proof.
  intros A b p1 p2.
  induction b as [ | b' bs].
  * reflexivity.
  * simpl. 
    remember (p2 b') as p2b.
    remember (p1 b') as p1b. 
    destruct p2b. simpl.
    rewrite <- Heqp1b.
    destruct p1b. simpl.
    rewrite <- Heqp2b.
    rewrite IHbs.
    reflexivity.
    apply IHbs.
    destruct p1b.
    simpl.
    rewrite <- Heqp2b.
    apply IHbs.
    apply IHbs.
Qed.
