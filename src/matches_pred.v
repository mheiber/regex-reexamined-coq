Require Import List.
Import ListNotations.

Require Import comparable.
Require Import derive_def.
Require Import regex.

Reserved Notation "xs =~ r" (at level 80).

Inductive matches_prop {A: Type} {cmp: comparable A} : regex A -> (list A) ->  Prop :=
  | empty_matches :
    [] =~ empty

  | char_matches (a : A):
    [a] =~ char a

  | or_matches_l (r s : regex A) (xs : list A):
    xs =~ r ->
    (* --------- *)
    xs =~ or r s

  | or_matches_r (r s : regex A) (xs : list A):
    xs =~ s ->
    (* --------- *)
    xs =~ or r s

  | and_matches (r s : regex A) (xs: list A) :
    xs =~ r ->
    xs =~ s ->
    (* --------- *)
    xs =~ and r s

  | concat_matches (r s : regex A) (xs ys: list A) :
    xs =~ r ->
    ys =~ s ->
    (* --------- *)
    (xs ++ ys) =~ concat r s

  (* | not_matches (r : regex A) (xs : list A):
    TODO: Help Wanted
  *)

  | star_matches_nil (r : regex A):
    [] =~ star r

  | star_matches_concat (r : regex A) (xs ys : list A):
    xs =~ r ->
    ys =~ star r ->
    (* --------- *)
    (xs ++ ys) =~ star r

  where "xs =~ r" := (matches_prop r xs).

Theorem matches_prop_describes_matches_impl: 
  forall
    {A: Type}
    {cmp: comparable A}
    (r: regex A) 
    (xs: list A), 
  matchesb r xs = true <-> matches_prop r xs
.
(* TODO: Help Wanted 
   If this theorem is proved,
   then matches_prop can be used in proofs,
   rather than induction on xs and matchesb.
*)
Abort.