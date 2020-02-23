Require Import List.

Section Regexes.

(* A character for a regular expression is generic,
   but it needs to implement an interface.
   It needs to be comparable.
*)

Variable X: Set.
Parameter compare : X -> X -> comparison.
Parameter proof_compare_equal: forall (x y: X) (p: compare x y = Eq),
  x = y.
Parameter proof_compare_reflex: forall (x: X), compare x x = Eq.
Parameter proof_compare_if_equal: forall (x1 x2: X) (c: compare x1 x2 = compare x2 x1), x1 = x2.

Definition is_eq (x y: X) : bool :=
  match compare x y with
  | Eq => true
  | _ => false
  end.

Inductive regex :=
  nothing : regex (* matches no strings *)
  | empty : regex (* matches the empty string *)
  | char : X -> regex (* matches a single character *)
  | or : regex -> regex -> regex
  | and : regex -> regex -> regex
  | concat : regex -> regex -> regex
  | not : regex -> regex
  | zero_or_more : regex -> regex
  .

Fixpoint compare_regex (r s: regex) : comparison :=
  match r with
  | nothing => match s with
    | nothing => Eq
    | _ => Lt
    end
  | empty => match s with
    | nothing => Gt
    | empty => Eq
    | _ => Lt
    end
  | char x => match s with
    | nothing => Gt
    | empty => Gt
    | char y => compare x y
    | _ => Lt
    end
  | or r1 r2 => match s with
    | nothing => Gt
    | empty => Gt
    | char _ => Gt
    | or s1 s2 =>
      match compare_regex r1 s1 with
      | Lt => Lt
      | Eq => compare_regex r2 s2
      | Gt => Gt
      end
    | _ => Lt
    end
  | and r1 r2 => match s with
    | nothing => Gt
    | empty => Gt
    | char _ => Gt
    | or _ _ => Gt
    | and s1 s2 =>
      match compare_regex r1 s1 with
      | Lt => Lt
      | Eq => compare_regex r2 s2
      | Gt => Gt
      end
    | _ => Lt
    end
  | concat r1 r2 => match s with
    | nothing => Gt
    | empty => Gt
    | char _ => Gt
    | or _ _ => Gt
    | and _ _ => Gt
    | concat s1 s2 =>
      match compare_regex r1 s1 with
      | Lt => Lt
      | Eq => compare_regex r2 s2
      | Gt => Gt
      end
    | _ => Lt
    end
  | not r1 => match s with
    | nothing => Gt
    | empty => Gt
    | char _ => Gt
    | or _ _ => Gt
    | and _ _ => Gt
    | concat _ _ => Gt
    | not s1 => compare_regex r1 s1
    | _ => Lt
    end
  | zero_or_more r1 => match s with
    | zero_or_more s1 => compare_regex r1 s1
    | _ => Gt
    end
  end.

Theorem compare_equal : forall (r1 r2: regex) (p: compare_regex r1 r2 = Eq),
  r1 = r2.
Proof.
induction r1.
 - induction r2; simpl; trivial; discriminate. (* nothing *)
 - induction r2; simpl; trivial; discriminate. (* empty *) 
 - induction r2; simpl; try discriminate. (* char *)
  + remember (compare x x0).
    induction c; simpl; try discriminate.
    * symmetry in Heqc.
      apply proof_compare_equal in Heqc.
      rewrite <- Heqc.
      reflexivity.
 - induction r2; simpl; try discriminate. (* or *)
  + remember (compare_regex r1_1 r2_1).
    remember (compare_regex r1_2 r2_2).
    induction c; try discriminate.
    * induction c0; try discriminate.
      -- symmetry in Heqc.
         symmetry in Heqc0.
         remember (IHr1_1 r2_1).
         remember (e Heqc).
         rewrite e.
         remember (IHr1_2 r2_2).
         remember (e1 Heqc0).
         rewrite e2.
         reflexivity.
         apply Heqc.
 - induction r2; simpl; try discriminate. (* and *)
  + remember (compare_regex r1_1 r2_1).
    remember (compare_regex r1_2 r2_2).
    induction c; try discriminate.
    * induction c0; try discriminate.
      -- symmetry in Heqc.
         symmetry in Heqc0.
         remember (IHr1_1 r2_1).
         remember (e Heqc).
         rewrite e.
         remember (IHr1_2 r2_2).
         remember (e1 Heqc0).
         rewrite e2.
         reflexivity.
         apply Heqc.
 - induction r2; simpl; try discriminate. (* concat *)
  + remember (compare_regex r1_1 r2_1).
    remember (compare_regex r1_2 r2_2).
    induction c; try discriminate.
    * induction c0; try discriminate.
      -- symmetry in Heqc.
         symmetry in Heqc0.
         remember (IHr1_1 r2_1).
         remember (e Heqc).
         rewrite e.
         remember (IHr1_2 r2_2).
         remember (e1 Heqc0).
         rewrite e2.
         reflexivity.
         apply Heqc.
 - induction r2; simpl; try discriminate. (* not *)
  + remember (IHr1 r2).
    remember (IHr1 (not r2)).
    intros.
    remember (e p).
    rewrite e1.
    reflexivity.
 - induction r2; simpl; try discriminate. (* zero_or_more *)
  + remember (IHr1 r2).
    remember (IHr1 (zero_or_more r2)).
    intros.
    remember (e p).
    rewrite e1.
    reflexivity.
Qed.

Theorem compare_reflex : forall (r: regex), 
 compare_regex r r = Eq.
Proof.
induction r; try reflexivity; simpl.
- apply proof_compare_reflex.
- rewrite IHr1. rewrite IHr2. reflexivity.
- rewrite IHr1. rewrite IHr2. reflexivity.
- rewrite IHr1. rewrite IHr2. reflexivity.
- rewrite IHr. reflexivity.
- rewrite IHr. reflexivity.
Qed.

Theorem compare_is_equal : forall (r1 r2: regex)
  (c: compare_regex r1 r2 = compare_regex r2 r1),
  r1 = r2.
induction r1, r2; try reflexivity; try discriminate.
- remember (compare_regex (char x) (char x0)) as ccharxx0.
  induction ccharxx0.
  + symmetry in Heqccharxx0.
    simpl in Heqccharxx0.
    apply (proof_compare_equal x x0) in Heqccharxx0.
    rewrite Heqccharxx0.
    simpl.
    rewrite proof_compare_reflex.
    trivial.
  + simpl in Heqccharxx0.
    simpl.
    rewrite Heqccharxx0.
    rewrite (proof_compare_if_equal x x0).
    * rewrite proof_compare_reflex.
      trivial.
    * apply proof_compare_equal_only_if.
    


Lemma compare_regex_gt_lt:
 forall (r1 r2: regex)
 (c: compare_regex r1 r2 = Gt),
 compare_regex r2 r1 = Lt.
Proof.
intros.
induction r2, r1; simpl; try discriminate; try trivial.
- simpl in c.
  apply proof_compare_gt_lt.
  apply c.
- remember (compare_regex r2_1 r1_1).
  induction c0.
  + remember (compare_regex r2_2 r1_2) as c1.
    symmetry in Heqc0.
    apply compare_equal in Heqc0.
    induction c1.
    * symmetry in Heqc1.
      apply compare_equal in Heqc1.
      rewrite Heqc0 in c.
      rewrite Heqc1 in c.
      simpl in c.
      rewrite (compare_reflex r1_1) in c.
      rewrite (compare_reflex r1_2) in c.
      discriminate.
    * reflexivity.
    * rewrite Heqc0 in c.
      simpl in c.
      rewrite (compare_reflex r1_1) in c.
      symmetry in Heqc1.
      rewrite <- Heqc1 in c.
      rewrite <- c.

(* nullable returns whether the regular expression matches the
   empty string, for example:
   nullable (ab)*        = true
   nullable a(ab)*       = false
   nullable a            = false
   nullable (abc)*|ab    = true
   nullable a(abc)*|ab   = false
*)
Fixpoint nullable (r: regex) : bool :=
  match r with
  | nothing => false
  | empty => true
  | char _ => false
  | or s t => nullable s || nullable t
  | and s t => nullable s && nullable t
  | concat s t => nullable s && nullable t
  | not s => negb (nullable s)
  | zero_or_more _ => true
  end.

(* derive returns the regular expression that is left to match
   after matching the input character x, for example:
   derive (ba)*      b    = a(ba)*
   derive a          a    = empty
   derive b          a    = nothing
   derive ab|a       a    = b|empty
   derive bc         b    = c
   derive (a|empty)b a    = b
   derive (a|empty)b b    = empty
   derive empty b    b    = empty
*)
Fixpoint derive (r: regex) (x: X) : regex :=
  match r with
  | nothing => nothing
  | empty => nothing
  | char y => if is_eq x y
    then empty
    else nothing
  | or s t => or (derive s x) (derive t x)
  | and s t => and (derive s x) (derive t x)
  | concat s t =>
    if nullable s
    then or (concat (derive s x) t) (derive t x)
    else concat (derive s x) t
  | not s => not (derive s x)
  | zero_or_more s => concat (derive s x) (zero_or_more s)
  end.

Definition matches (r: regex) (xs: list X) : bool :=
  nullable (fold_left derive xs r)
.

(* simple is the property that says whether the regex is simplified *)
Fixpoint simple (r: regex) : Prop :=
 match r with
 | nothing => True
 | empty => True
 | char _ => True
 | or s t => simple s /\ simple t /\ compare_regex s t = Lt
 | and s t => simple s /\ simple t
 | concat s t => simple s /\ simple t
 | not s => simple s
 | zero_or_more s => simple s
 end.

(* sderive is the same as derive, except that it applies
   simplification rules by construction.
   This way we don't have to apply simplification after derivation.
   We hope this will also make it easier to prove things.
*)
(* TODO add associativity *)
Definition smart_or (r s: regex) : regex :=
  match compare_regex r s with
  | Eq => s
  | Lt => or r s
  | Gt => or s r
  end.

Fixpoint sderive (r: regex) (x: X) : regex :=
  match r with
  | nothing => nothing
  | empty => nothing
  | char y => if is_eq x y
    then empty
    else nothing
  | or s t => smart_or (sderive s x) (sderive t x)
  | and s t => and (sderive s x) (sderive t x)
  | concat s t =>
    if nullable s
    then smart_or (concat (sderive s x) t) (sderive t x)
    else concat (sderive s x) t
  | not s => not (sderive s x)
  | zero_or_more s => concat (sderive s x) (zero_or_more s)
  end.

Lemma sderive_simple_or:
 forall (r1 r2: regex) (x: X)
        (sor: simple (or r1 r2)) 
        (Hsr1: simple r1 -> simple (sderive r1 x))
        (Hsr2: simple r2 -> simple (sderive r2 x)),
        simple (smart_or (sderive r1 x) (sderive r2 x)).
Proof.
 intros.
 simpl in sor.
 destruct sor as [sr1 [sr2 clt]].
 remember (Hsr1 sr1) as sdr1.
 remember (Hsr2 sr2) as sdr2.
 unfold smart_or.
 remember (compare_regex (sderive r1 x) (sderive r2 x)) as c.
 induction c.
 - apply sdr2.
 - simpl.
   split.
   apply sdr1.
   split.
   apply sdr2.
   symmetry in Heqc.
   apply Heqc.
 - simpl.
   split.
   apply sdr2.
   split.
   apply sdr1.
   rewrite <- Heqc.
   symmetry in Heqc.
   rewrite <- Heqc.
Admitted.

Lemma sderive_simple_and:
 forall (r1 r2: regex) (x: X)
        (is_simple: simple (and r1 r2)) 
        (IHr1: simple r1 -> simple (sderive r1 x))
        (IHr2: simple r2 -> simple (sderive r2 x)),
        simple (and (sderive r1 x) (sderive r2 x)).
Proof.
 intros.
 simpl in is_simple.
 destruct is_simple as [sr1 sr2].
 remember (IHr1 sr1) as sdr1.
 remember (IHr2 sr2) as sdr2.
 split.
 apply sdr1.
 apply sdr2.
Qed.

Lemma sderive_simple_concat:
 forall (r1 r2: regex) (x: X)
        (is_simple: simple (and r1 r2)) 
        (IHr1: simple r1 -> simple (sderive r1 x))
        (IHr2: simple r2 -> simple (sderive r2 x)),
        simple
         (if nullable r1
           then or (concat (sderive r1 x) r2) (sderive r2 x)
           else concat (sderive r1 x) r2).
Proof.
 intros.
 simpl in is_simple.
 destruct is_simple as [sr1 sr2].
 remember (IHr1 sr1) as sdr1.
 remember (IHr2 sr2) as sdr2.
 remember (nullable r1) as n.
 induction (nullable r1); rewrite Heqn; simpl.
 - rewrite Heqn.
Qed.




Theorem sderive_is_closed_under_simple :
 forall (r: regex) (x: X) (is_simple: simple r),
 simple (sderive r x).
Proof.
 intros.
 induction r; simpl; try trivial.
 - remember (is_eq x x0).
   induction (is_eq x x0); rewrite Heqb; simpl; try trivial.
 - apply (sderive_simple_or r1 r2 x is_simple IHr1 IHr2).
 - apply (sderive_simple_and r1 r2 x is_simple IHr1 IHr2).
 - 
   
 
 

Definition smatches (r: regex) (xs: list X) : bool :=
  nullable (fold_left sderive xs r)
.
 

(*Using only or_comm, or_assoc and or_idemp 
  Brzozowski proved that a notion of RE similarity including only
  r + r = r
  r + s = s + r
  (r + s) + t = r + (s + t)
  is enough to ensure that every RE has only a finite number of dissimilar derivatives. 
  Hence, DFA construction is guaranteed to terminate if we use similarity as an approximation for equivalence
  see https://www.ccs.neu.edu/home/turon/re-deriv.pdf
  Regular-expression derivatives reexamined - Scott Owens, John Reppy, Aaron Turon
*)

(* r&r = r *)
Theorem and_idemp : forall (xs: list X) (r1 r2: regex) (p: compare_regex r1 r2 = Eq),
  matches (and r1 r2) xs = matches r1 xs.
Proof.
unfold matches.
induction xs.
- simpl.
  intros.
  rewrite (compare_equal r1 r2 p).
  apply Bool.andb_diag.
- simpl.
  intros.
  rewrite (compare_equal r1 r2 p).
  apply IHxs.
  apply compare_reflex.
Qed.

(* r&s = s&r *)
Theorem and_comm : forall (xs: list X) (r1 r2: regex),
  matches (and r1 r2) xs = matches (and r2 r1) xs.
Proof.
unfold matches.
induction xs.
- simpl.
  firstorder.
- simpl.
  intros.
  apply IHxs.
Qed.

(* (r&s)&t = r&(s&t) *)
Theorem and_assoc : forall (xs: list X) (r s t: regex),
    matches (and (and r s) t) xs = matches (and r (and s t)) xs.
Proof.
unfold matches.
induction xs.
- simpl.
  firstorder.
- simpl.
  intros.
  apply IHxs.
Qed.

(* nothing&r = nothing *)
Theorem and_nothing : forall (xs: list X) (r: regex),
  matches (and nothing r) xs = matches nothing xs.
Proof.
unfold matches.
induction xs.
- simpl.
  trivial.
- simpl.
  intros.
  apply IHxs.
Qed.

(* not(nothing)&r = r *)
Theorem and_not_nothing : forall (xs: list X) (r: regex),
    matches (and (not nothing) r) xs = matches r xs.
Proof.
unfold matches.
induction xs.
- simpl.
  trivial.
- simpl.
  intros.
  apply IHxs.
Qed.

(* TODO *)
(* (r.s).t = r.(s.t) *)
Theorem concat_assoc: forall (xs: list X) (r s t: regex),
  matches (concat (concat r s) t) xs = matches (concat r (concat s t)) xs.
Admitted.

(* nothing.r = nothing *)
Theorem concat_nothing : forall (xs: list X) (r: regex),
  matches (concat nothing r) xs = matches nothing xs.
Proof.
unfold matches.
induction xs.
- simpl.
  reflexivity.
- simpl.
  exact IHxs.
Qed.

Lemma fold_at_nothing : forall (xs : list X), (fold_left derive xs nothing = nothing).
Proof.
simpl.
intros.
induction xs.
- simpl.
  trivial.
- simpl.
  apply IHxs.
Qed.

Lemma nullable_fold : forall (xs : list X) (r s: regex), (nullable (fold_left derive xs (or r s))) = (orb (nullable (fold_left derive xs r)) (nullable (fold_left derive xs s))).
Proof.
induction xs.
- intros.
  simpl.
  reflexivity.
- intros.
  simpl.
  apply IHxs.
Qed.

(* r.nothing = nothing *)
Theorem concat_nothing2 : forall (xs: list X) (r: regex),
  matches (concat r nothing) xs = matches nothing xs.
Proof.
unfold matches.
induction xs.
- intros.
  simpl.
  apply Bool.andb_false_r.
- simpl.
  intros.
  remember (nullable r).
  destruct b.
  + rewrite nullable_fold.
    case (nullable(fold_left derive xs nothing)).
    * firstorder.
    * rewrite IHxs.
      rewrite fold_at_nothing.
      simpl.
      trivial.
  + apply IHxs.
Qed.

(* TODO *)
(* empty.r = r *)
Theorem concat_empty : forall (xs: list X) (r: regex),
  matches (concat empty r) xs = matches r xs.
Admitted.

(* TODO *)
(* r.empty = r *)
Theorem concat_empty2: forall (xs: list X) (r: regex),
  matches (concat r empty) xs = matches r xs.
Admitted.

(* r|r = r *)
Theorem or_idemp : forall (xs: list X) (r1 r2: regex) (p: compare_regex r1 r2 = Eq),
  matches (or r1 r2) xs = matches r1 xs.
Proof.
unfold matches.
induction xs.
- simpl.
  intros.
  rewrite (compare_equal r1 r2 p).
  induction (nullable r2); compute; reflexivity.
- simpl.
  intros.
  rewrite (compare_equal r1 r2 p).
  apply IHxs.
  apply compare_reflex.
Qed.

(* r|s = s|r *)
Theorem or_comm : forall (xs: list X) (r s: regex),
  matches (or r s) xs = matches (or s r) xs.
Proof.
unfold matches.
induction xs.
- simpl.
  firstorder.
- simpl.
  intros.
  apply IHxs.
Qed.

(* (r|s)|t = r|(s|t) *)
Theorem or_assoc : forall (xs: list X) (r s t: regex),
  matches (or r (or s t)) xs = matches (or (or r s) t) xs.
Proof.
unfold matches.
induction xs.
- simpl.
  intros.
  firstorder.
- intros.
  apply IHxs.
Qed.

(* TODO *)
(* not(nothing)|r = not(nothing) *)
Theorem or_not_nothing : forall (xs: list X) (r: regex),
  matches (or (not nothing) r) xs = matches (not nothing) xs.
Admitted.

(* nothing|r = r *)
Theorem or_id : forall (xs: list X) (r: regex),
  matches (or r nothing) xs = matches r xs.
Proof.
unfold matches.
induction xs.
- simpl.
  firstorder.
- intros.
  simpl.
  apply IHxs.
Qed.

(* TODO *)
(* zero_or_more(zero_or_more(r)) = zero_or_more(r) *)
Theorem zero_or_more_zero_or_more : forall (xs: list X) (r: regex),
  matches (zero_or_more (zero_or_more r)) xs = matches (zero_or_more r) xs.
Admitted.

(* TODO *)
(* (empty)* = empty *)
Theorem zero_or_more_empty : forall (xs: list X),
  matches (zero_or_more empty) xs = matches empty xs.
Admitted.

(* (nothing)* = empty *)
Theorem nothing_zero_or_more : forall (xs: list X),
  matches (zero_or_more nothing) xs = matches empty xs.
Proof.
unfold matches.
induction xs.
- simpl.
  reflexivity.
- simpl.
  apply concat_nothing.
Qed.

(* TODO *)
(* not(not(r)) = r *)
Theorem not_not : forall (xs: list X) (r: regex),
  matches (not (not r)) xs = matches r xs.
Admitted.

(* mathing without simplification is the same as with simplification *)
Theorem simplify_is_correct : forall (xs: list X) (r: regex),
  matches r xs = smatches r xs.
Proof.
unfold matches.
unfold smatches.
induction xs.
- simpl.
  reflexivity.
- simpl.
  induction r; simpl; try (apply IHxs).
  * unfold smart_or.
    remember (compare_regex (derive r1 a) (derive r2 a)).
    induction c.
    + symmetry in Heqc.
      remember or_idemp as H_or_idemp.
      remember (H_or_idemp xs (derive r1 a) (derive r2 a)) as Hmatch_or_if.
      remember (Hmatch_or_if Heqc) as Hmatch_or.
      unfold matches in Hmatch_or.
      rewrite Hmatch_or.
      remember compare_equal as H_compare_equal.
      remember (H_compare_equal (derive r1 a) (derive r2 a) Heqc) as Heq_r1_r2.
      rewrite Heq_r1_r2.
      apply IHxs.
    + apply IHxs.
    + remember or_comm as H_or_comm.
      unfold matches in H_or_comm.
      rewrite H_or_comm.
      apply IHxs.
Qed.

(* Definition 4.2
   Two input characters are equivalent if for the same regex r
   they produce the same derivative.
*)
Definition eqv_char (a b: X) (r: regex) : Prop :=
  derive r a = derive r b.

(* Lemma 4.1 proves that given the equivalent_character property
   it also holds for the combinators.
   If characters a and b are equivalent for regular expressions r and s.
   Then they are also equivalent for the:
   - concat
   - or
   - and
   - zero_or_more
   - not
   or those regular expressions.
*)
Lemma eqv_concat : forall (a b: X) (r s: regex)
  (eqvr: eqv_char a b r) (eqvs: eqv_char a b s),
eqv_char a b (concat r s).
Proof.
(* TODO *)
Admitted.

Lemma eqv_or : forall (a b: X) (r s: regex)
  (eqvr: eqv_char a b r) (eqvs: eqv_char a b s),
eqv_char a b (or r s).
Proof.
unfold eqv_char.
intros.
simpl.
rewrite eqvr.
rewrite eqvs.
reflexivity.
Qed.

Lemma eqv_and : forall (a b: X) (r s: regex)
  (eqvr: eqv_char a b r) (eqvs: eqv_char a b s),
eqv_char a b (and r s).
Proof.
(* TODO *)
Admitted.

Lemma eqv_zero_or_more : forall (a b: X) (r: regex)
  (eqvr: eqv_char a b r),
eqv_char a b (zero_or_more r).
Proof.
(* TODO *)
Admitted.

Lemma eqv_not : forall (a b: X) (r: regex)
  (eqvr: eqv_char a b r),
eqv_char a b (not r).
Proof.
(* TODO *)
Admitted.



End Regexes.


