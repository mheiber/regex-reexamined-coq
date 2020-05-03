Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.

(* Alphabet is Sigma_k *)
(* We are defining it here as a1 and x0, but we could do any disjoint set *)
Inductive alphabet := a1 | a0.

Definition string := (list alphabet).

(*
**Definition 2.1.** A regular expression is defined recursively as follows:
1. The symbols of the alphabet $\Sigma_k$, $\lambda$ and $\emptyset$ are regular expressions.
2. If $P$ and $Q$ are regular expressions, then so are $P.Q$, $P^*$, and $f(P, Q)$,
   where $f$ is any Boolean function of $P$ and $Q$.
3. Nothing else is a regular expression unless its being so follows from a
   finite number of applications of Rules 1 and 2.
*)

Inductive regex :=
    | symbol : alphabet -> regex
    | lambda : regex
    | emptyset : regex
    | concat : regex -> regex -> regex
    | star : regex -> regex
    (* We can use nor to express f, 
       Since any Boolean function can be expressed using a finite number of sums and complements
       See https://en.wikipedia.org/wiki/Logical_NOR
    *)
    | nor : regex -> regex -> regex
    .

Definition complement (r: regex) : regex :=
    nor r r.

Definition and (r s: regex) : regex :=
    nor (nor r r) (nor s s).

Definition or (r s: regex) : regex :=
    nor (nor r s) (nor r s).

(* See https://en.wikipedia.org/wiki/Exclusive_or *)
Definition xor (r s: regex) : regex :=
    or (and r (complement s)) (and (complement r) s).

Definition I: regex :=
    complement (emptyset).

(*  A regular expression represents a set of sequences. 
    We define the following operations on sets of sequences: 
    If $P$ and $Q$ are two sets of sequences of symbols from our alphabet, $\Sigma_k$, we have:
*)

Inductive is_member: regex -> string -> Prop :=
    | is_member_lambda :
        is_member lambda []
    | is_member_symbol (a: alphabet) :
        is_member (symbol a) [a]
    (*
        *Product or Concatenation*. $(P.Q) = \{ s | s = p.q; p \in P, q \in Q \}$.
        (Sometimes the dot is omitted for convenience. Also, since the operation is associative we omit parentheses.)
    *)
    | is_member_concat (p q: regex) (s: string):
        (exists
            (p_s: string)
            (q_s: string)
            (pq_s: p_s ++ q_s = s),
            is_member p p_s /\
            is_member q q_s
        ) ->
        is_member (concat p q) s
    (*
        *Iterate or Star Operation*. $P^{*} = \cup_{0}^{\infty} P^n$ , where $P^2 = P.P$, etc. 
        and $P^0 = \lambda$, the set consisting of the sequence of zero length, 
        which has the property $\lambda . R = R .\lambda = R$.
    *)
    | is_member_star_0 (p: regex):
        is_member (star p) []
    | is_member_star_n (p: regex) (s: string):
        is_member (concat p (star p)) s ->
        is_member (star p) s
    (*
        *Boolean function*. We shall denote any Boolean function of $P$ and $Q$ by $f(P, Q)$. 
        Of course, all the laws of Boolean algebra apply.
        the *intersection* $P \& Q$,
    *)
    | is_member_intersection (p q: regex) (s: string):
        is_member p s ->
        is_member q s ->
        is_member (and p q) s
    (*
        the sum or union $P + Q$, 
    *)
    | is_member_union_l (p q: regex) (s: string):
        is_member p s ->
        is_member (or p q) s
    | is_member_union_r (p q: regex) (s: string):
        is_member q s ->
        is_member (or p q) s
    (*
         the modulo-two sum (exclusive OR) $P \oplus Q$, etc.
    *)
    | is_member_not (p: regex) (s: string):
        not_member p s ->
        is_member (complement p) s
(* 
    See how even and odd are defined in:
    http://www.cs.umd.edu/class/fall2019/cmsc631/res/IndPrinciples.html 
*)
with not_member: regex -> string -> Prop :=
    (*
        The empty set is denoted by $\emptyset$ and the universal set by $I$.
        Thus we have the complement $P'$ (with respect to $I$) of $P$,
    *)
    | not_member_empty_set (s: string):
        not_member emptyset s
    | not_member_lambda (s: string):
        (s <> []) ->
        not_member lambda s
    | not_member_symbol (a: alphabet) (s: string):
        (s <> [a]) ->
        not_member (symbol a) s
    | not_member_concat (p q: regex) (s: string):
        (forall
            (p_s: string)
            (q_s: string)
            (pq_s: p_s ++ q_s = s),
            not_member p p_s \/
            not_member q q_s
        ) ->
        not_member (concat p q) s
    | not_member_star (p: regex) (s: string):
        (s <> []) ->
        not_member (concat p (star p)) s ->
        not_member (star p) s
    | not_member_not (p: regex) (s: string):
        is_member p s ->
        not_member (complement p) s
    | not_member_intersection_l (p q: regex) (s: string):
        not_member p s ->
        not_member (and p q) s
    | not_member_intersection_r (p q: regex) (s: string):
        not_member q s ->
        not_member (and p q) s
    | not_member_union (p q: regex) (s: string):
        not_member p s ->
        not_member q s ->
        not_member (or p q) s
    .

Lemma is_member_or_not_member : forall (r: regex) (s: string),
    (is_member r s) \/ (not_member r s).
Proof.
(* TODO: Help Wanted *)
Abort.

Lemma is_member_not_member_dec : forall (r: regex) (s: string),
    {is_member r s} + {not_member r s}.
Proof.
(* TODO: Help Wanted *)
Abort.

Lemma is_member_false_not_member : forall (r: regex) (s: string),
    (is_member r s -> False) -> not_member r s.
Proof.
(* TODO: Help Wanted *)
Abort.

Lemma not_member_false_is_member : forall (r: regex) (s: string),
    (not_member r s -> False) -> is_member r s.
Proof.
(* TODO: Help Wanted *)
Admitted.

Lemma not_member_is_member_false : forall (r: regex) (s: string),
    not_member r s -> is_member r s -> False.
Proof.
(* TODO: Help Wanted *)
Admitted.

Lemma is_member_not_member_false : forall (r: regex) (s: string),
    is_member r s -> not_member r s -> False.
Proof.
(* TODO: Help Wanted *)
Admitted.

Lemma is_member_emptyset_false: 
    forall (p: string),
    is_member emptyset p -> False.
Proof.
intro p.
apply not_member_is_member_false.
apply not_member_empty_set.
Qed.

Lemma not_member_is_is_member_not : forall (r: regex) (s: string),
    not_member r s -> is_member (complement r) s.
Proof.
intros.
apply is_member_not.
apply H.
Qed.

Lemma is_member_not_is_not_member : forall (r: regex) (s: string),
    is_member (complement r) s -> not_member r s.
Proof.
(* TODO: Help Wanted *)
Abort.

(* \lambda.R = R.\lambda = R *)

Theorem expand_concat_lambda_l: forall (r: regex) (s: string),
    is_member r s -> is_member (concat lambda r) s.
Proof.
- intros.
  apply (is_member_concat lambda r s).
  exists [].
  exists s.
  cbn.
  assert (s = s).
  reflexivity.
  exists H0.
  split.
  + apply is_member_lambda.
  + apply H.
Qed.

Theorem collapse_concat_lambda_l: forall (r: regex) (s: string),
    is_member (concat lambda r) s -> is_member r s.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem expand_concat_lambda_r: forall (r: regex) (s: string),
    is_member r s -> is_member (concat r lambda) s.
Proof.
(* TODO: Good First Issue *)
Abort.

Theorem collapse_concat_lambda_r: forall (r: regex) (s: string),
    is_member (concat r lambda) s -> is_member r s.
Proof.
(* TODO: Help Wanted *)
Abort.

(*
The introduction of arbitrary Boolean functions enriches the language of regular expressions. 
For example, suppose we desire to represent the set of all sequences having three consecutive 1's 
but not those ending in 01 or consisting of 1's only. 
The desired expression is easily seen to be:

R = (I.1.1.1.I)\&(I.0.1+1.1^{*})'.
*)
Definition x1 := symbol a1.
Definition x0 := symbol a0.
Definition xI111I := concat I (concat x1 (concat x1 (concat x1 I))).
Definition xI01 := concat I (concat x0 x1).
Definition x11star := concat x1 (star x1).
Definition exampleR := and xI111I (complement (or xI01 x11star)).

Lemma test_member_xI01_101:
    is_member xI01 ([a1] ++ [a0] ++ [a1]).
Proof.
unfold xI01.
apply is_member_concat.
exists [a1].
exists ([a0] ++ [a1]).
split.
- constructor.
- split.
  + constructor. constructor.
  + constructor.
    * exists [a0]. exists [a1].
      assert ([a0] ++ [a1] = [a0] ++ [a1]).
      reflexivity.
      exists H.
      split.
      constructor.
      constructor.
Qed.

Lemma test_not_member_xI01_101_false:
    not_member xI01 ([a1] ++ [a0] ++ [a1]) -> False.
Proof.
apply is_member_not_member_false.
apply test_member_xI01_101.
Qed.

Lemma test_not_member_xI01_empty:
    not_member xI01 [].
Proof.
constructor.
intros.
remember (app_eq_nil p_s q_s pq_s).
destruct a.
right.
apply not_member_concat.
intros.
rewrite e0 in pq_s0.
remember (app_eq_nil p_s0 q_s0 pq_s0).
destruct a.
rewrite e1.
rewrite e2.
left.
constructor.
discriminate.
Qed.

Lemma app_eq_unit_2 : forall (A: Type) (xs ys: list A) (x y: A),
    xs ++ ys = [x;y] <->
    (xs = [] /\ ys = [x;y])
    \/ (xs = [x] /\ ys = [y])
    \/ (xs = [x;y] /\ ys = []).
Proof.
Admitted.

Local Ltac breakdown :=
    repeat match goal with
            | [ H: _ \/ _ |- _ ] =>
                destruct H
            | [ H: _ /\ _ |- _ ] =>
                destruct H
            | [ H: ?X ++ ?Y = ?XS ++ ?YS |- _ ] =>
                cbn in H
            | [ H: ?XS ++ ?YS = [?X;?Y] |- _ ] =>
                idtac X;
                apply (app_eq_unit_2 alphabet XS YS X Y) in H
           end.

Lemma test_not_member_xI01_10:
    not_member xI01 ([a1] ++ [a0]).
Proof.
unfold xI01.
apply not_member_concat.
intros p' q' H_p_app_q.
right.
constructor.
intros p0 q0 H_p0_app_q0.
rewrite <- H_p0_app_q0 in H_p_app_q.
breakdown.
- left.
  constructor.
  rewrite H0.
  discriminate.
- left.
  constructor.
  rewrite H0.
  discriminate.
- left.
  constructor.
  rewrite H0.
  discriminate.
- apply app_eq_unit in H0.
  breakdown.
  + left.
    constructor.
    rewrite H0.
    discriminate.
  + right.
    constructor.
    rewrite H1.
    discriminate.
- apply app_eq_nil in H0.
  breakdown.
  left.
  constructor.
  rewrite H0.
  discriminate.
Qed.

Lemma fst1: forall (A: Type) (x: A) (y: A) (xs: list A) (ys: list A),
    x :: xs = [y] ++ ys ->
    x = y /\ xs = ys.
Admitted.

Lemma fst2: forall (A: Type) (x: A) (y: A) (xy: x <> y) (xs ys zs: list A),
    xs ++ ys = x :: zs ->
    xs <> [y].
Admitted.

Lemma three: forall (A: Type) (x y z: A),
    [x; y; z] = [x; y] ++ [z].
Admitted.

Lemma last1: forall (A: Type) (x y: A) (xy: x <> y) (xs ys zs xs': list A),
    xs ++ ys ++ zs = xs' ++ [x] ->
    zs <> [y].
Admitted.

Lemma test_not_member_xI01_1110:
    not_member xI01 ([a1] ++ [a1] ++ [a1] ++ [a0]).
Proof.
unfold xI01.
apply not_member_concat.
intros.
destruct p_s.
- destruct q_s.
  + left. cbn. discriminate.
  + right.
    apply not_member_concat.
    intros.
    left.
    constructor.
    cbn in pq_s.
    rewrite pq_s in pq_s0.
    breakdown.
    apply fst1 in pq_s.
    assert (a1 <> a0) as a10. discriminate.
    apply (fst2 alphabet a1 a0 a10) in pq_s0.
    exact pq_s0.
- cbn in pq_s.
  apply fst1 in pq_s.
  destruct pq_s.
  right.
  apply not_member_concat.
  intros.
  rewrite <- pq_s in H0.
  right.
  constructor.
  assert (a0 <> a1) as a01. discriminate.
  rewrite three in H0.
  apply (last1 alphabet a0 a1 a01) in H0.
  exact H0.
Qed.

Lemma combo4: forall (A: Type) (x y: A) (xs ys: list A),
    xs ++ ys = [x;x;x;y] ->
    (xs = [] /\ ys = [x;x;x;y])
    \/ (xs = [x] /\ ys = [x;x;y])
    \/ (xs = [x;x] /\ ys = [x;y])
    \/ (xs = [x;x;x] /\ ys = [y])
    \/ (xs = [x;x;x;y] /\ ys = []).
Admitted.

Lemma combo3: forall (A: Type) (x y: A) (xs ys: list A),
    xs ++ ys = [x;x;y] ->
    (xs = [] /\ ys = [x;x;y])
    \/ (xs = [x] /\ ys = [x;y])
    \/ (xs = [x;x] /\ ys = [y])
    \/ (xs = [x;x;y] /\ ys = []).
Admitted.

Lemma test_not_member_x11star_0: 
    not_member x11star ([a0]).
Proof.
constructor.
intros.
apply app_eq_unit in pq_s.
breakdown.
- left.
  rewrite H.
  constructor.
  discriminate.
- left.
  rewrite H.
  constructor.
  discriminate.
Qed.

Lemma test_not_member_x11star_10: 
    not_member x11star ([a1] ++ [a0]).
Proof.
constructor.
intros.
cbn in pq_s.
apply app_eq_unit_2 in pq_s.
breakdown.
- left. rewrite H. constructor. discriminate.
- right. constructor.
  + rewrite H0. discriminate.
  + rewrite H0. apply test_not_member_x11star_0.
- left. rewrite H. constructor. discriminate.
Qed.  

Lemma test_not_member_x11star_110: 
    not_member x11star ([a1] ++ [a1] ++ [a0]).
Proof.
constructor.
intros.
cbn in pq_s.
apply combo3 in pq_s.
breakdown.
- left. rewrite H. constructor. discriminate.
- right. constructor.
  + rewrite H0. discriminate.
  + rewrite H0. apply test_not_member_x11star_10.
- left. rewrite H. constructor. discriminate.
- left. rewrite H. constructor. discriminate.
Qed.

Lemma test_not_member_x11star_1110: 
    not_member x11star ([a1] ++ [a1] ++ [a1] ++ [a0]).
Proof.
unfold x11star.
apply not_member_concat.
intros.
apply combo4 in pq_s.
breakdown.
- left. apply not_member_symbol. rewrite H. discriminate.
- right. constructor.
  + rewrite H0. discriminate.
  + rewrite H0. apply test_not_member_x11star_110.
- left. apply not_member_symbol. rewrite H. discriminate.
- left. apply not_member_symbol. rewrite H. discriminate.
- left. apply not_member_symbol. rewrite H. discriminate.
Qed.

Lemma test_member_xI111I_1110: 
    is_member xI111I ([a1] ++ [a1] ++ [a1] ++ [a0]).
Proof.
unfold xI111I.
rewrite <- app_nil_l.
apply is_member_concat.
exists [].
exists ([a1] ++ [a1] ++ [a1] ++ [a0]).
unfold I.
split.
reflexivity.
split.
apply is_member_not.
apply not_member_empty_set.
apply is_member_concat.
exists [a1].
exists ([a1] ++ [a1] ++ [a0]).
split.
reflexivity.
split.
apply is_member_symbol.
apply is_member_concat.
exists [a1].
exists ([a1] ++ [a0]).
split.
reflexivity.
split.
apply is_member_symbol.
apply is_member_concat.
exists [a1].
exists [a0].
split.
reflexivity.
split.
apply is_member_symbol.
apply is_member_not.
apply not_member_empty_set.
Qed.

Theorem test_exampleR_1110_member: 
    is_member exampleR ([a1] ++ [a1] ++ [a1] ++ [a0]).
Proof.
unfold exampleR.
apply is_member_intersection.
- apply test_member_xI111I_1110.
- apply is_member_not.
  apply not_member_union.
  + apply test_not_member_xI01_1110.
  + apply test_not_member_x11star_1110. 
Qed.

Theorem test_exampleR_111_not_member : is_member exampleR [a1; a1; a1].
Proof.
(* TODO: Help Wanted *)
Abort.

(*
    **Definition 3.2.** Given any set $R$ of sequences we define $\delta(R)$ to be

    $$
    \begin{aligned}
    \delta(R) & = \lambda\ \text{if}\ \lambda \in R \\
              & = \emptyset\ \text{if}\ \lambda \notin R \\
    \end{aligned}
    $$
*)

Inductive delta: regex -> regex -> Prop :=
    | delta_lambda (r: regex):
        is_member r [] ->
        delta r lambda
    | delta_emptyset (r: regex):
        not_member r [] ->
        delta r emptyset
    .

(*
    It is clear that:

    $$
    \begin{aligned}
    \delta(a) & = \emptyset\ \text{for any}\ a \in \Sigma_k, \\
    \delta(\lambda) & = \lambda, \text{and} \\
    \delta(\emptyset) & = \emptyset . \\
    \end{aligned}
    $$
*)

Theorem delta_lambda_is_lambda: delta lambda lambda.
Proof.
apply delta_lambda.
apply is_member_lambda.
Qed.

Theorem delta_emptyset_is_emptyset: delta emptyset emptyset.
Proof.
apply delta_emptyset.
apply not_member_empty_set.
Qed.

Theorem delta_symbol_is_emptyset: forall (a: alphabet),
    delta (symbol a) emptyset.
Proof.
intros.
apply delta_emptyset.
(* TODO: Help Wanted *)
Abort.

(*
    Furthermore

    $$
    \begin{aligned}
    \delta(P* ) &= \lambda\ \text{(by definition of * ), and} \\
    \delta(P.Q) &= \delta(P)\ \&\ \delta(Q).
    \end{aligned}
    $$
*)

Theorem delta_star_is_lambda: forall (r: regex),
    delta (star r) lambda.
Proof.
intros.
apply delta_lambda.
apply is_member_star_0.
Qed.

Theorem delta_concat_is_and_lambda: forall (p q: regex),
    delta p lambda ->
    delta q lambda ->
    delta (concat p q) lambda.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem delta_concat_is_and_emptyset_r: forall (p q: regex),
    delta p emptyset ->
    delta q lambda ->
    delta (concat p q) emptyset.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem delta_concat_is_and_emptyset_l: forall (p q: regex),
    delta p lambda ->
    delta q emptyset ->
    delta (concat p q) emptyset.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem delta_concat_is_and_emptyset: forall (p q: regex),
    delta p emptyset ->
    delta q emptyset ->
    delta (concat p q) emptyset.
Proof.
(* TODO: Help Wanted *)
Abort.

(*
    If $R = f(P, Q)$ it is also easy to determine $\delta(R)$. For example,

    $$
    \begin{aligned}
    \text{(3.1)}&\ \delta(P + Q)    &= \delta(P) + \delta(Q). \\
    \text{(3.2)}&\ \delta(P\ \&\ Q) &= \delta(P)\ \&\ \delta(Q). \\
    \text{(3.3)}&\ \delta(P')       &= \lambda\ \text{if}\ \delta(P) = \emptyset \\
                &                   &= \emptyset\ \text{if}\ \delta(P) = \lambda \\
    \end{aligned}
    $$
*)

Theorem delta_or_lambda: forall (p q: regex),
    delta p lambda ->
    delta q lambda ->
    delta (or p q) lambda.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem delta_or_lambda_l: forall (p q: regex),
    delta p lambda ->
    delta q emptyset ->
    delta (or p q) lambda.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem delta_or_lambda_r: forall (p q: regex),
    delta p emptyset ->
    delta q lambda ->
    delta (or p q) lambda.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem delta_or_emptyset: forall (p q: regex),
    delta p emptyset ->
    delta q emptyset ->
    delta (or p q) emptyset.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem delta_and_lambda: forall (p q: regex),
    delta p lambda ->
    delta q lambda ->
    delta (and p q) lambda.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem delta_and_emptyset_r: forall (p q: regex),
    delta p emptyset ->
    delta q lambda ->
    delta (and p q) emptyset.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem delta_and_emptyset_l: forall (p q: regex),
    delta p lambda ->
    delta q emptyset ->
    delta (and p q) emptyset.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem delta_and_emptyset: forall (p q: regex),
    delta p emptyset ->
    delta q emptyset ->
    delta (and p q) emptyset.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem delta_not_emptyset: forall (r: regex),
    delta r lambda ->
    delta (complement r) emptyset.
Proof.
(* TODO: Help Wanted *)
Abort.

Theorem delta_not_lambda: forall (r: regex),
    delta r emptyset ->
    delta (complement r) lambda.
Proof.
(* TODO: Help Wanted *)
Abort.

(*
    We define another operation on a set $R$ of sequences, 
    yielding a new set of sequences called a derivative of $R$.
    **Definition 3.1.** Given a set $R$ of sequences and a finite sequence $s$, 
    the derivative of $R$ with respect to $s$ is denoted by $D_s R$ and is 
    $D_s R = \{t | s.t \in R \}$.
*)

(* TODO: Help Wanted
   The definition of derivative is probably incorrect.
*)
Inductive derivative: regex -> string -> regex -> Prop :=
    | is_derivative (r: regex) (s: string) (dr: regex):
        (exists (dr: regex),
            forall (t: string)
                   (m: is_member r (s ++ t)),
            is_member dr t
        ) -> derivative r s dr
    .

(*
    **THEOREM 3.1.** If $R$ is a regular expression, 
    the derivative of $R$ with respect to a character $a \in \Sigma_k$ 
    is found recursively as follows:

    $$
    \begin{aligned}
    \text{(3.4)}&\ D_a a &=&\ \lambda, \\
    \text{(3.5)}&\ D_a b &=&\ \emptyset,\ \text{for}\ b = \lambda\ \text{or}\ b = \emptyset\ \text{or}\ b \in A_k\ \text{and}\ b \neq a, \\
    \text{(3.6)}&\ D_a (P^* ) &=&\ (D_a P)P^*, \\
    \text{(3.7)}&\ D_a (PQ) &=&\ (D_a P)Q + \delta(P)(D_a Q). \\
    \text{(3.8)}&\ D_a (f(P, Q)) &=&\ f(D_a P, D_a Q). \\
    \end{aligned}
    $$
*)

Lemma list_app_concat : forall {A: Type} (x: A) (xs: list A),
    x :: xs = [x] ++ xs.
Proof.
reflexivity.
Qed.

Lemma concat_lambda_lambda: forall (xs: string),
    is_member (concat lambda lambda) xs -> is_member lambda xs.
Admitted.

(*
    \text{(3.4)}&\ D_a a &=&\ \lambda
*)
Theorem derivative_a: forall (a: alphabet),
    derivative (symbol a) [a] lambda.
Proof.
intros.
constructor.
exists lambda.
intros.
induction t.
- apply is_member_lambda.
- rewrite list_app_concat.
Abort.

Theorem lambda_only_empty: forall (x: alphabet) (xs: string),
    is_member lambda (x :: xs) -> False.
Proof.
intros.
Admitted.

(*
    \text{(3.5)}&\ D_a b &=&\ \emptyset,\ \text{for}\ 
      b = \lambda\ \text{or}\ 
      b = \emptyset\ \text{or}\ 
      b \in A_k\ \text{and}\ b \neq a
*)
Theorem derivative_lambda_symbol: forall (a: alphabet),
    derivative lambda [a] emptyset.
Proof.
intros.
constructor.
exists emptyset.
induction t.
- intros.
  apply lambda_only_empty in m.
  contradiction.
- intros.
  apply lambda_only_empty in m.
  contradiction.
Qed.

Theorem derivative_emptyset_symbol: forall (a: alphabet),
    derivative emptyset [a] emptyset.
Proof.
intros.
constructor.
exists emptyset.
intros.
remember (is_member_not_member_false emptyset ([a] ++ t) m).
remember (not_member_empty_set ([a] ++ t)).
remember (f n).
contradiction.
Qed.

Theorem derivative_b: forall (a: alphabet) (b: alphabet) (n: ~ (b = a)),
    derivative (symbol b) [a] emptyset.
Proof.
(* TODO: Help Wanted *)
Abort.

(*
    \text{(3.6)}&\ D_a (P^* ) &=&\ (D_a P)P^*
*)
Theorem derivative_star: forall 
    (a: alphabet)
    (p: regex),
    exists
        (dp: regex),
        derivative p [a] dp ->
        derivative (star p) [a] (concat dp (star p))
    .
Proof.
(* TODO: Help Wanted *)
Abort.

(*
    \text{(3.7)}&\ D_a (PQ) &=&\ (D_a P)Q + \delta(P)(D_a Q).
*)
Theorem derivative_concat: forall
    (a: alphabet)
    (p q: regex),
    exists
        (dp: regex)
        (dq: regex)
        (deltap: regex),
        derivative p [a] dp ->
        derivative q [a] dq ->
        delta p deltap ->
        derivative (concat p q) [a] (or (concat dp q) (concat deltap dq)).
Proof.
(* TODO: Help Wanted *)
Abort.

(*
    \text{(3.8)}&\ D_a (f(P, Q)) &=&\ f(D_a P, D_a Q).
*)
Theorem derivative_nor: forall
    (a: alphabet)
    (p q: regex),
    exists
        (dp: regex)
        (dq: regex),
        derivative p [a] dp ->
        derivative q [a] dq ->
        derivative (nor p q) [a] (nor dp dq).
Proof.
(* TODO: Help Wanted *)
Abort.

(* TODO: Translate more proofs from the paper *)