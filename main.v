(* main.v *)
(* Singapore, Tue 26 Mar 2024 *)

(* ********** *)
(* {FOLD_UNFOLD_TACTIC} *)
Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.
(* {END} *)
Require Import Arith Bool List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Setoid Program.
(* CHECK https://github.com/snu-sf/paco for installation *)
Require Import Paco.paco.



(* ************************************************************ *)
(* ***************************SETUP**************************** *)
(* ************************************************************ *)

(* ******************** *)
(* MISCELLANEOUS *)
(* ******************** *)

(* auxiliary power function and its unfolding lemmas: *)

(* {POWER_AUX} *)
Fixpoint power_aux (b e : nat) : nat :=
  match e with
    | 0    => b
    | S e' => (power_aux b e') * b
  end.
(* {END} *)

(* {FOLD_UNFOLD_POWER_AUX} *)
Lemma fold_unfold_power_aux_O :
  forall b : nat, power_aux b 0 = b.
Proof.
  fold_unfold_tactic power_aux.
Qed.

Lemma fold_unfold_power_aux_S :
  forall b e' : nat, power_aux b (S e') = (power_aux b e') * b.
Proof.
  fold_unfold_tactic power_aux.
Qed.
(* {END} *)
(* ********** *)

(* power function and its unfolding lemmas: *)
(* {POWER} *)
Definition power (b e' : nat) : nat :=
  match e' with
    | 0     => 1
    | S e'' => power_aux b e''
  end.
(* {END} *)

Lemma unfold_power_O :
  forall b : nat, power b 0 = 1.
Proof.
  intros b; unfold power; reflexivity.
Qed.

Lemma unfold_power_S :
  forall b e'' : nat, power b (S e'') = power_aux b e''.
Proof.
  intros b e''; unfold power; reflexivity.
Qed.

Lemma about_power_aux_0_Se :
  forall (e : nat), power 0 (S e) = 0.
Proof.
  intros; rewrite -> unfold_power_S; case e as [ | e'].
  - rewrite -> fold_unfold_power_aux_O; reflexivity.
  - rewrite -> fold_unfold_power_aux_S, Nat.mul_0_r; reflexivity.
Qed. 

(* ********** *)

Notation "base ^ exponent" := (power base exponent).

(* ********** *)
(* END OF MISCELLANEOUS *)

(* ************************************************************ *)

(* ******************** *)
(* BINOMIAL COEFFICIENTS *)
(* ******************** *)

(* binomial_coefficient function and its unfolding lemmas: *)

(* START binomial_coefficient START *)
(* {BINOMIAL_COEFFICIENT} *)
Fixpoint binomial_coefficient (n k : nat) : nat :=
  match n with
  | O    => match k with
            | O    => 1
            | S k' => 0
            end
  | S n' => match k with
            | O    => 1
            | S k' => binomial_coefficient n' k' + binomial_coefficient n' (S k')
            end
  end.
(* {END} *)

(* {FOLD_UNFOLD_BINOMIAL_COEFFICIENT} *)
Lemma fold_unfold_binomial_coefficient_O :
  forall k : nat, binomial_coefficient 0 k =
      match k with
      | O    => 1
      | S k' => 0
      end.
Proof.
  fold_unfold_tactic binomial_coefficient.
Qed.

Lemma fold_unfold_binomial_coefficient_S :
  forall n' k : nat, binomial_coefficient (S n') k =
      match k with
      | O    => 1
      | S k' => binomial_coefficient n' k' + binomial_coefficient n' (S k')
      end.
Proof.
  fold_unfold_tactic binomial_coefficient.
Qed.
(* {END} *)


(* ********** *)

(* reasoning about binomial coefficients: *)
(* {ABOUT_BINOMIAL_COEFFICIENT_K_MORE_THAN_N} *)
Lemma about_binomial_coefficient_k_more_than_n :
  forall n k : nat,
    n < k <-> binomial_coefficient n k = 0.
Proof.
  induction n as [ | n' IHn']; intro k.
  - split.
    + intro H_k.
      case k as [ | k'].
      * contradiction (Nat.lt_irrefl 0 H_k).
      * rewrite -> fold_unfold_binomial_coefficient_O.
        reflexivity.
    + intro H_k.
      case k as [ | k'].
      * rewrite -> fold_unfold_binomial_coefficient_O in H_k.
        discriminate H_k.
      * exact (Nat.lt_0_succ k').
  - split.
    + intro H_k.
      case k as [ | k'].
      * contradiction (Nat.nlt_0_r (S n') H_k).
      * rewrite -> fold_unfold_binomial_coefficient_S.
        destruct (IHn' k') as [lt_implies_O O_implies_lt].
        rewrite -> (lt_implies_O (lt_S_n n' k' H_k)).
        rewrite -> Nat.add_0_l.
        destruct (IHn' (S k')) as [lt_implies_O' O_implies_lt'].
        exact (lt_implies_O' (lt_trans n' (S n') (S k') (Nat.lt_succ_diag_r n') H_k)).
    + intro H_k.
      case k as [ | k'].
      * rewrite -> fold_unfold_binomial_coefficient_S in H_k.
        discriminate H_k.
      * rewrite -> fold_unfold_binomial_coefficient_S in H_k.
        destruct (plus_is_O (binomial_coefficient n' k') (binomial_coefficient n' (S k')) H_k) as [H_n'_k' H_n'_Sk'].
        destruct (IHn' k') as [lt_implies_O O_implies_lt].
        exact (lt_n_S n' k' (O_implies_lt H_n'_k')).
Qed.
(* {END} *)

(* *** *)

(* {ABOUT_BINOMIAL_COEFFICIENTS_N_N} *)
Lemma about_binomial_coefficients_n_n :
  forall n : nat, binomial_coefficient n n = 1.
Proof.
  induction n as [ | n' IHn'].
  - rewrite -> fold_unfold_binomial_coefficient_O.
    reflexivity.
  - rewrite -> fold_unfold_binomial_coefficient_S.
    destruct (about_binomial_coefficient_k_more_than_n n' (S n')) as [H_key _].
    rewrite -> (H_key (Nat.lt_succ_diag_r n')).
    rewrite -> Nat.add_0_r.
    exact IHn'.
Qed.
(* {END} *)

(* *** *)

Lemma about_binomial_coefficients_n_0 :
  forall n : nat, binomial_coefficient n 0 = 1.
Proof.
  intros [ | n'].
  - rewrite -> fold_unfold_binomial_coefficient_O.
    reflexivity.
  - rewrite -> fold_unfold_binomial_coefficient_S.
    reflexivity.
Qed.

(* *** *)

Lemma about_binomial_coefficients_n_S0 :
  forall n : nat, binomial_coefficient n 1 = n.
Proof.
  induction n as [ | n' IHn'].
  - destruct (about_binomial_coefficient_k_more_than_n 0 1).
    rewrite -> (H (Nat.lt_0_1)).
    reflexivity.
  - rewrite -> fold_unfold_binomial_coefficient_S.
    rewrite -> about_binomial_coefficients_n_0.
    rewrite -> IHn'.
    rewrite -> Nat.add_1_l.
    reflexivity.
Qed.

(* *** *)
  
Lemma about_binomial_coefficients_Sn_0 :
  forall n : nat, binomial_coefficient n 0 = binomial_coefficient (S n) 0.
Proof.
  intro n.
  rewrite -> 2about_binomial_coefficients_n_0.
  reflexivity.
Qed.

(* *** *)

Lemma about_equivalence_of_binomial_coefficients :
  forall (n k : nat),
    binomial_coefficient (n + k) k = binomial_coefficient (n + k) n.
Proof.
  induction n as [ | n' IHn']; intro k.
  - induction k as [ | k' IHk'].
    + reflexivity.
    + rewrite -> Nat.add_0_l.
      rewrite -> about_binomial_coefficients_n_0.
      rewrite -> about_binomial_coefficients_n_n.
      reflexivity.
  - induction k as [ | k' IHk'].
    + rewrite -> Nat.add_0_r.
      rewrite -> about_binomial_coefficients_n_0.
      rewrite -> about_binomial_coefficients_n_n.
      reflexivity.
    + rewrite -> Nat.add_succ_l.
      rewrite -> 2fold_unfold_binomial_coefficient_S.
      rewrite <- (Nat.add_succ_comm n' k') at 1.
      rewrite -> IHk'.
      rewrite -> (IHn' (S k')).
      rewrite -> (Nat.add_succ_comm n' k') at 1.
      rewrite -> (Nat.add_comm (binomial_coefficient (n' + S k') (S n')) (binomial_coefficient (n' + S k') n')).
      reflexivity.
Qed.


(* *** *)
(* {PASCALS_IDENTITY} *)
Lemma pascals_identity :
  forall n k : nat,
    binomial_coefficient (S n) (S k) = binomial_coefficient n k + binomial_coefficient n (S k).
Proof.
  intros n k.
  rewrite -> fold_unfold_binomial_coefficient_S.
  reflexivity.
Qed.
(* {END} *)


(* Factorial function *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => (S n') * factorial n'
  end.

Lemma fold_unfold_factorial_O :
  factorial 0 = 1.
Proof. fold_unfold_tactic factorial. Qed.

Lemma fold_unfold_factorial_S :
  forall (n' : nat), factorial (S n') = (S n') * factorial n'.
Proof. fold_unfold_tactic factorial. Qed.

(* Binomial coefficient using combinatorial definition *)
Definition binomial_coefficient_comb (n k : nat) : nat :=
  factorial n / (factorial k * factorial (n - k)).

Lemma factorial_non_0 :
  forall (n : nat), factorial n <> 0.
Proof.
  induction n.
  - rewrite -> fold_unfold_factorial_O.
    auto.
  - rewrite -> fold_unfold_factorial_S.
    destruct (Nat.neq_mul_0 (S n) (factorial n)).
    exact (H (conj (Nat.neq_succ_0 n) IHn)).
Qed.    
    
(* Lemma: equivalence of binomial coefficient definitions *)
Lemma binomial_coefficient_eq : forall n k : nat,
    k <= n ->
    binomial_coefficient_comb n k = binomial_coefficient n k.
Proof.
  intros n k le_k_n.
  unfold binomial_coefficient_comb.
  revert k le_k_n.
  induction n; intros.
  - Search (_ <= 0 -> _).
    rewrite <- (Arith_prebase.le_n_0_eq_stt k le_k_n).
    simpl; reflexivity.
  - rewrite -> fold_unfold_binomial_coefficient_S.
    induction k as [ | k' IHk'].
    + rewrite -> Nat.sub_0_r, fold_unfold_factorial_O, Nat.mul_1_l.
      rewrite -> (Nat.div_same (factorial (S n)) (factorial_non_0 (S n))).
      reflexivity.
    + Search (S _ <= S _ -> _).
      destruct (le_S_n k' n le_k_n).
      * Search (_ - _ = 0).
        rewrite -> Nat.sub_diag.
        rewrite -> fold_unfold_factorial_O.
        rewrite -> Nat.mul_1_r.
        rewrite -> (Nat.div_same (factorial (S k')) (factorial_non_0 (S k'))).
        rewrite -> about_binomial_coefficients_n_n.
        destruct (about_binomial_coefficient_k_more_than_n k' (S k')).
        rewrite -> (H (Nat.lt_succ_diag_r k')).
        ring.
      * Check (IHn k').
        Search (_ <= _ -> S _ <= S _).
        rewrite <- (IHn (S k') (le_n_S k' m l)).
        rewrite <- (IHn k' (le_S_n k' (S m) le_k_n)).
        Compute (
            let m := 5 in
            let k' := 3 in
            factorial (S (S m)) / (factorial (S k') * factorial (S (S m) - S k')) =
              factorial (S m) / (factorial k' * factorial (S m - k')) +
                factorial (S m) / (factorial (S k') * factorial (S m - S k'))
          ).
        { admit. }
Admitted.


(* ********** *)
(* END OF BINOMIAL COEFFICIENTS *)

(* ************************************************************ *)

(* ******************** *)
(* SIGMA *)
(* ******************** *)

(* Sigma function and its unfolding lemmas: *)
(* {SIGMA} *)
Fixpoint Sigma (n : nat) (f : nat -> nat) : nat :=
  match n with
  | O    => f 0
  | S n' => Sigma n' f + f n
  end.
(* {END} *)

(* {FOLD_UNFOLD_SIGMA_O} *)
Lemma fold_unfold_Sigma_O :
  forall (f : nat -> nat), Sigma 0 f = f 0.
(* {END} *)
Proof.
  fold_unfold_tactic Sigma.
Qed.

(* {FOLD_UNFOLD_SIGMA_S} *)
Lemma fold_unfold_Sigma_S :
  forall (n' : nat) (f : nat -> nat), Sigma (S n') f = Sigma n' f + f (S n').
(* {END} *)
Proof.
  fold_unfold_tactic Sigma.
Qed.
(* {END} *)

(* ********** *)

(* reasoning about Sigma: *)


Lemma about_factoring_a_multiplicative_constant_on_the_right_in_Sigma :
  forall (x c : nat) (f : nat -> nat),
    Sigma x (fun i => f i * c) = Sigma x f * c.
Proof.
  induction x as [| x' IHx]; intros c f.
  - rewrite -> 2 fold_unfold_Sigma_O.
    reflexivity.
  - rewrite -> 2 fold_unfold_Sigma_S.
    rewrite -> (Nat.mul_add_distr_r (Sigma x' f) (f (S x')) c).
    rewrite -> IHx.
    reflexivity.
Qed.

(* ***** *)

Lemma about_factoring_a_multiplicative_constant_on_the_left_in_Sigma :
  forall (x c : nat) (f : nat -> nat),
    Sigma x (fun i => c * f i) = c * Sigma x f.
Proof.
  induction x as [| x' IHx]; intros c f.
  - rewrite -> 2 fold_unfold_Sigma_O.
    reflexivity.
  - rewrite -> 2 fold_unfold_Sigma_S.
    rewrite -> (Nat.mul_add_distr_l c (Sigma x' f) (f (S x'))).
    rewrite -> IHx.
    reflexivity.
Qed.


Lemma about_factoring_a_function_on_the_left_in_double_Sigma :
  forall (x y : nat)
         (f : nat -> nat)
         (g : nat -> nat -> nat),
    Sigma x (fun j => Sigma y (fun i => f j * g i j)) =
                        Sigma x (fun j => f j * Sigma y (fun i => g i j)).
Proof.
Admitted.

Lemma about_factoring_a_function_on_the_right_in_double_Sigma :
  forall (x y : nat)
         (f : nat -> nat)
         (g : nat -> nat -> nat),
    Sigma x (fun j => Sigma y (fun i => g i j * f j)) =
                        Sigma x (fun j => Sigma y (fun i => g i j) * f j).
Proof.
Admitted.

Lemma about_mining_term :
  forall (n : nat)
         (f : nat -> nat),
    f 0 + Sigma n (fun i => f (S i)) =
      Sigma (S n) (fun i => f i).
Proof.
Admitted.

  
Lemma about_mult_assoc_in_Sigma :
  forall (x : nat)
         (f g h : nat -> nat),
    Sigma x (fun i => f i * g i * h i) = Sigma x (fun i => f i * (g i * h i)).
Proof.
Admitted.

Lemma about_mult_assoc_in_double_Sigma :
  forall (x y : nat)
         (f g h : nat -> nat -> nat),
    Sigma x (fun j => Sigma y (fun i => f i j * g i j * h i j)) = Sigma x (fun j => Sigma y (fun i => f i j * (g i j * h i j))).
Proof.
Admitted.

Lemma about_mul_commutativity_in_Sigma :
  forall (x : nat)
         (f g : nat -> nat),
    Sigma x (fun i => f i * g i) = Sigma x (fun i => g i * f i).
Proof.
Admitted.
  
(* ***** *)

Lemma about_swapping_Sigma :
  forall (x y : nat) (f : nat -> nat -> nat),
    Sigma x (fun i => Sigma y (fun j => f i j)) = Sigma y (fun j => Sigma x (fun i => f i j)).
Proof.
  induction x as [ | x' IHx'].
  - induction y as [ | y' IHy']; intro f.
    + rewrite -> 4 fold_unfold_Sigma_O.
      reflexivity.
    + rewrite -> fold_unfold_Sigma_O.
      rewrite -> 2 fold_unfold_Sigma_S.
      rewrite -> fold_unfold_Sigma_O.
      rewrite <- (IHy' f).
      rewrite -> fold_unfold_Sigma_O.
      reflexivity.
  - induction y as [ | y' IHy']; intro f.
    + rewrite -> fold_unfold_Sigma_O.
      rewrite -> 2 fold_unfold_Sigma_S.
      rewrite -> fold_unfold_Sigma_O.
      rewrite -> (IHx' 0 f).
      rewrite -> fold_unfold_Sigma_O.
      reflexivity.
    + rewrite -> 4 fold_unfold_Sigma_S.
      rewrite -> (IHx' (S y') f).
      rewrite <- (IHy' f).
      rewrite -> 2 fold_unfold_Sigma_S.
      rewrite <- (IHx' y' f).
      rewrite -> Nat.add_shuffle1.
      reflexivity.
Qed.

(* ***** *)
(* {ABOUT_SIGMA_WITH_TWO_EQUIVALENT_FUNCTIONS} *)
Lemma about_Sigma_with_two_equivalent_functions :
  forall (x : nat) (f g : nat -> nat),
    (forall i : nat, f i = g i) -> Sigma x f = Sigma x g.
Proof.
  induction x as [ | x' IHx']; intros f g eq_fi_gi.
  - rewrite -> 2 fold_unfold_Sigma_O.
    exact (eq_fi_gi 0).
  - rewrite -> 2 fold_unfold_Sigma_S.
    rewrite -> (eq_fi_gi (S x')).
    rewrite -> (IHx' f g eq_fi_gi).
    reflexivity.
Qed.
(* {END} *)

(* ***** *)

Lemma about_Sigma_with_two_equivalent_functions_up_to_the_bound :
  forall (x : nat) (f g : nat -> nat),
    (forall i : nat, i <= x -> f i = g i) ->
    Sigma x f = Sigma x g.
Proof.
  induction x as [ | x' IHx']; intros f g eq_fi_gi.
  - rewrite -> 2 fold_unfold_Sigma_O.
    exact (eq_fi_gi 0 (Nat.le_0_l 0)).
  - rewrite -> 2 fold_unfold_Sigma_S.
    rewrite -> (eq_fi_gi (S x') (Nat.le_refl (S x'))).
    assert (helpful : forall i : nat, i <= x' -> f i = g i).
    {
      intros i le_i_x'.
      rewrite <- (eq_fi_gi i).
      - reflexivity.
      - rewrite -> ((Nat.le_le_succ_r i x') le_i_x').
        reflexivity.
    }
    rewrite -> (IHx' f g helpful).
    reflexivity.
Qed.

(* ***** *)

Lemma about_Sigma_with_an_additive_function :
  forall (x : nat) (f g : nat -> nat),
    Sigma x (fun i => f i + g i) = Sigma x f + Sigma x g.
Proof.
  induction x as [ | x' IHx']; intros f g.
  - rewrite -> 3 fold_unfold_Sigma_O.
    reflexivity.
  - rewrite -> 3 fold_unfold_Sigma_S.
    rewrite -> (IHx' f g).
    exact (Nat.add_shuffle1 (Sigma x' f) (Sigma x' g) (f (S x')) (g (S x'))).
Qed.

(* ***** *)

Lemma about_Sigma_with_a_constant_function :
  forall x y : nat, Sigma x (fun _ => y) = y * (S x).
Proof.
  induction x as [ | x' IHx']; intro y.
  - rewrite -> fold_unfold_Sigma_O.
    rewrite -> Nat.mul_1_r; reflexivity.
  - rewrite -> fold_unfold_Sigma_S.
    rewrite -> (IHx' y).
    exact (mult_n_Sm y (S x')).
Qed.

Lemma about_Sigma_with_two_small_a_function :
  forall (x : nat) (f : nat -> nat),
    (forall i : nat, i <= x -> f i = 0) ->
    Sigma x f = 0.
Proof.
  induction x as [ | x' IHx']; intros f le_i_0_impl_0.
  - rewrite -> fold_unfold_Sigma_O.
    exact (le_i_0_impl_0 0 (Nat.le_refl 0)).
  - rewrite -> fold_unfold_Sigma_S.
    rewrite -> (le_i_0_impl_0 (S x') (Nat.le_refl (S x'))).
    assert (helpful : forall i : nat, i <= x' -> f i = 0).
    {
      intros i le_i_x'.
      exact (le_i_0_impl_0 i ((Nat.le_le_succ_r i x') le_i_x')).
    }
    rewrite -> (IHx' f helpful).
    reflexivity.
Qed.

(* ***** *)

Lemma about_Sigma_up_to_a_positive_sum :
  forall (x y : nat) (f : nat -> nat),
    Sigma (x + S y) f = Sigma x f + Sigma y (fun i => f (x + S i)).
Proof.
  case x as [ | x'].
  - induction y as [ | y' IHy']; intro f.
    * rewrite -> 2 fold_unfold_Sigma_O.
      rewrite -> Nat.add_0_l.
      exact (fold_unfold_Sigma_S 0 f).
    * rewrite -> fold_unfold_Sigma_S.
      rewrite -> Nat.add_0_l.
      rewrite -> fold_unfold_Sigma_S.
      rewrite -> Nat.add_0_l in IHy'.
      rewrite -> (IHy' f).
      rewrite -> Nat.add_assoc; reflexivity.
  - induction y as [ | y' IHy']; intro f.
    * rewrite -> (Nat.add_1_r (S x')).
      rewrite -> (fold_unfold_Sigma_S (S x') f).
      rewrite -> (fold_unfold_Sigma_S x' f).
      rewrite -> fold_unfold_Sigma_O.
      rewrite -> (Nat.add_1_r (S x')).
      reflexivity.
    * rewrite -> (fold_unfold_Sigma_S y' (fun i : nat => f (S x' + S i))).
      rewrite -> Nat.add_assoc.
      rewrite <- plus_n_Sm, fold_unfold_Sigma_S.
      rewrite -> IHy'.
      reflexivity.
Qed.

(* ***** *)

Lemma about_Sigma_specifically_left :
  forall (x y : nat) (f : nat -> nat),
    Sigma (x * S y + y) f = Sigma x (fun i => Sigma y (fun j => f (i * S y + j))).
Proof.
  induction x as [ | x' IHx']; intros y f.
  - rewrite -> fold_unfold_Sigma_O.
    rewrite -> Nat.mul_0_l.
    rewrite -> Nat.add_0_l.
    assert (helpful :
             forall j : nat,
               f (0 + j) = f j).
    {
      intro j; rewrite -> Nat.add_0_l; reflexivity.
    }
    exact (about_Sigma_with_two_equivalent_functions y f (fun j : nat => f (0 + j)) helpful).
  - rewrite -> fold_unfold_Sigma_S.
    rewrite -> Nat.mul_succ_l.
    rewrite -> Nat.add_shuffle0.
    rewrite -> (about_Sigma_up_to_a_positive_sum (x' * S y + y) y f).
    rewrite -> IHx'.
    apply (f_equal (fun z => Sigma x' (fun i : nat => Sigma y (fun j : nat => f (i * S y + j))) + z)).
    assert (helpful :
             forall i : nat,
               f (x' * S y + y + S i) = f (x' * S y + S y + i)).
    {
      intro i; rewrite <-2 plus_n_Sm; reflexivity.      
    }
    exact (about_Sigma_with_two_equivalent_functions y (fun i : nat => f (x' * S y + y + S i)) (fun j : nat => f (x' * S y + S y + j)) helpful).
Qed.

Lemma about_Sigma_up_to_a_positive_product_left :
  forall (x y : nat) (f : nat -> nat),
    Sigma (S x * S y) f = Sigma (x * S y + y) f + f (S x * S y).
Proof.
  intros x y f.
  rewrite -> (Nat.mul_succ_l x (S y)).
  rewrite -> (Nat.add_succ_r (x * S y) y).
  rewrite -> (fold_unfold_Sigma_S (x * S y + y) f).
  reflexivity.
Qed.

(* *** *)

Lemma about_splitting_Sigma_at_plus :
  forall (n : nat) (f g : nat -> nat),
    Sigma n (fun j => f j + g j) = Sigma n f + Sigma n g.
Proof.
  intros n f g.
  induction n as [ | n' IHn'].
  - rewrite -> 3fold_unfold_Sigma_O.
    reflexivity.
  - rewrite -> 3fold_unfold_Sigma_S.
    rewrite -> IHn'.
    rewrite -> Nat.add_shuffle1.
    reflexivity.
Qed.

(* ********** *)
(* END OF SIGMA *)

(* ************************************************************ *)

(* ******************** *)
(* STREAMS *)
(* ******************** *)

(* stream type *)
(* {STREAM} *)
CoInductive stream (V : Type) : Type := Cons : V -> stream V -> stream V.
(* {END} *)

(* ********** *)

(* stream decomposition (fold and unfold) *)
(* {FOLD_UNFOLD_STREAM} *)
Definition stream_decompose (V : Type) (s : stream V) :=
  match s with Cons _ v s' => Cons V v s' end.

Theorem stream_decomposition :
  forall (V : Type) (s : stream V),
    s = stream_decompose V s.
Proof.
  intros V [v s'].
  unfold stream_decompose.
  reflexivity.
Qed.

Ltac unfold_and_fold f :=
  unfold stream_decompose;
  unfold f; fold f.
(* {END} *)

(* ********** *)
(* END OF STREAMS *)

(* ************************************************************ *)

(* ******************** *)
(* REASONING WITH STREAMS *)
(* ******************** *)

(* stream_prefix function and its unfolding lemmas: *)
(* {STREAM_PREFIX} *)
Fixpoint stream_prefix (V : Type) (s : stream V) (n : nat) : list V :=
  match n with
  | 0 => nil
  | S n' => match s with
            | Cons _ v s' => v :: (stream_prefix V s' n')
            end
  end.
(* {END} *)

Lemma fold_unfold_stream_prefix_0 :
  forall (V : Type) (s : stream V),
    stream_prefix V s 0 = nil.
Proof.
  fold_unfold_tactic stream_prefix.
Qed.

Lemma fold_unfold_stream_prefix_S :
  forall (V : Type) (v : V) (s' : stream V) (n' : nat),
    stream_prefix V (Cons V v s') (S n') =
      v :: (stream_prefix V s' n').
Proof.
  fold_unfold_tactic stream_prefix.
Qed.

(* ********** *)

(* stream_index function and its unfolding lemmas: *)
(* {STREAM_INDEX} *)
Fixpoint stream_index (V : Type) (s : stream V) (n : nat) : V :=
  match n with
  | O    => match s with
            | Cons _ v s' => v
            end
  | S n' => match s with
            | Cons _ v s' => stream_index V s' n'
            end
  end.
(* {END} *)

Lemma fold_unfold_stream_index_O :
  forall (V : Type) (s : stream V),
    stream_index V s 0 =
      match s with
      | Cons _ v s' => v
      end.
Proof.
  fold_unfold_tactic stream_index.
Qed.

Lemma fold_unfold_stream_index_S :
  forall (V : Type) (s : stream V) (n' : nat),
    stream_index V s (S n') =
      match s with
        Cons _ v s' => stream_index V s' n'
      end.
Proof.
  fold_unfold_tactic stream_index.
Qed.

(* ********** *)

(* stream_map function *)
(* {MAP} *)
CoFixpoint map (V : Type) (f : V -> V) (s : stream V) : stream V :=
  match s with Cons _ v s' => Cons V (f v) (map V f s') end.
(* {END} *)

(* {FOLD_UNFOLD_MAP} *)
Lemma fold_unfold_map : forall (V : Type) (f : V -> V) (v : V) (s' : stream V),
    map V f (Cons V v s') = Cons V (f v) (map V f s').
(* {END} *)
Proof.
  intros.
  rewrite -> (stream_decomposition V (map V f (Cons V v s'))).
  unfold stream_decompose.
  unfold map; fold map.
  reflexivity.
Qed.


(* relevant streams and their fold-unfold lemmas *)
(* {ONES} *)
CoFixpoint ones : stream nat := Cons nat 1 ones.
(* {END} *)

Lemma fold_unfold_ones :
  ones = Cons nat 1 ones.
Proof.
  rewrite -> (stream_decomposition nat ones) at 1.
  unfold_and_fold ones.
  reflexivity.
Qed.

(* {NATS} *)
CoFixpoint nats_aux (i : nat) : stream nat := Cons nat i (nats_aux (S i)).

Definition nats : stream nat := nats_aux 0.
(* {END} *)

(* {FOLD_UNFOLD_NATS_AUX} *)
Lemma fold_unfold_nats_aux : forall (i : nat), nats_aux i = Cons nat i (nats_aux (S i)).
(* {END} *)
Proof.
  intros.
  rewrite -> (stream_decomposition nat (nats_aux i)).
  unfold_and_fold nats_aux.
  reflexivity.
Qed.  

(* {POSINTS} *)
Definition posints : stream nat := nats_aux 1.
(* {END} *)

(* ********** *)
(* END OF REASONING WITH STREAMS *)

(* ************************************************************ *)

(* ******************** *)
(* STREAM EQUALITY (BISIMILARITY) AND PARAMETERIZED COINDUCTION *)
(* ******************** *)

(* example of an intuitive definition of stream equality *)

(* {BISIMILAR} *)
CoInductive bisimilar : forall V : Type, (V -> V -> Prop) -> stream V -> stream V -> Prop :=
| Bisimilar :
    forall (V : Type) (eq_V : V -> V -> Prop) (v1 v2 : V) (v1s v2s : stream V),
    eq_V v1 v2 ->
    bisimilar V eq_V v1s v2s ->
    bisimilar V eq_V (Cons V v1 v1s) (Cons V v2 v2s).
(* {END} *)

(* generative step in stream equality *)
(* {SEQ_GEN} *)
Inductive seq_gen (seq : stream nat -> stream nat -> Prop) : stream nat -> stream nat -> Prop :=
| _seq_gen : forall n s1 s2 (R : seq s1 s2 : Prop), seq_gen seq (Cons nat n s1) (Cons nat n s2).
#[export] Hint Constructors seq_gen : core.
(* {END} *)

(* main stream equality (bisimilarity) relation *)
(* {SEQ} *)
CoInductive seq : stream nat -> stream nat -> Prop :=
| seq_fold : forall s1 s2, seq_gen seq s1 s2 -> seq s1 s2.
(* {END} *)

(* ********** *)

(* {PRACTICE_PROOF_SEQ} *)
Theorem example :
  forall (n : nat), seq (nats_aux n) (Cons nat n (map nat S (nats_aux n))).
Proof.
  cofix coIH; intro n.
  pattern (nats_aux n) at 1. (*Cannot use rewrite ... at 1*)
  rewrite -> stream_decomposition.
  unfold_and_fold nats_aux.
  apply seq_fold; constructor. (* reduce to tails once equal heads *)
  rewrite -> (fold_unfold_nats_aux n).
  rewrite -> fold_unfold_map.
  exact (coIH (S n)).
Qed.  
(* {END} *)

(* ********** *)

(* parameterized stream equality using paco2 *)
(* {SEQ'} *)
Definition seq' (s1 s2 : stream nat) := paco2 seq_gen bot2 s1 s2.
#[export] Hint Unfold seq' : core.
(* {END} *)

(* prove paco2 requirement of the relation monotonicity *)

Lemma seq_gen_mon:
  monotone2 seq_gen.
Proof.
  pmonauto.
Qed.
#[export] Hint Resolve seq_gen_mon : paco.

(* seq' implies equality of heads and seq' of tails  *)

(* {SEQ'_CONS} *)
Theorem seq'_cons :
  forall (n1 n2 : nat)
         (s1 s2 : stream nat)
         (seq_n1_s1_n2_s2 : seq' (Cons nat n1 s1) (Cons nat n2 s2)),
    n1 = n2 /\ seq' s1 s2.
(* {END} *)
Proof.
  intros.
  punfold seq_n1_s1_n2_s2.
  inversion_clear seq_n1_s1_n2_s2.
  pclearbot.
  auto.
Qed.

(* equality of heads and seq' of tails implies seq'  *)

Theorem seq'_cons_rev :
  forall (n1 n2 : nat)
         (s1 s2 : stream nat),
    n1 = n2 /\ seq' s1 s2 ->
    seq' (Cons nat n1 s1) (Cons nat n2 s2).
Proof.
  pcofix coIH.
  intros.
  rewrite -> H0.
  pfold; constructor; right.
  case s1 as [x1 s1'].
  case s2 as [x2 s2'].
  destruct (seq'_cons x1 x2 s1' s2' H1) as [eq_x1_x2 bs_s1'_s2'].
  exact (coIH x1 x2 s1' s2' eq_x1_x2 bs_s1'_s2').
Qed.  

(* practice proof using parameterized coinduction *)

(* {EXAMPLE_PROOF_SEQ'} *)
Theorem example' :
  forall (n : nat), seq' (nats_aux n) (Cons nat n (map nat S (nats_aux n))).
Proof.
  pcofix coIH; intro n.
  rewrite -> fold_unfold_nats_aux at 1.
  pfold; constructor; right. (* reduce to tails once equal heads *)
  rewrite -> (fold_unfold_nats_aux n).
  rewrite -> fold_unfold_map.
  exact (coIH (S n)).
Qed.
(* {END} *)

(* ********** *)
(* END OF STREAM EQUALITY (BISIMILARITY) AND PARAMETERIZED COINDUCTION *)

(* ************************************************************ *)

(* ******************** *)
(* REASONING ABOUT STREAM EQUALITY *)
(* ******************** *)

Lemma seq'_is_reflexive :
  forall xs : stream nat,
    seq' xs xs.
Proof.
  pcofix coIH.
  intros [x xs'].
  pfold; constructor; right.
  exact (coIH xs').
Qed.


Lemma seq'_is_symmetric :
  forall xs ys : stream nat,
    seq' xs ys ->
    seq' ys xs.
Proof.
  pcofix coIH.
  intros [x xs'] [y ys'] seq'_xs_ys.
  destruct (seq'_cons x y xs' ys' seq'_xs_ys) as [eq_y_x seq'_xs'_ys'].
  rewrite -> eq_y_x.
  pfold; constructor; right.
  exact (coIH xs' ys' seq'_xs'_ys').
Qed.  


Lemma seq'_is_transitive :
  forall xs ys zs : stream nat,
    seq' xs ys ->
    seq' ys zs ->
    seq' xs zs.
Proof.
  pcofix coIH.
  intros [x xs'] [y ys'] [z zs'] seq'_xs_ys seq'_ys_zs.
  destruct (seq'_cons x y xs' ys' seq'_xs_ys) as [eq_x_y seq'_xs'_ys']; clear seq'_xs_ys.
  destruct (seq'_cons y z ys' zs' seq'_ys_zs) as [eq_y_z seq'_ys'_zs']; clear seq'_ys_zs.
  rewrite -> eq_x_y, eq_y_z.
  pfold; constructor; right.
  exact (coIH xs' ys' zs' seq'_xs'_ys' seq'_ys'_zs').
Qed.  

(* ********** *)
(* END OF REASONING ABOUT STREAM EQUALITY *)

(* ************************************************************ *)

(* ******************** *)
(* GENERALIZED PARAMETERISED COINDUCTION *)
(* ******************** *)

(* establish transitive closure *)

Variant seqTC (r : stream nat -> stream nat -> Prop)
  : stream nat -> stream nat -> Prop :=
| seqTC_intro s1 s1' s2 s2'
      (EQl: seq' s1 s1')
      (EQr: seq' s2 s2')
      (REL: r s1' s2')
  : seqTC r s1 s2
.

(* prove paco2 requirement of the relation monotonicity *)

Lemma seqTC_mon :
  forall (r1 r2 : stream nat -> stream nat -> Prop)
         (s1 s2 : stream nat)
         (IN: seqTC r1 s1 s2)
         (LE: r1 <2= r2),
  seqTC r2 s1 s2.
Proof.
  intros.
  destruct IN.
  econstructor; eauto.
Qed.
Hint Resolve seqTC_mon : paco.

(* relation (seq_gen) is compatible with a coinductive predicate (seqTC) if using this function or relation in the context of this predicate does not lead one out of the domain of the predicate. *)
(* this condition is established in paco's compatible2 *)
(* compatibility is a sufficient condition to establish the validity of the up-to principle. *)
(* hence, show that seq_gen compatible with seq_TC *)

Lemma seqTC_compat:
  compatible2 seq_gen seqTC.
Proof.
  econstructor; eauto with paco.
  (*   forall (r : rel2 (stream nat) (fun _ : stream nat => stream nat)) (x0 x1 : stream nat),
       seqTC (seq_gen r) x0 x1 -> seq_gen (seqTC r) x0 x1 *)
  intros ? s1 s2 H.
  inversion_clear H.
  punfold EQl; inversion EQl.
  punfold EQr; inversion EQr.
  inversion REL.
  subst.
  inversion H3; inversion H4; subst.
  constructor.
  pclearbot.
  econstructor; eauto.
Qed.

(* weak compatibility is sufficient for paco *)

Lemma seqTC_wcompat:
  wcompatible2 seq_gen seqTC.
Proof.
  apply compat2_wcompat; eauto with paco; apply seqTC_compat.
Qed.
Hint Resolve seqTC_wcompat : paco.

(* up-to reflexivity *)

#[global] Instance Reflexive_seq_gen f (r rg: stream nat -> stream nat -> Prop) :
  Reflexive (gpaco2 seq_gen f r rg).
Proof.
  gcofix CoIH. gstep; intros.
  destruct x; constructor.
  eauto with paco.
Qed.

(* seq' is reflexive *)

#[global] Instance Reflexive_seq :
  Reflexive seq'.
Proof.
  intro.
  ginit.
  apply Reflexive_seq_gen.
Qed.

Lemma seq_seq_gen :
  forall (r rg: stream nat -> stream nat -> Prop) s1 s2 t1 t2,
    seq' s1 s2 -> seq' t1 t2 ->
    gpaco2 seq_gen seqTC r rg s1 t1 ->
    gpaco2 seq_gen seqTC r rg s2 t2.
Proof.
  intros r rg s1 s2 t1 t2 Hseq_s1_s2 Hseq_t1_t2 Hgpaco_s1_t1.
  gclo; econstructor; eauto.
  - exact (seq'_is_symmetric s1 s2 Hseq_s1_s2).
  - exact (seq'_is_symmetric t1 t2 Hseq_t1_t2).
Qed.

(*
From Coq Require Import Morphisms.
(* So in particular seq_gen is reflexive *)
#[global] Instance seq_seq_gen (r rg: stream nat -> stream nat -> Prop) :
  Proper (seq' ==> seq' ==> flip impl) (gpaco2 seq_gen seqTC r rg).
Proof.
  intros ?? EQ1 ?? EQ2 EQ3.
  gclo; econstructor; eauto.
Qed.
*)

(* ************************************************************ *)
(* **************************PERRON**************************** *)
(* ************************************************************ *)

(* ******************** *)
(* MOESSNER'S PROCESS AND RELEVANT FUNCTIONS FOR PERRON *)
(* ******************** *)

(* strike_out function, its auxiliary and its unfold lemmas *)

(* {STRIKE_OUT_AUX} *)
CoFixpoint strike_out_aux (k counter : nat) (s : stream nat) : stream nat :=
  match s with Cons _ x s' =>
                 match counter with
                 | O => match s' with Cons _ x' s'' =>
                                        Cons nat x' (strike_out_aux k k s'')
                        end
                 | S counter' => Cons nat x (strike_out_aux k counter' s')
                 end
  end.
(* {END} *)

Lemma unfold_strike_out_aux_0 :
  forall (k' x x' : nat) (s'' : stream nat),
    strike_out_aux k' 0 (Cons nat x (Cons nat x' s'')) =
    Cons nat x' (strike_out_aux k' k' s'').
Proof.
  intros k' x x' s''.
  rewrite -> (stream_decomposition nat (strike_out_aux k' 0 (Cons nat x (Cons nat x' s'')))).
  unfold_and_fold strike_out_aux.
  reflexivity.
Qed.

Lemma unfold_strike_out_aux_S :
  forall (k counter' x : nat) (s' : stream nat),
    strike_out_aux k (S counter') (Cons nat x s') =
    Cons nat x (strike_out_aux k counter' s').
Proof.
  intros k counter' x s'.
  rewrite -> (stream_decomposition nat (strike_out_aux k (S counter') (Cons nat x s'))).
  unfold_and_fold strike_out_aux.
  reflexivity.
Qed.

(* *** *)

(* {STRIKE_OUT} *)
Definition strike_out (k : nat) (s : stream nat) : stream nat :=
  match k with
  | O    => s   (* vacuously returns s *)
  | S k' =>   (* filters out every element with the column indexed with k *)
      match s with Cons _ x s' => Cons nat x (strike_out_aux k' k' s') end
  end.
(* {END} *)

(* {STRIKE_OUT_SK} *)
Definition strike_out_Sk (k : nat) (s : stream nat) : stream nat :=
  match k with
  | O | S O   => s   (* vacuously returns s *)
  | S (S k'') =>   (* filters out every element with the column indexed with k *)
      match s with
      | Cons _ x s' => Cons nat x (strike_out_aux k'' k'' s')
      end
  end.
(* {END} *)

Compute (stream_prefix nat (strike_out 2 posints) 10).

Lemma unfold_strike_out :
  forall (k' x : nat) (s' : stream nat),
    strike_out (S k') (Cons nat x s') = Cons nat x (strike_out_aux k' k' s').
Proof.
  intros k' x s'.
  unfold strike_out.
  reflexivity.
Qed.

Lemma fold_strike_out_aux_0 :
  forall (k' x : nat) (s' : stream nat),
    strike_out_aux k' 0 (Cons nat x s') = strike_out (S k') s'.
Proof.
  intros k' x s'.
  rewrite -> (stream_decomposition nat s') at 1.
  destruct s' as [x' s''].
  unfold stream_decompose.
  rewrite -> unfold_strike_out_aux_0.
  rewrite -> unfold_strike_out.
  reflexivity.
Qed.

(* partial_sums function, its auxiliary and its unfold lemma *)
(* {PARTIAL_SUMS_AUX} *)
CoFixpoint partial_sums_aux (a : nat) (s : stream nat) : stream nat :=
  match s with Cons _ x s' => Cons nat a (partial_sums_aux (x + a) s') end.
(* {END} *)

Lemma fold_unfold_partial_sums_aux :
  forall (a x : nat)
         (s' : stream nat),
    partial_sums_aux a (Cons nat x s') =
    Cons nat a (partial_sums_aux (x + a) s').
Proof.
  intros a x s'.
  rewrite -> (stream_decomposition
                nat
                (partial_sums_aux a (Cons nat x s'))).
  unfold stream_decompose.
  unfold partial_sums_aux;
    fold partial_sums_aux.
  reflexivity.
Qed.

(* {PARTIAL_SUMS} *)
Definition partial_sums (s : stream nat) : stream nat :=
  match s with Cons _ x s' => partial_sums_aux x s' end.
(* {END} *)

(* We can define Moessner's process, yet we are more interested in Perron's process *)
(* {MOESSNER'_STEP} *)
Definition Moessner'_step (k : nat) (s : stream nat) :=
  match k with
  | O      => s
  | (S k') => partial_sums (strike_out (S k') s)
  end.
(* {END} *)

(* {MOESSNER'_AUX} *)
Fixpoint Moessner'_aux (k : nat) (s : stream nat) :=
  match k with
  | O    => Moessner'_step 0 s
  | S k' => Moessner'_aux k' (Moessner'_step (S k') s)
  end.
(* {END} *)

(* {MOESSNER} *)
Definition Moessner' (rank : nat) :=
  Moessner'_aux rank posints.
(* {END} *)

(* {MOESSNER_TEST} *)
Compute (stream_prefix nat (Moessner' 0) 5). (* = 1 :: 2 :: 3 :: 4 :: 5 :: nil *)
Compute (stream_prefix nat (Moessner' 1) 5). (* = 1 :: 4 :: 9 :: 16 :: 25 :: nil *)
Compute (stream_prefix nat (Moessner' 2) 5). (* = 1 :: 8 :: 27 :: 64 :: 125 :: nil *)
Compute (stream_prefix nat (Moessner' 3) 5). (* = 1 :: 16 :: 81 :: 256 :: 625 :: nil *)
(* {END} *)

(* *** *)

(* Perron's process *)
(* {PERRON_STEP} *)
Definition Perron_step (k : nat) (s : stream nat) :=
  strike_out k (partial_sums s).
(* {END} *)

(* Since proof is not adjusted for n ranging from 0, we have 
the following coq adjustment *)

(* {PERRON_STREAM} *)
Fixpoint Perron_stream (n k : nat) (s : stream nat) :=
  match n with
  | O    => strike_out k s
  | S n' => Perron_step (k - (S n')) (Perron_stream n' k s)
  end.
(* {END} *)

Lemma fold_unfold_Perron_stream_O :
  forall (k : nat) (s : stream nat),
    Perron_stream 0 k s = strike_out k s.
Proof.
  fold_unfold_tactic Perron_stream.
Qed.

Lemma fold_unfold_Perron_stream_S :
  forall (n' k : nat) (s : stream nat),
    Perron_stream (S n') k s = Perron_step (k - (S n')) (Perron_stream n' k s).
Proof.
  fold_unfold_tactic Perron_stream.
Qed.

(* {PERRON_STREAM_TEST} *)
Compute (stream_prefix nat (Perron_stream 0 0 posints) 3). (* 1 :: 2 :: 3 :: nil *)
Compute (stream_prefix nat (Perron_stream 0 1 posints) 3). (* 1 :: 3 :: 5 :: nil *)
Compute (stream_prefix nat (Perron_stream 1 2 posints) 3). (* 1 :: 7 :: 19 :: nil *)
Compute (stream_prefix nat (Perron_stream 2 3 posints) 3). (* = 1 :: 15 :: 65 :: nil *)
(* {END} *)


(* ********** *)

(* indexing stream *)

(* {SKIP} *)
Fixpoint skip (V : Type) (s : stream V) (n : nat) : stream V :=
  match n, s with
  | 0, _              => s
  | S n', Cons _ _ s' => skip V s' n'
  end.
(* {END} *)

(* {STREAM_INDEX_2D} *)
Fixpoint stream_index_2d (V : Type) (s : stream V) (row_length row col : nat) : V :=
  match row with
  | O      => stream_index V s col
  | S row' => stream_index_2d V (skip V s row_length) row_length row' col
  end.
(* {END} *)

Lemma fold_unfold_stream_index_2d_O :
  forall (V : Type) (s : stream V) (row_length col : nat),
    stream_index_2d V s row_length 0 col = stream_index V s col.
Proof.
  fold_unfold_tactic stream_index_2d.
Qed.

Lemma fold_unfold_stream_index_2d_S :
  forall (V : Type) (s : stream V) (row_length row' col : nat),
    stream_index_2d V s row_length (S row') col =
    stream_index_2d V (skip V s row_length) row_length row' col.
Proof.
  fold_unfold_tactic stream_index_2d.
Qed.

(* The definition below allows to prove the base case, 
   but conflicts with induction step due to compromizing the restriction on col
*)

Fixpoint stream_index_2d' (V : Type) (s : stream V) (row_length row col : nat) : V :=
  match row with
  | O      => stream_index V s col
  | S row' => stream_index_2d' V s row_length row' (col + row_length) 
  end.

(* ********** *)

(* Perron's lemma formula *)
(* {PERRON_BINOM} *)
Definition Perron_binom (n row col k : nat) :=
  Sigma (S n)
    (fun t =>
       (binomial_coefficient (col + t) t)
       * (binomial_coefficient (S k) (S n - t))
       * (power row (S n-t))
    ).
(* {END} *)

Compute ((Perron_binom 1 0 0 2, Perron_binom 1 1 0 2, Perron_binom 1 2 0 2)).
(*1, 7, 19*)
(* That is, when n=2. k=3, this is the final column before the final partial sums *)
(* that would yield (1, 8, 27) *)

(* ********** *)
(* END OF MOESSNER'S PROCESS AND RELEVANT FUNCTIONS FOR PERRON *)

(* ************************************************************ *)

(* ******************** *)
(* PERRON'S LEMMA *)
(* ******************** *)


Lemma about_strike_out_aux_Sk_k :
  forall (k col i : nat),
    col <= k ->
    stream_index nat (Cons nat (S i) (strike_out_aux k k (nats_aux (S (S i))))) col =
      stream_index nat (Cons nat (S i) (strike_out_aux (S k) k (nats_aux (S (S i))))) col.
Proof.
  intros.
  revert k i H.
  induction col; intros.
  - rewrite -> 2 fold_unfold_stream_index_O.
    reflexivity.
  - rewrite -> 2 fold_unfold_stream_index_S.
    rewrite -> fold_unfold_nats_aux.
    rewrite -> fold_unfold_nats_aux.
    case k as [ | k'].
    + inversion H.
    + rewrite -> 2 unfold_strike_out_aux_S.

      (*
        The fold_unfold lemmas for strike_out are not helpful enough 
       *)

      (*
  col : nat
  IHcol : forall k i : nat,
          col <= k ->
          stream_index nat (Cons nat (S i) (strike_out_aux k k (nats_aux (S (S i))))) col =
          stream_index nat (Cons nat (S i) (strike_out_aux (S k) k (nats_aux (S (S i))))) col
  k', i : nat
  H : S col <= S k'
  ============================
  stream_index nat
    (Cons nat (S (S i))
       (strike_out_aux (S k') k' (Cons nat (S (S (S i))) (nats_aux (S (S (S (S i)))))))) col =
  stream_index nat
    (Cons nat (S (S i))
       (strike_out_aux (S (S k')) k' (Cons nat (S (S (S i))) (nats_aux (S (S (S (S i)))))))) col
       *)
Admitted.

  
Lemma resetting_nats_aux :
  forall (col k i : nat),
    col <= k ->
    stream_index nat (Cons nat i (strike_out_aux k k (nats_aux (S i)))) col = col + i.
Proof.
  Compute (
      let k := 8 in
      let i := 99 in
      let col := 7 in
      stream_index nat (Cons nat i (strike_out_aux k k (nats_aux (S i)))) col = col + i
    ).
  induction col; intros k i H.
  - rewrite -> fold_unfold_stream_index_O.
    rewrite -> Nat.add_0_l.
    reflexivity.
  - rewrite -> fold_unfold_stream_index_S.
    rewrite -> fold_unfold_nats_aux.
    case k as [ | k'] eqn: H_k.
    + inversion H.
    + rewrite -> unfold_strike_out_aux_S.
      Compute (
          let i := 10 in
          let col := 11 in
          let k' := 18 in
          stream_index nat (Cons nat (S i) (strike_out_aux k' k' (nats_aux (S (S i))))) col =
            stream_index nat (Cons nat (S i) (strike_out_aux (S k') k' (nats_aux (S (S i))))) col
        ).
      Check (about_strike_out_aux_Sk_k k' col i (le_S_n col k' H)).
      rewrite <- (about_strike_out_aux_Sk_k k' col i (le_S_n col k' H)).
      Search (S _ + _ = _ + S _).
      rewrite -> Nat.add_succ_comm.
      Check (IHcol k' (S i) (le_S_n col k' H)).
      exact (IHcol k' (S i) (le_S_n col k' H)).
Qed.

Theorem Perron_base_case_lemma :
  forall (row col k : nat),
    1 <= k ->
    col <= k - 1 ->
    stream_index_2d nat (strike_out k posints) k row col = (S k) * row + (col + 1).
Proof.
  Compute (
      let row := 2 in
      let col := 1 in
      let k := 2 in
      stream_index_2d nat (strike_out k posints) k row col = (S k) * row + (col + 1)
    ).          
  intros row col k.
  case k as [ | k'] eqn:H_k.
  - intro H; inversion H.
  - intros le_1_Sk' le_col_k'.
    rewrite -> Nat.sub_succ in le_col_k'.
    rewrite -> Nat.sub_0_r in le_col_k'.
    induction row.
    + rewrite -> fold_unfold_stream_index_2d_O.
      rewrite -> Nat.mul_0_r.
      rewrite -> Nat.add_0_l.
      (* GOAL: stream_index nat (strike_out (S k') posints) col = col + 1 *)
      unfold posints.
      rewrite -> fold_unfold_nats_aux.
      rewrite -> unfold_strike_out.
      Check (resetting_nats_aux col k' 1 le_col_k').
      exact (resetting_nats_aux col k' 1 le_col_k').
    + { admit .}        

Admitted.
      
      
(* {PERRON_LEMMA} *)
Theorem Perron_lemma :
  forall (n k row col : nat),
    1 <= k ->
    n <= k - 1 ->
    col <= k - n - 1 ->
    stream_index_2d nat (Perron_stream n k posints) (k-n) row col =
      Perron_binom n row col k.
(* {END} *)
Proof.
  Compute (
      let k := 2 in
      let n := 0 in
      let row := 2 in
      let col := 1 in
      stream_index_2d nat (Perron_stream n k posints) (k-n) row col =
      Perron_binom n row col k
    ).
  Proof.
    induction n as [ | n' IHn']; intros k row col le_1_k le_n_k_minus_1 le_col_k_minus_n_minus_1.
    - unfold Perron_binom.
      rewrite -> fold_unfold_Sigma_S.
      rewrite -> fold_unfold_Sigma_O.
      simpl (1-1).
      rewrite -> 2 about_binomial_coefficients_n_0.
      rewrite -> 2 Nat.sub_0_r.
      rewrite -> Nat.mul_1_l.
      rewrite -> about_binomial_coefficients_n_S0.
      rewrite -> unfold_power_O.
      rewrite -> unfold_power_S.
      rewrite -> fold_unfold_power_aux_O.
      rewrite -> 2 Nat.mul_1_r.
      rewrite -> about_binomial_coefficients_n_S0.
      (* RHS READY *)
      rewrite -> fold_unfold_Perron_stream_O.
      rewrite -> Nat.sub_0_r in le_col_k_minus_n_minus_1.
      (* {PERRON_LEMMA_BASE_CASE_GOAL} *)

      (* {END} *)

        
        Check (Perron_base_case_lemma row col k le_1_k le_col_k_minus_n_minus_1).
        exact (Perron_base_case_lemma row col k le_1_k le_col_k_minus_n_minus_1).
    - 

Abort.


(* ***** *)
(* ALTERNATIVES? *)

(* 
   The question is: how to construct posints in the way that is relatable to our functions? 
 *)


(* 
   take k, then subdivide? or just modify stream_index, row, col
 *)

(* {A} *)
Fixpoint A (n k row col : nat) :=
  match n with
  | O    => (S k) * row + (S col)
  | S n' => match row with
            | O      => Sigma col (fun j => A n' k 0 j)
            | S row' =>
                Sigma row' (fun i => Sigma (k - n' - 1) (fun j => A n' k i j))
                + (Sigma col (fun j => A n' k (S row') j))
            end
  end.
(* {END} *)


Lemma fold_unfold_A_O :
  forall (k row col : nat),
    A 0 k row col = (S k) * row + (S col).
Proof.
  fold_unfold_tactic A.
Qed.

Lemma fold_unfold_A_S :
  forall (n' k row col : nat),
    A (S n') k row col =
            match row with
      | O => Sigma col (fun j => A n' k 0 j)
      | S row' =>
          Sigma row' (fun i => Sigma (k - n' - 1) (fun j => A n' k i j)) + (Sigma col (fun j => A n' k (S row') j))
      end.
Proof.
  fold_unfold_tactic A.
Qed.


Compute (A 0 0 0 0).
Compute (A 0 1 0 0).
Compute (A 0 1 0 1).
Compute (A 0 1 1 0).
Compute (A 0 1 1 1).

Compute (A 0 2 0 0).
Compute (A 0 2 0 1).
Compute (A 0 2 1 0).
Compute (A 0 2 1 1).
Compute (A 0 2 2 0).
Compute (A 0 2 2 1).

Compute (A 1 2 0 0).
Compute (A 1 2 1 0).
Compute (A 1 2 2 0).


Lemma about_power_0_in_Sigma :
  forall (n col k : nat),
    Sigma (S n)
      (fun t : nat =>
         binomial_coefficient (col + t) t * binomial_coefficient (S k) (S n - t) *
           power 0 (S n - t))
      = Sigma (S n) (fun t : nat => 0).
Proof.

Admitted.

Lemma about_empty_sum :
  forall (n : nat),
    Sigma n (fun j : nat => 0) = 0.
Proof.
Admitted.

Lemma about_summation_of_binomial_coefficients :
  forall (m t : nat),
    Sigma m (fun j => binomial_coefficient (j + t) t) = binomial_coefficient (m + S t) (S t).
Admitted.

Lemma binomial_identity_1 :
  forall (n k t : nat),
    t <= S n -> S (S n) <= k ->
    binomial_coefficient (S k) (S n - t) * binomial_coefficient (k - n + t) (S t) =
      binomial_coefficient (S k) (S (S n)) * binomial_coefficient (S (S n)) (S t).
Proof.
  Compute (
      let n := 3 in
      let k := 5 in
      let t := 2 in
      binomial_coefficient (S k) (S n - t) * binomial_coefficient (k - n + t) (S t) =
        binomial_coefficient (S k) (S (S n)) * binomial_coefficient (S (S n)) (S t)
    ).
  intros.
  Check (fold_unfold_binomial_coefficient_S).
Admitted.

Lemma binomial_identity_2 :
  forall (n i : nat),
    Sigma (S n) (fun t => binomial_coefficient (S (S n)) (S t) * (power i (S n - t))) =
      power (S i) (S (S n)) - power i (S (S n)).
Proof.
Admitted.


Lemma telescoping_sums :
  forall (x n : nat),
    Sigma x (fun i : nat => power (S i) (S n) - power i (S n)) =
      power (S x) (S n).
Proof.
  Compute (
      let x := 3 in
      let n := 3 in
    Sigma x (fun i : nat => power (S i) (S n) - power i (S n)) =
      power (S x) (S n)
    ).
Admitted.

(* {PERRON_LEMMA'} *)
Theorem Perron_lemma' :
  forall (n k row col : nat),
    1 <= k ->
    n <= k - 1 ->
    col <= k - n - 1 ->
    A n k row col =
      Perron_binom n row col k.
(* {END} *)
Proof.
  Compute (
      let k := 2 in
      let n := 0 in
      let row := 2 in
      let col := 1 in
    A n k row col =
      Perron_binom n row col k
    ).
  Proof.
    induction n as [ | n' IHn']; intros k row col le_1_k le_n_k_minus_1 le_col_k_minus_n_minus_1.
    - unfold Perron_binom.
      rewrite -> fold_unfold_Sigma_S.
      rewrite -> fold_unfold_Sigma_O.
      simpl (1-1).
      rewrite -> 2 about_binomial_coefficients_n_0.
      rewrite -> Nat.sub_0_r.
      rewrite -> Nat.mul_1_l.
      rewrite -> about_binomial_coefficients_n_S0.
      rewrite -> unfold_power_O.
      rewrite -> unfold_power_S.
      rewrite -> fold_unfold_power_aux_O.
      rewrite -> 2 Nat.mul_1_r.
      rewrite -> about_binomial_coefficients_n_S0.
      (* RHS READY *)
      rewrite -> fold_unfold_A_O.
      rewrite -> Nat.add_1_r.
      reflexivity.
    - assert (le_n'_k_minus_1 : n' <= k - 1).
      { admit. }
      assert (le_col_k_minus_n'_minus_1 : col <= k - n' - 1).
      { admit. }
      assert (sum_eq1 :
               forall (row : nat),
                 Sigma col (fun j : nat => A n' k row j) =
                   Sigma col (fun j : nat => Perron_binom n' row j k)
             ).
      {
        intros row'.
        apply (about_Sigma_with_two_equivalent_functions_up_to_the_bound
                 col
                 (fun j : nat => A n' k row' j)
                 (fun j : nat => Perron_binom n' row' j k)
              ).
        intros j le_j_col.
        Check (Nat.le_trans j col (k-n'-1) le_j_col le_col_k_minus_n'_minus_1).
        exact (IHn' k row' j le_1_k le_n'_k_minus_1 (Nat.le_trans j col (k-n'-1) le_j_col le_col_k_minus_n'_minus_1)).
      }

      case row as [ | row'].
      + rewrite -> fold_unfold_A_S.

        rewrite -> sum_eq1.
        unfold Perron_binom.
        Check (about_power_0_in_Sigma).
        Check (about_power_0_in_Sigma (S n') col k).
        rewrite -> (about_power_0_in_Sigma (S n') col k).
        assert (sum_eq2 :
                 (Sigma col
                    (fun j : nat =>
                       Sigma (S n')
                         (fun t : nat =>
                            binomial_coefficient (j + t) t * binomial_coefficient (S k) (S n' - t) * power 0 (S n' - t)))) = (Sigma col (fun j : nat => 0))
               ).
        {
          apply (about_Sigma_with_two_equivalent_functions_up_to_the_bound
                   col
                   (fun j : nat =>
                       Sigma (S n')
                         (fun t : nat =>
                            binomial_coefficient (j + t) t * binomial_coefficient (S k) (S n' - t) * power 0 (S n' - t)))
                   (fun j : nat => 0)
                ).
          intros j le_j_col.
          rewrite -> about_power_0_in_Sigma.
          rewrite -> about_empty_sum.
          reflexivity.
        }
        rewrite -> sum_eq2.
        rewrite -> 2 about_empty_sum.
        reflexivity.
      + rewrite -> fold_unfold_A_S.
        rewrite -> sum_eq1.
        assert (sum_eq3 :
                 Sigma row' (fun i : nat => Sigma (k - n' - 1) (fun j : nat => A n' k i j)) =
                   Sigma row' (fun i : nat => Sigma (k - n' - 1) (fun j : nat => Perron_binom n' i j k))
               ).
        {
          apply (about_Sigma_with_two_equivalent_functions_up_to_the_bound
                  row'
                    (fun i : nat => Sigma (k - n' - 1) (fun j : nat => A n' k i j))
                    (fun i : nat => Sigma (k - n' - 1) (fun j : nat => Perron_binom n' i j k))
                ).
          intros i le_i_row'.
          apply (about_Sigma_with_two_equivalent_functions_up_to_the_bound
                   (k - n' - 1)
                   (fun j : nat => A n' k i j)
                   (fun j : nat => Perron_binom n' i j k)
                ).
          intros j le_j_k_minus_n'_minus_1.
          Check (IHn' k i j le_1_k le_n'_k_minus_1 le_j_k_minus_n'_minus_1).
          exact (IHn' k i j le_1_k le_n'_k_minus_1 le_j_k_minus_n'_minus_1).          
        }
        rewrite -> sum_eq3.
        unfold Perron_binom.
        (* INDUCTION ARGUMENT BEGINS *)

        (* FIRST REORDER SUMS *)
        assert (reorder :
                 forall (i : nat),
                   Sigma (k - n' - 1)
                     (fun j : nat =>
                        Sigma (S n')
                          (fun t : nat =>
                             binomial_coefficient (j + t) t * binomial_coefficient (S k) (S n' - t) *
                               power i (S n' - t)))
                   =
                     Sigma (S n') (fun t : nat => binomial_coefficient (S k) (S n' - t) * (power i (S n' - t)) * (binomial_coefficient (k - n' + t) (S t)))
               ).
        {
          intro i.
          rewrite -> (about_swapping_Sigma (k-n'-1) (S n') (fun j t => binomial_coefficient (j + t) t * binomial_coefficient (S k) (S n' - t) * power i (S n' - t))).
          Check (about_mult_assoc_in_Sigma).
          assert (assoc_in_double_Sigma :
                   Sigma (S n')
                     (fun j : nat =>
                        Sigma (k - n' - 1)
                          (fun i0 : nat =>
                             binomial_coefficient (i0 + j) j * binomial_coefficient (S k) (S n' - j) * power i (S n' - j))) =
                          Sigma (S n')
                            (fun j : nat =>
                               Sigma (k - n' - 1)
                                 (fun i0 : nat =>
                                    binomial_coefficient (i0 + j) j * (binomial_coefficient (S k) (S n' - j) * power i (S n' - j))))
                 ).
          {
            apply (about_Sigma_with_two_equivalent_functions
                     (S n')
                     (fun j : nat =>
                        Sigma (k - n' - 1)
                          (fun i0 : nat =>
                             binomial_coefficient (i0 + j) j * binomial_coefficient (S k) (S n' - j) * power i (S n' - j)))
                     (fun j : nat =>
                        Sigma (k - n' - 1)
                          (fun i0 : nat =>
                             binomial_coefficient (i0 + j) j * (binomial_coefficient (S k) (S n' - j) * power i (S n' - j))))
                     ).
            intros i0.
            exact (about_mult_assoc_in_Sigma (k - n' - 1)
                     (fun i1 => binomial_coefficient (i1 + i0) i0)
                     (fun i1 => binomial_coefficient (S k) (S n' - i0))
                     (fun i1 => power i (S n' - i0))
                  ).          
          }
          rewrite -> assoc_in_double_Sigma; clear assoc_in_double_Sigma. 
          rewrite -> (about_factoring_a_function_on_the_right_in_double_Sigma (S n') (k - n' - 1)
                   (fun j => binomial_coefficient (S k) (S n' - j) * power i (S n' - j))
                   (fun i0 j => binomial_coefficient (i0 + j) j)
                ).
          (* Need the up to m lemma *)
          Check (about_summation_of_binomial_coefficients (k -n' -1)).
          assert (sum_binom_identity :
                   Sigma (S n')
                     (fun j : nat =>
                        Sigma (k - n' - 1) (fun i0 : nat => binomial_coefficient (i0 + j) j) *
                          (binomial_coefficient (S k) (S n' - j) * power i (S n' - j)))
                   =
                     Sigma (S n')
                       (fun j : nat =>
                          binomial_coefficient (k - n' - 1 + S j) (S j) *
                            (binomial_coefficient (S k) (S n' - j) * power i (S n' - j)))
                 ).
          {
            apply (about_Sigma_with_two_equivalent_functions (S n')
                      (fun j : nat =>
                         Sigma (k - n' - 1) (fun i0 : nat => binomial_coefficient (i0 + j) j) *
                           (binomial_coefficient (S k) (S n' - j) * power i (S n' - j)))
                      (fun j : nat =>
                         binomial_coefficient (k - n' - 1 + S j) (S j) *
                           (binomial_coefficient (S k) (S n' - j) * power i (S n' - j)))
                   ).
            intros.
            rewrite -> (about_summation_of_binomial_coefficients (k -n' -1) i0).
            reflexivity.
          }
          rewrite -> sum_binom_identity; clear sum_binom_identity.
          assert (ly :
                   Sigma (S n')
                     (fun t : nat =>
                        binomial_coefficient (k - n' - 1 + S t) (S t) *
                          (binomial_coefficient (S k) (S n' - t) * power i (S n' - t))) =
                     Sigma (S n')
                       (fun t : nat =>
                          binomial_coefficient (S k) (S n' - t) * power i (S n' - t) *
                            binomial_coefficient (k - n' + t) (S t))).
          {
            apply (about_Sigma_with_two_equivalent_functions_up_to_the_bound (S n')
                     (fun t : nat =>
                        binomial_coefficient (k - n' - 1 + S t) (S t) *
                          (binomial_coefficient (S k) (S n' - t) * power i (S n' - t)))                                          (fun t : nat => binomial_coefficient (S k) (S n' - t) * power i (S n' - t) * binomial_coefficient (k - n' + t) (S t))).        
            intros t le_t_Sn'.
            rewrite -> Nat.mul_comm.
            rewrite -> (Nat.add_comm (k - n' - 1) (S t)).
            assert (manipulation : S t + (k - n' - 1) = k - n' + t).
            { admit. }
            rewrite -> manipulation.
            reflexivity.
          }
          exact ly.
        } 
        rewrite -> (about_Sigma_with_two_equivalent_functions
                 row'
                 (fun i : nat =>
                    Sigma (k - n' - 1)
                      (fun j : nat =>
                         Sigma (S n')
                           (fun t : nat =>
                              binomial_coefficient (j + t) t * binomial_coefficient (S k) (S n' - t) *
                                power i (S n' - t))))
                 (fun i : nat =>
                    Sigma (S n')
                      (fun t : nat =>
                         binomial_coefficient (S k) (S n' - t) * power i (S n' - t) *
                           binomial_coefficient (k - n' + t) (S t)))
                 reorder
              ).
        clear reorder.
        assert (binom_ident_2 : 
            forall i : nat,
              Sigma (S n')
                (fun t : nat =>
                   binomial_coefficient (S k) (S n' - t) * power i (S n' - t) *
                     binomial_coefficient (k - n' + t) (S t)) =
                  Sigma (S n')
                    (fun t : nat =>
                       binomial_coefficient (S k) (S (S n'))
                       * binomial_coefficient (S (S n')) (S t)
                       * power i (S n' - t)
                    )
          ).
        {
          intro i.
          apply (about_Sigma_with_two_equivalent_functions_up_to_the_bound (S n')
                   (fun t : nat =>
                      binomial_coefficient (S k) (S n' - t) * power i (S n' - t) *
                        binomial_coefficient (k - n' + t) (S t))
                   (fun t : nat =>
                      binomial_coefficient (S k) (S (S n')) * binomial_coefficient (S (S n')) (S t) *
                        power i (S n' - t))
                ).
          intros t le_t_Sn'.
          rewrite -> Nat.mul_shuffle0.
          assert (le_SSn'_k : S (S n') <= k).
          { admit. }
          Check (binomial_identity_1 n' k t le_t_Sn' le_SSn'_k).
          rewrite -> (binomial_identity_1 n' k t le_t_Sn' le_SSn'_k).
          reflexivity.
        }
        rewrite -> (about_Sigma_with_two_equivalent_functions row'
                 (fun i : nat =>
                    Sigma (S n')
                      (fun t : nat =>
                         binomial_coefficient (S k) (S n' - t) * power i (S n' - t) *
                           binomial_coefficient (k - n' + t) (S t)))
                 (fun i : nat =>
                    Sigma (S n')
                      (fun t : nat =>
                         binomial_coefficient (S k) (S (S n')) * binomial_coefficient (S (S n')) (S t) * power i (S n' - t)))
                 binom_ident_2
              ).
        clear binom_ident_2.
        rewrite -> (about_mult_assoc_in_double_Sigma row' (S n')
                 (fun t i => binomial_coefficient (S k) (S (S n')))
                 (fun t i => binomial_coefficient (S (S n')) (S t))
                 (fun t i => power i (S n' - t))
              ).
        rewrite -> (about_factoring_a_function_on_the_left_in_double_Sigma row' (S n')
                 (fun t => binomial_coefficient (S k) (S (S n')))
                 (fun t i => binomial_coefficient (S (S n')) (S t) *
        power i (S n' - t))
              ).
        rewrite -> (about_factoring_a_multiplicative_constant_on_the_left_in_Sigma row'
                 (binomial_coefficient (S k) (S (S n')))
                 (fun j => Sigma (S n') (fun i : nat => binomial_coefficient (S (S n')) (S i) * power j (S n' - i)))
          ).
        rewrite -> (about_Sigma_with_two_equivalent_functions row'
                 (fun j : nat =>
                    Sigma (S n') (fun i : nat => binomial_coefficient (S (S n')) (S i) * power j (S n' - i)))
                 (fun i => power (S i) (S (S n')) - power i (S (S n')))
                 (binomial_identity_2 n')
          ).
        rewrite -> (telescoping_sums row' (S n')).
        rewrite -> (about_swapping_Sigma col (S n')
                 (fun j t => binomial_coefficient (j + t) t * binomial_coefficient (S k) (S n' - t) *
        power (S row') (S n' - t))
          ).
        rewrite -> (about_mult_assoc_in_double_Sigma (S n') col
                 (fun i j => binomial_coefficient (i + j) j)
                 (fun i j => binomial_coefficient (S k) (S n' - j))
                 (fun i j => power (S row') (S n' - j))
          ).

        rewrite -> (about_factoring_a_function_on_the_right_in_double_Sigma (S n') col
                 (fun j => (binomial_coefficient (S k) (S n' - j) * power (S row') (S n' - j)))
                 (fun i j => binomial_coefficient (i + j) j)
              ).
        assert (sum_eq :
                 Sigma (S n')
                   (fun j : nat =>
                      Sigma col (fun i : nat => binomial_coefficient (i + j) j) *
                        (binomial_coefficient (S k) (S n' - j) * power (S row') (S n' - j))) =
                   Sigma (S n')
                     (fun j : nat =>
                        binomial_coefficient (col + S j) (S j) *
                          (binomial_coefficient (S k) (S n' - j) * power (S row') (S n' - j)))
               ).
        {
          apply (about_Sigma_with_two_equivalent_functions
                   (S n')
                   (fun j : nat =>
                      Sigma col (fun i : nat => binomial_coefficient (i + j) j) *
                        (binomial_coefficient (S k) (S n' - j) * power (S row') (S n' - j)))
                   (fun j : nat =>
                        binomial_coefficient (col + S j) (S j) *
                          (binomial_coefficient (S k) (S n' - j) * power (S row') (S n' - j)))
                ).
          intros.
          rewrite -> about_summation_of_binomial_coefficients.
          reflexivity.
        }
        rewrite -> sum_eq; clear sum_eq.
        assert (sum_eq_mining_term :
                 binomial_coefficient (col + 0) 0 *
                   (binomial_coefficient (S k) (S (S n') - 0) * power (S row') (S (S n') - 0)) +
                   Sigma (S n')
                     (fun i : nat =>
                        binomial_coefficient (col + S i) (S i) *
                          (binomial_coefficient (S k) (S (S n') - S i) * power (S row') (S (S n') - S i))) =
                   Sigma (S (S n'))
                     (fun i : nat =>
                        binomial_coefficient (col + i) i *
                          (binomial_coefficient (S k) (S (S n') - i) * power (S row') (S (S n') - i)))
               ).
        {
          exact (about_mining_term (S n')
                 (fun j : nat =>
                    binomial_coefficient (col + j) j *
                      (binomial_coefficient (S k) (S (S n') - j) * power (S row') (S (S n') - j)))
                ).
        }
        rewrite -> about_binomial_coefficients_n_0 in sum_eq_mining_term.
        rewrite -> Nat.sub_0_r in sum_eq_mining_term.
        rewrite -> Nat.mul_1_l in sum_eq_mining_term.
        assert (sum_eq :
                   Sigma (S n')
                     (fun j : nat =>
                        binomial_coefficient (col + S j) (S j) *
                          (binomial_coefficient (S k) (S n' - j) * power (S row') (S n' - j)))
                   =
                     Sigma (S n')
                       (fun j : nat =>
                          binomial_coefficient (col + S j) (S j) *
                            (binomial_coefficient (S k) (S (S n') - S j) * power (S row') (S (S n') - S j)))
               ).
        {
          apply (about_Sigma_with_two_equivalent_functions (S n')
                   (fun j : nat =>
                      binomial_coefficient (col + S j) (S j) *
                        (binomial_coefficient (S k) (S n' - j) * power (S row') (S n' - j)))
                   (fun j : nat =>
                      binomial_coefficient (col + S j) (S j) *
                        (binomial_coefficient (S k) (S (S n') - S j) * power (S row') (S (S n') - S j))) 
                ).
          intro i.
          rewrite -> Nat.sub_succ; reflexivity.
        }
        rewrite -> sum_eq; clear sum_eq.
        rewrite -> (about_mult_assoc_in_Sigma (S (S n'))
                 (fun t => binomial_coefficient (col + t) t)
                 (fun t => binomial_coefficient (S k) (S (S n') - t))
                 (fun t => power (S row') (S (S n') - t))
              ).
        exact sum_eq_mining_term.
Admitted.




(* ************************************************************ *)
(* *********MOESSNER'S PROCESS WITHOUT STRIKING OUT************ *)
(* ************************************************************ *)

(* ******************** *)
(* MOESSNER'S PROCESS WITHOUT STRIKING OUT AND RELEVANT FUNCTIONS *)
(* ******************** *)

(* the function of the process without striking out and its unfold lemma *)
(* {PARTIAL_SUMS_K} *)  
Fixpoint partial_sums_k (k : nat) (s : stream nat) : stream nat :=
  match k with
  | O    => partial_sums s
  | S k' => partial_sums (partial_sums_k k' s)
  end.
(* {END} *)

Compute (stream_prefix nat (partial_sums_k 0 posints) 10).
Compute (stream_prefix nat (partial_sums_k 1 posints) 10).
Compute (stream_prefix nat (partial_sums_k 2 posints) 10).
Compute (stream_prefix nat (partial_sums_k 3 posints) 10).


Lemma fold_unfold_partial_sums_k_O :
  forall s : stream nat,
    partial_sums_k 0 s =
    partial_sums s.
Proof.
  fold_unfold_tactic partial_sums_k.
Qed.


Lemma fold_unfold_partial_sums_k_S :
  forall (k' : nat)
         (s : stream nat),
    partial_sums_k (S k') s =
    partial_sums (partial_sums_k k' s).
Proof.
  fold_unfold_tactic partial_sums_k.
Qed.

(* ********** *)

(* binomial coefficient formula from the theorem's RHS *)
(* {BCS_K_I} *)
Definition bcs_k_i (k i : nat) (s : stream nat) : nat :=
  Sigma i (fun j => (binomial_coefficient (k + i - j) (i - j)) * (stream_index nat s j)).
(* {END} *)
(* *** *)

Lemma about_bcs_k_0 :
  forall (k : nat)
         (s : stream nat),
    bcs_k_i k 0 s = stream_index nat s 0.
Proof.
  intros k s.
  unfold bcs_k_i.
  rewrite -> fold_unfold_Sigma_O.
  rewrite -> 2Nat.sub_0_r.
  rewrite -> about_binomial_coefficients_n_0.
  rewrite -> Nat.mul_1_l.
  reflexivity.
Qed.
  
(* *** *)

Lemma about_bcs_0_i :
  forall (i : nat)
         (s : stream nat),
    bcs_k_i 0 i s = Sigma i (fun j : nat => stream_index nat s j).
Proof.
  intros i s.
  unfold bcs_k_i.
  rewrite (Nat.add_0_l i).
  apply (about_Sigma_with_two_equivalent_functions_up_to_the_bound
           i
           (fun j : nat => binomial_coefficient (i - j) (i - j) * stream_index nat s j)
           (fun j : nat => stream_index nat s j)
        ).
  intros j le_j_i.
  rewrite -> (about_binomial_coefficients_n_n (i-j)).
  rewrite -> Nat.mul_1_l.
  reflexivity.
Qed.

(* the corresponding stream of binomial coefficients *)
(* {BCS_K_STREAM} *)
CoFixpoint bcs_k_i_stream (k i : nat) (s : stream nat) : stream nat :=
  Cons nat (bcs_k_i k i s) (bcs_k_i_stream k (S i) s).

Definition bcs_k_stream (k : nat) (s : stream nat) : stream nat :=
  bcs_k_i_stream k 0 s.
(* {END} *)

Compute (let k := 0 in
         let s := ones in
         (stream_prefix nat (bcs_k_stream k s) 5, stream_prefix nat (partial_sums_k k s) 5)).
Compute (let k := 1 in
         let s := ones in
         (stream_prefix nat (bcs_k_stream k s) 5, stream_prefix nat (partial_sums_k k s) 5)).

Lemma fold_unfold_bcs_k_i_stream :
  forall (k i : nat)
         (s : stream nat),
    bcs_k_i_stream k i s = Cons nat (bcs_k_i k i s) (bcs_k_i_stream k (S i) s).
Proof.
  intros k i s.
  rewrite -> (stream_decomposition nat (bcs_k_i_stream k i s)).
  unfold stream_decompose.
  unfold bcs_k_i_stream; fold bcs_k_i_stream.
  reflexivity.
Qed.


(* ********** *)
(* END OF MOESSNER'S PROCESS WITHOUT STRIKING OUT AND RELEVANT FUNCTIONS *)

(* ************************************************************ *)

(* ******************** *)
(* INDUCTION PROOF *)
(* ******************** *)

(* {ABOUT_PASCAL_IDENTITY_IN_SIGMA} *)
Lemma about_pascal_identity_in_Sigma :
  forall (k i : nat)
         (s : stream nat),
    Sigma i 
      (fun j : nat => binomial_coefficient (S (k + S i - j)) (S (i - j)) * stream_index nat s j)
    =
      Sigma i (fun j : nat =>
                  binomial_coefficient (S k + i - j) (i - j) * stream_index nat s j +
                    binomial_coefficient (k + S i - j) (S i - j) * stream_index nat s j).
(* {END} *)
Proof.
  intros k i s.
  apply (about_Sigma_with_two_equivalent_functions_up_to_the_bound
           i
           (fun j : nat => binomial_coefficient (S (k + S i - j)) (S (i - j)) * stream_index nat s j)
           (fun j : nat =>
              binomial_coefficient (S k + i - j) (i - j) * stream_index nat s j +
                binomial_coefficient (k + S i - j) (S i - j) * stream_index nat s j)
        ).
  intros j le_j_i.
  rewrite -> (pascals_identity (k + S i - j) (i - j)).
  rewrite -> Nat.mul_add_distr_r.
  rewrite -> (Nat.add_succ_comm k i).
  rewrite -> (Nat.sub_succ_l j i le_j_i).
  reflexivity.
Qed.

(* {ABOUT_STREAM_INDEX_SI_AND_SSI} *)
Lemma about_stream_index_Si_and_SSi :
  forall (i a b x : nat)
         (s : stream nat),
  stream_index nat (Cons nat a s) (S i) =
    stream_index nat (Cons nat b (Cons nat x s)) (S (S i)).
(* {END} *)
Proof.
  induction i as [ | i' IHi']; intros a b x [x' s'].
  - rewrite -> 2fold_unfold_stream_index_S.
    rewrite -> fold_unfold_stream_index_S.
    rewrite -> fold_unfold_stream_index_O.
    reflexivity.
  - rewrite -> (fold_unfold_stream_index_S nat (Cons nat a (Cons nat x' s')) (S i')).
    rewrite -> (fold_unfold_stream_index_S nat (Cons nat b (Cons nat x (Cons nat x' s'))) (S (S i'))).
    Check (IHi' x' x x' s').
    exact (IHi' x' x x' s').
Qed.

(* {ABOUT_SIGMA_I_AND_SI_OF_TWO_STREAMS} *)   
Lemma about_Sigma_i_and_Si_of_two_streams :
  forall (i a x : nat) (s : stream nat),
    Sigma i (fun j : nat => stream_index nat (Cons nat (x + a) s) j) =
      Sigma (S i) (fun j : nat => stream_index nat (Cons nat a (Cons nat x s)) j).
(* {END} *)
Proof.
  induction i as [ | i' IHi']; intros a x s.
  - rewrite -> fold_unfold_Sigma_S.
    rewrite -> 2fold_unfold_Sigma_O.
    rewrite -> fold_unfold_stream_index_S.
    rewrite -> 3fold_unfold_stream_index_O.
    rewrite -> Nat.add_comm.
    reflexivity.
  - rewrite -> 2fold_unfold_Sigma_S.
    Check (about_stream_index_Si_and_SSi i' (x + a) a x s).
    rewrite -> (about_stream_index_Si_and_SSi i' (x + a) a x s).
    Check (IHi' a x s).
    rewrite -> (IHi' a x s).
    reflexivity.
Qed.

(* {BASE_CASE_LEMMA_IND} *)
Lemma base_case_lemma_ind :
  forall (i a : nat) (s : stream nat),
    stream_index nat (partial_sums_aux a s) i =
      Sigma i (fun j : nat => stream_index nat (Cons nat a s) j).
(* {END} *)
Proof.
  induction i as [ | i' IHi']; intros a [x s'].
  - rewrite -> fold_unfold_partial_sums_aux.
    rewrite -> fold_unfold_stream_index_O.
    rewrite -> fold_unfold_Sigma_O.
    rewrite -> fold_unfold_stream_index_O.
    reflexivity.
  - rewrite -> fold_unfold_partial_sums_aux.
    rewrite -> fold_unfold_stream_index_S.
    rewrite -> (IHi' (x + a) s').
    exact (about_Sigma_i_and_Si_of_two_streams i' a x s').
Qed.

(* {ABOUT_PARTIAL_SUMS_AND_SIGMA} *)
Corollary about_partial_sums_and_Sigma :
  forall (i : nat)
         (s : stream nat),
    stream_index nat (partial_sums s) i = Sigma i (fun j => stream_index nat s j).
(* {END} *)
Proof.
  intros i [x s'].
  unfold partial_sums.
  exact (base_case_lemma_ind i x s').
Qed.

(* {RECURSIVE_DEFINITION_AS_SUMMATION_OF_BCS_K_I} *)
Lemma recursive_definition_as_summation_of_bcs_k_i :
  forall (i k : nat) (s : stream nat),
    bcs_k_i (S k) i s =
      Sigma i (fun j => bcs_k_i k j s).
(* {END} *)
Proof.
  Compute (
      let i := 3 in
      let k := 2 in
      let s := nats in
      bcs_k_i (S k) i s =
        Sigma i (fun j => bcs_k_i k j s)
    ).
  induction i as [ | i' IHi']; intros k s.
  - rewrite -> fold_unfold_Sigma_O.
    unfold bcs_k_i.
    rewrite -> 2fold_unfold_Sigma_O.
    simpl (0-0).
    rewrite -> 2about_binomial_coefficients_n_0.
    reflexivity.
  - rewrite -> fold_unfold_Sigma_S.
    rewrite <- IHi'.
    unfold bcs_k_i.
    Check (about_pascal_identity_in_Sigma k i' s).
    rewrite -> fold_unfold_Sigma_S.
    Search (_ - _ = _).
    rewrite -> (Nat.sub_diag (S i')).
    rewrite -> about_binomial_coefficients_n_0, Nat.mul_1_l.
    assert (helpful :
             Sigma i' (fun j : nat => binomial_coefficient (S k + S i' - j) (S i' - j) * stream_index nat s j) =
               Sigma i' (fun j : nat => binomial_coefficient (S (k + S i' - j)) (S (i' - j)) * stream_index nat s j)
           ).
    {
      apply (about_Sigma_with_two_equivalent_functions_up_to_the_bound i'
               (fun j : nat => binomial_coefficient (S k + S i' - j) (S i' - j) * stream_index nat s j)
               (fun j : nat => binomial_coefficient (S (k + S i' - j)) (S (i' - j)) * stream_index nat s j)
            ).
      intros j le_j_i'.
      Search (S _ - _ = _).
      rewrite -> (Nat.sub_succ_l j i' le_j_i').
      rewrite -> (Nat.add_succ_l k (S i')).
      Search (_ <= _ -> _ <= _ + _).
      assert (le_j_Si'_plus_k :
               j <= S i' + k
             ).
      { exact (Arith_prebase.le_plus_trans_stt j (S i') k (Nat.le_le_succ_r j i' le_j_i')). }
      rewrite -> Nat.add_comm in le_j_Si'_plus_k.
      rewrite -> (Nat.sub_succ_l
                    j
                    (k + S i')
                    le_j_Si'_plus_k
        ).
      reflexivity.
    }
    rewrite -> helpful.
    rewrite -> (about_pascal_identity_in_Sigma k i' s).
    rewrite -> about_splitting_Sigma_at_plus.
    rewrite -> fold_unfold_Sigma_S.
    rewrite -> (Nat.sub_diag (S i')).
    rewrite -> about_binomial_coefficients_n_0, Nat.mul_1_l.
    rewrite -> Nat.add_assoc.
    reflexivity.
Qed.

(* {MOESSNER_WITHOUT_STRIKING_OUT_IND} *)
Theorem moessner_without_striking_out_v0 :
  forall (k i : nat) (s : stream nat),
    stream_index nat (partial_sums_k k s) i = bcs_k_i k i s.
(* {END} *)
Proof.
  Compute (
      let k := 0 in
      let i := 0 in
      let s := ones in
      stream_index nat (partial_sums_k k s) i = bcs_k_i k i s,
        let k := 1 in
        let i := 1 in
        let s := ones in
        stream_index nat (partial_sums_k k s) i = bcs_k_i k i s,
          let k := 4 in
          let i := 4 in
          let s := ones in
          stream_index nat (partial_sums_k k s) i = bcs_k_i k i s                           
    ).
  induction k as [ | k' IHk']; intros i s.
  - unfold partial_sums_k.
    case s as [x s'].
    unfold partial_sums.
    rewrite -> (about_bcs_0_i).
    exact (base_case_lemma_ind i x s').
  - rewrite -> fold_unfold_partial_sums_k_S.
    rewrite -> (about_partial_sums_and_Sigma i (partial_sums_k k' s)).
    rewrite -> recursive_definition_as_summation_of_bcs_k_i.
    apply (about_Sigma_with_two_equivalent_functions_up_to_the_bound
             i
             (fun j : nat => stream_index nat (partial_sums_k k' s) j)
             (fun j : nat => bcs_k_i k' j s)
          ).
    intros j le_j_i.
    exact (IHk' j s).
Qed.



(* ********** *)
(* END OF INDUCTION PROOF *)

(* ************************************************************ *)

(* ******************** *)
(* COINDUCTION PROOF *)
(* ******************** *)

(* {CONTEXTUAL_KEY} *)
Lemma contextual_key :
  forall xs ys zs : stream nat,
    seq' xs ys ->
    seq' (partial_sums ys) zs ->
    seq' (partial_sums xs) zs.
(* {END} *)
Proof.
  pcofix coIH.
  intros [x xs] [y ys] [z zs] H1 H2.
  unfold partial_sums.
  case xs as [x' xs'].
  rewrite -> fold_unfold_partial_sums_aux.
  unfold partial_sums in H2.
  case ys as [y' ys'].
  rewrite -> fold_unfold_partial_sums_aux in H2.

  destruct (seq'_cons x y (Cons nat x' xs') (Cons nat y' ys') H1) as [eq_x_y bs_xs_ys]; clear H1.
  destruct (seq'_cons x' y' xs' ys' bs_xs_ys) as [eq_x'_y' bs_xs'_ys']; clear bs_xs_ys.
  destruct (seq'_cons y z (partial_sums_aux (y' + y) ys') zs H2) as [eq_y_z bs_ps_ys'_zs]; clear H2.
  rewrite -> eq_x_y, eq_y_z at 1.
  pfold.
  constructor.
  Check (coIH (Cons nat (x' + x) xs') (Cons nat (y' + y) ys') zs).
  
  assert (pacoIH :
           seq' (Cons nat (x' + x) xs') (Cons nat (y' + y) ys') ->
           seq' (partial_sums (Cons nat (y' + y) ys')) zs ->
           r (partial_sums (Cons nat (x' + x) xs')) zs
         ).

  { exact (coIH (Cons nat (x' + x) xs') (Cons nat (y' + y) ys') zs). }

  unfold partial_sums in pacoIH.

  right.
  apply pacoIH.
  - rewrite -> eq_x_y, eq_x'_y'.
    pfold.
    constructor.
    punfold bs_xs'_ys'.
  - exact (bs_ps_ys'_zs).
Qed.

(* {ABOUT_SUMMATION_OF_A_STREAM_THAT_STARTS_WITH_A_SUM} *)
Lemma about_summation_of_a_stream_that_starts_with_a_sum :
  forall (i a x : nat)
         (s : stream nat),
    (Sigma i (fun j : nat => stream_index nat (Cons nat a (Cons nat x s)) j) +
       stream_index nat (Cons nat a (Cons nat x s)) (S i))
    =
      (Sigma i (fun j : nat => stream_index nat (Cons nat (a + x) s) j)).
(* {END} *)
Proof.     
  intro i.
  induction i as [ | i' IHi']; intros a x s.
  - rewrite -> 2fold_unfold_Sigma_O.
    rewrite -> 2fold_unfold_stream_index_O.
    rewrite -> fold_unfold_stream_index_S.
    rewrite -> fold_unfold_stream_index_O.
    reflexivity.
  - rewrite -> 2fold_unfold_Sigma_S.
    rewrite -> IHi'.
    rewrite -> (fold_unfold_stream_index_S nat (Cons nat a (Cons nat x s)) (S i')).
    rewrite -> (fold_unfold_stream_index_S nat (Cons nat (a + x) s) i').
    rewrite -> (fold_unfold_stream_index_S nat (Cons nat x s) i').
    reflexivity.
Qed.

(* {ABOUT_BCS_K_I_STREAM_SUMMATION} *)
Lemma about_bcs_k_i_stream_summation :
  forall (a x i : nat)
         (s : stream nat),
    seq'
      (bcs_k_i_stream 0 i (Cons nat (a + x) s))
      (bcs_k_i_stream 0 (S i) (Cons nat a (Cons nat x s))).
(* {END} *)
Proof.
  Compute (
      let a := 10 in
      let x := 5 in
      let i := 3 in
      let s := ones in
      stream_prefix nat (bcs_k_i_stream 0 (S i) (Cons nat a (Cons nat x s))) 5
      =
        stream_prefix nat (bcs_k_i_stream 0 i (Cons nat (x + a) s)) 5
    ).
  intros a x.
  rewrite -> (Nat.add_comm a x).
  revert a x.
  pcofix coIH.
  intros a x i s.
  Check (fold_unfold_bcs_k_i_stream).
  rewrite -> (fold_unfold_bcs_k_i_stream 0 (S i) (Cons nat a (Cons nat x s))).
  rewrite -> (fold_unfold_bcs_k_i_stream 0 i (Cons nat (x + a) s)).
  rewrite -> about_bcs_0_i.
  rewrite -> about_bcs_0_i.
  rewrite -> fold_unfold_Sigma_S.
  rewrite -> about_summation_of_a_stream_that_starts_with_a_sum.
  rewrite -> (Nat.add_comm a x).
  pfold; constructor; right.
  exact (coIH a x (S i) s).
Qed.



Lemma about_Sigma_and_S_in_binomial_coefficient :
  forall (i k : nat) (s : stream nat),
    Sigma i
      (fun j : nat => binomial_coefficient (S (k + S i) - j) (S i - j) * stream_index nat s j)
    =
      Sigma i
        (fun j : nat => binomial_coefficient (S ((k + S i) - j)) (S (i - j)) * stream_index nat s j).
Proof.
  intros i k s.
  apply (about_Sigma_with_two_equivalent_functions_up_to_the_bound
           i
           (fun j : nat => binomial_coefficient (S (k + S i) - j) (S i - j) * stream_index nat s j)
           (fun j : nat => binomial_coefficient (S ((k + S i) - j)) (S (i - j)) * stream_index nat s j)
        ).  
  intros j le_j_i.
  rewrite -> (Nat.sub_succ_l j i le_j_i).
  rewrite -> (Nat.add_comm k (S i)).
  rewrite -> (Nat.add_succ_comm i k).
  rewrite -> (Nat.sub_succ_l j (i + S k) (le_plus_trans j i (S k) le_j_i)).
  reflexivity.
Qed.

(* {ABOUT_SUM_AND_DOUBLE_SUM_OF_BCS_K_I} *)
Lemma about_sum_and_double_sum_of_bcs_k_i :
  forall (k i : nat) (s : stream nat),
    bcs_k_i (S k) i s = Sigma i (fun j : nat => bcs_k_i k j s).
(* {END} *)
Proof.
  unfold bcs_k_i.
  intro k.
  induction i as [ | i' IHi']; intro s.
  - rewrite -> 2fold_unfold_Sigma_O.
    rewrite -> fold_unfold_Sigma_O.
    simpl (0-0).
    rewrite -> 2about_binomial_coefficients_n_0.
    rewrite -> Nat.mul_1_l.
    reflexivity.
  - rewrite -> fold_unfold_Sigma_S.
    rewrite -> fold_unfold_Sigma_S.
    rewrite -> (Nat.sub_diag (S i')).
    rewrite -> about_binomial_coefficients_n_0.
    rewrite -> Nat.mul_1_l.
    rewrite -> fold_unfold_Sigma_S.
    rewrite -> (Nat.sub_diag (S i')).
    rewrite -> about_binomial_coefficients_n_0.
    rewrite -> Nat.mul_1_l.
    rewrite <- (IHi' s).
    rewrite -> (Nat.add_succ_l k (S i')).
    rewrite -> about_Sigma_and_S_in_binomial_coefficient.
    rewrite -> about_pascal_identity_in_Sigma.
    rewrite -> (about_splitting_Sigma_at_plus
             i'
             (fun j => binomial_coefficient (S k + i' - j) (i' - j) * stream_index nat s j)
             (fun j => binomial_coefficient (k + S i' - j) (S i' - j) * stream_index nat s j)
          ).
    rewrite -> Nat.add_assoc.
    reflexivity.
Qed.

    
Lemma about_Sigma_S_i :
  forall (k i : nat) (s : stream nat),
    bcs_k_i k (S i) s + Sigma i (fun j : nat => bcs_k_i k j s)
    = 
      Sigma (S i) (fun j : nat => bcs_k_i k j s).
Proof.        
  intros k i s.
  rewrite -> (Nat.add_comm (bcs_k_i k (S i) s) (Sigma i (fun j : nat => bcs_k_i k j s))). 
  rewrite <- (fold_unfold_Sigma_S i (fun j : nat => bcs_k_i k j s)).
  reflexivity.
Qed.


(* ********** *)
(* END OF USEFUL LEMMAS FOR SUPERMOESSNER *)



(* MAIN LEMMA RESETTING THE ACCUMULATOR PACO *)
(* {ABOUT_PARTIAL_SUMS_AUX_AND_BCS_K_I} *)
Lemma about_partial_sums_aux_and_bcs_k_i :
  forall (k i : nat) (s : stream nat),
    seq'
      (bcs_k_i_stream (S k) i s)
      (partial_sums_aux (Sigma i (fun j => bcs_k_i k j s)) (bcs_k_i_stream k (S i) s)).
(* {END} *)
Proof.
  Compute (
      let k := 5 in
      let i := 4 in
      let s := ones in
      stream_prefix nat (bcs_k_i_stream (S k) i s) 5 =
        stream_prefix nat (partial_sums_aux (Sigma i (fun j => bcs_k_i k j s)) (bcs_k_i_stream k (S i) s)) 5
    ).
  pcofix coIH.
  intros k i s.
  (* get 1st element on the left out *)
  rewrite -> (fold_unfold_bcs_k_i_stream (S k) i s).

  (* get 1st element on the right out *)
  rewrite -> (fold_unfold_bcs_k_i_stream k (S i) s).
  rewrite -> (fold_unfold_partial_sums_aux
                (Sigma i (fun j : nat => bcs_k_i k j s))
                (bcs_k_i k (S i) s)
                (bcs_k_i_stream k (S (S i)) s)
    ).
  (*
    LHS 1st: (bcs_k_i (S k) i s)
    RHS 1st: (Sigma i (fun j : nat => bcs_k_i k j s))
   *)

  (* Have a lemma for it *)
  rewrite -> about_sum_and_double_sum_of_bcs_k_i.

  pfold. constructor. right.

  (* WTS: 
     Sigma i (fun j : nat => bcs_k_i k j s) + (bcs_k_i k (S i) s 
     = 
     Sigma (S i) (fun j : nat => bcs_k_i k j s)
   *)

  Compute (
      let i := 5 in
      let k := 3 in
      let s := ones in
      Sigma i (fun j : nat => bcs_k_i k j s) +  bcs_k_i k (S i) s 
      = 
        Sigma (S i) (fun j : nat => bcs_k_i k j s)
    ).
  (* Have a lemma for it *)
  rewrite -> about_Sigma_S_i.
  exact (coIH k (S i) s).
Qed.


(* Corollary of the lemma above *)
(* {ABOUT_PARTIAL_SUMS_AUX_AND_BCS_K_I_FOR_0} *)
Corollary about_partial_sums_aux_and_bcs_k_i_for_0 :
  forall (k : nat) (s : stream nat),
    seq' (bcs_k_i_stream (S k) 0 s) (partial_sums_aux (bcs_k_i k 0 s) (bcs_k_i_stream k 1 s)).
(* {END} *)
Proof.
  intros k s.
  assert (H_i : seq'
                  (bcs_k_i_stream (S k) 0 s)
                  (partial_sums_aux (Sigma 0 (fun j => bcs_k_i k j s)) (bcs_k_i_stream k (S 0) s))
         ).
  { exact (about_partial_sums_aux_and_bcs_k_i k 0 s). }
  rewrite -> fold_unfold_Sigma_O in H_i.
  exact H_i.
Qed.



(* BASE CASE LEMMA PACO *)

(*
Lemma base_case_lemma_aux :
  forall (i : nat)
         (xs : stream nat),
    bisimilar nat Nat.eq
      (partial_sums_aux (Sigma i (fun j => stream_index nat xs j)) (stream_tail nat xs (S i)))
      (bcs_n_i_stream 0 i xs).
Admitted.
*)

(* {BASE_CASE_LEMMA_GPACO} *)  
Lemma base_case_lemma_gpaco :
  forall (a : nat) (s : stream nat),
    seq' (partial_sums_aux a s) (bcs_k_i_stream 0 0 (Cons nat a s)).
(* {END} *)
Proof.
  Compute (
      let a := 4 in
      let s := ones in
      stream_prefix nat (partial_sums_aux a s) 5 = stream_prefix nat (bcs_k_i_stream 0 0 (Cons nat a s)) 5
    ).
  ginit.
  gcofix coIH. 
  intros a s.
  rewrite fold_unfold_bcs_k_i_stream.
  destruct s as [x s'] eqn: H_s.
  rewrite -> fold_unfold_partial_sums_aux.
  Check (about_bcs_0_i).
  rewrite -> about_bcs_0_i.
  rewrite -> fold_unfold_Sigma_O.
  Check (fold_unfold_stream_index_O).
  rewrite -> (fold_unfold_stream_index_O).
  Check (about_partial_sums_aux_and_bcs_k_i). 

  gstep; constructor.

  gclo. econstructor.
  
  Check (about_bcs_k_i_stream_summation a x 0 s').
  reflexivity.
  assert (needed :
           seq'
             (bcs_k_i_stream 0 0 (Cons nat (a + x) s'))
             (bcs_k_i_stream 0 1 (Cons nat a (Cons nat x s')))
         ).
  {
    Check (about_bcs_k_i_stream_summation a x 0 s').
    exact (about_bcs_k_i_stream_summation a x 0 s').
  }
  rewrite -> Nat.add_comm in needed.
  apply (
      seq'_is_symmetric
        (bcs_k_i_stream 0 0 (Cons nat (x + a) s'))
        (bcs_k_i_stream 0 1 (Cons nat a (Cons nat x s')))
        needed
    ).
  gbase.
  exact (coIH (x + a) s').
Qed.


(* {INDUCTION_STEP_LEMMA} *)
Lemma induction_step_lemma :
  forall (k : nat) (s : stream nat),
    seq' (partial_sums (bcs_k_i_stream k 0 s)) (bcs_k_i_stream (S k) 0 s).
(* {END} *)
Proof.
  Compute (
      let k := 5 in
      let s := ones in
      stream_prefix nat (bcs_k_i_stream (S k) 0 s) 5 = stream_prefix nat (partial_sums (bcs_k_i_stream k 0 s)) 5
    ).
  
  (* NEED TO GET THE FIRST ELEMENT OUT *)
  
  unfold partial_sums.
  case s as [x s'] eqn:H_s.
  rewrite -> (fold_unfold_bcs_k_i_stream k 0 (Cons nat x s')).
  rewrite <- H_s.
  exact (seq'_is_symmetric
           (bcs_k_i_stream (S k) 0 s)
           (partial_sums_aux (bcs_k_i k 0 s) (bcs_k_i_stream k 1 s))
           (about_partial_sums_aux_and_bcs_k_i_for_0 k s)
        ).
Qed.

(* {ABOUT_BS_PS_BCS_AND_PS_PARTIAL_SUMS_K} *)
Lemma about_bs_ps_bcs_and_ps_partial_sums_k :
  forall (k : nat) (s : stream nat),
    seq' (partial_sums_k k s) (bcs_k_i_stream k 0 s) ->
    seq' (partial_sums (bcs_k_i_stream k 0 s)) (partial_sums (partial_sums_k k s)).
(* {END} *)
Proof.
  intros k s bs_partial_sums_k_bcs_k_i.  
  exact (seq'_is_symmetric
           (partial_sums (partial_sums_k k s))
           (partial_sums (bcs_k_i_stream k 0 s))
           (contextual_key
              (partial_sums_k k s)
              (bcs_k_i_stream k 0 s)
              (partial_sums (bcs_k_i_stream k 0 s))
              (bs_partial_sums_k_bcs_k_i)
              (seq'_is_reflexive (partial_sums (bcs_k_i_stream k 0 s)))
           )
        ).
Qed.


(* MAIN THEOREM *)
(* {MOESSNER_WITHOUT_STRIKING_OUT_COIND} *)
Theorem moessner_without_striking_out_v1 :
  forall (k : nat) (s : stream nat),
    seq' (partial_sums_k k s) (bcs_k_stream k s).
(* {END} *)
Proof.
  Compute (
      let k := 0 in
      let s := ones in
      stream_prefix nat (partial_sums_k k s) 5 = stream_prefix nat (bcs_k_stream k s) 5,
        let k := 1 in
        let s := ones in
        stream_prefix nat (partial_sums_k k s) 5 = stream_prefix nat (bcs_k_stream k s) 5,
          let k := 4 in
          let s := ones in
          stream_prefix nat (partial_sums_k k s) 5 = stream_prefix nat (bcs_k_stream k s) 5
    ).
  unfold bcs_k_stream.
  intro k.
  induction k as [ | k' IHk']; intro s.
  - rewrite -> fold_unfold_partial_sums_k_O.
    unfold partial_sums.
    case s as [x s'].
    exact (base_case_lemma_gpaco x s').

  (* INDUCTION STEP *)  
  - rewrite -> fold_unfold_partial_sums_k_S.
    exact (seq'_is_transitive
             (partial_sums (partial_sums_k k' s))
             (partial_sums (bcs_k_i_stream k' 0 s))
             (bcs_k_i_stream (S k') 0 s)
             (
               seq'_is_symmetric
                 (partial_sums (bcs_k_i_stream k' 0 s))
                 (partial_sums (partial_sums_k k' s))
                 (about_bs_ps_bcs_and_ps_partial_sums_k k' s (IHk' s))
             )
             (induction_step_lemma k' s)
          ).
Qed.


    




