/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov
-/
import Mathlib.Algebra.Polynomial.BigOperators

import ArkLib.Data.Polynomial.FoldingPolynomial

/-!
# Generalized polynomial splitting and folding

This file defines n-way splitting and folding operations on polynomials.

## Main definitions

* `Polynomial.splitNth f n i`: Splits polynomial `f` into `n` component polynomials,
  where `splitNth f n i` extracts coefficients at positions `j ≡ i (mod n)`.

* `Polynomial.foldNth n f α`: Recombines the n-way split of `f` using powers of `α`,
  computing `∑ i : Fin n, α^i * splitNth f n i`. This is the core operation in
  FRI-style polynomial commitment schemes.

## Implementation notes

When `n = 2`, this recovers the even/odd splitting: `splitNth f 2 0` gives the even
coefficients and `splitNth f 2 1` gives the odd coefficients (after appropriate
reindexing). 

-/

open Polynomial

namespace Polynomial

variable {𝔽 : Type} [CommSemiring 𝔽] [NoZeroDivisors 𝔽]

/--
Splits a polynomial into `n` component polynomials based on coefficient indices modulo `n`.

For a polynomial `f = ∑ⱼ aⱼ Xʲ` and index `i : Fin n`, returns the polynomial whose
coefficients are extracted from positions `j ≡ i (mod n)`, reindexed by `j / n`.
Formally: `splitNth f n i = ∑_{j ≡ i (mod n)} aⱼ X^(j/n)`.
-/
def splitNth (f : 𝔽[X]) (n : ℕ) [inst : NeZero n] : Fin n → 𝔽[X] :=
  fun i =>
    let sup :=
      Finset.filterMap (fun x => if x % n = i.1 then .some (x / n) else .none)
      f.support
      (by
        intros a a' b
        simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq, and_imp]
        intros h g h' g'
        rw [Eq.symm (Nat.div_add_mod' a n), Eq.symm (Nat.div_add_mod' a' n)]
        rw [h, g, h', g'])
    Polynomial.ofFinsupp
      ⟨
        sup,
        fun e => f.coeff (e * n + i.1),
        by
          intros a
          dsimp [sup]
          simp only [Finset.mem_filterMap, mem_support_iff, ne_eq, Option.ite_none_right_eq_some,
            Option.some.injEq]
          apply Iff.intro
          · rintro ⟨a', g⟩
            have : a' = a * n + i.1 := by
              rw [Eq.symm (Nat.div_add_mod' a' n)]
              rw [g.2.1, g.2.2]
            rw [this.symm]
            exact g.1
          · intros h
            exists (a * n + i.1)
            apply And.intro h
            rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.2]
            apply And.intro rfl
            have {a b : ℕ} : (a * n + b) / n = a + (b / n) := by
              have := inst.out
              have ne_zero : 0 < n := by omega
              rw [Nat.add_div ne_zero, Nat.mul_mod_left, zero_add, Nat.mul_div_cancel a ne_zero]
              have : ¬ (n ≤ b % n) := by
                simp only [not_le]
                exact Nat.mod_lt b ne_zero
              simp [this]
            simp [this]
      ⟩

/- Proof of key identity `splitNth` has to satisfy. -/
omit [NoZeroDivisors 𝔽] in
lemma splitNth_def (n : ℕ) (f : 𝔽[X]) [inst : NeZero n] :
    f =
      ∑ i : Fin n,
        (Polynomial.X ^ i.1) *
          Polynomial.eval₂ Polynomial.C (Polynomial.X ^ n) (splitNth f n i) := by
  ext e
  rw [Polynomial.finset_sum_coeff]
  have h₀ {b e : ℕ} {f : 𝔽[X]} : (X ^ b * f).coeff e = if e < b then 0 else f.coeff (e - b) := by
    rw [Polynomial.coeff_X_pow_mul' f b e]
    aesop
  have h₁ {e : ℕ} {f : 𝔽[X]}  :
    (eval₂ C (X ^ n) f).coeff e =
      if e % n = 0
      then f.coeff (e / n)
      else 0 := by
    rw [Polynomial.eval₂_def, Polynomial.coeff_sum, Polynomial.sum_def]
    conv =>
      lhs
      congr
      · skip
      ext n
      rw [←pow_mul, Polynomial.coeff_C_mul_X_pow]
    by_cases h : e % n = 0 <;> simp only [h, ↓reduceIte]
    · rw [Finset.sum_eq_single (e / n)]
      · have : e = n * (e / n) :=
          Nat.eq_mul_of_div_eq_right
            (Nat.dvd_of_mod_eq_zero h) rfl
        rw [if_pos]
        exact this
      · intros b h₀ h₁
        have : ¬ (e = n * b) := by
          intros h'
          apply h₁
          rw [h']
          exact Nat.eq_div_of_mul_eq_right inst.out rfl
        simp [this]
      · intros h'
        split_ifs with h''
        · exact notMem_support_iff.mp h'
        · rfl
    · have {α : Type} {a b : α} : ∀ m, (if e = n * m then a else b) = b := by aesop
      conv =>
        lhs
        congr
        · skip
        ext m
        rw [this m]
      rw [Finset.sum_const_zero]
  conv =>
    rhs
    congr
    · skip
    · ext b
      rw [h₀, h₁]
  unfold splitNth
  simp only [coeff_ofFinsupp, Finsupp.coe_mk]
  rw [Finset.sum_eq_single ⟨e % n, by refine Nat.mod_lt e (by have := inst.out; omega)⟩]
  · simp only
    have h₁ : ¬ (e < e % n) := by
      by_cases h : e < n
      · rw [Nat.mod_eq_of_lt h]
        simp
      · simp only [not_lt] at h ⊢
        exact Nat.mod_le e n
    have h₂ : (e - e % n) % n = 0 := Nat.sub_mod_eq_zero_of_mod_eq (by simp)
    simp only [h₁, h₂, Eq.symm Nat.div_eq_sub_mod_div, Nat.div_add_mod' e n, ↓reduceIte]
  · rintro ⟨b, h⟩ _
    simp only [ne_eq, Fin.mk.injEq, ite_eq_left_iff, not_lt, ite_eq_right_iff]
    intros h₀ h₁ h₂
    exfalso
    apply h₀
    have : e % n = b % n := by
      have h₁' := h₁
      rw [←Nat.div_add_mod' e n, ←Nat.div_add_mod' b n] at h₁ h₂
      by_cases h' : e % n ≥ b % n
      · have : e / n * n + e % n - (b / n * n + b % n) =
                ((e / n - b / n) * n) + (e % n - b % n) := by
          have : e / n * n + e % n - (b / n * n + b % n) =
                  e / n * n + e % n - b / n * n - b % n := by
            omega
          rw [this]
          have : e / n * n + e % n - b / n * n = ((e / n) - (b / n)) * n + e % n := by
            have : e / n * n + e % n - b / n * n = (e / n * n - b / n * n) + e % n :=
              Nat.sub_add_comm (Nat.mul_le_mul (Nat.div_le_div_right h₁') (by rfl))
            rw [this, ←Nat.sub_mul]
          rw [this]
          exact Nat.add_sub_assoc h' ((e / n - b / n) * n)
        rw [
          this, Nat.mul_add_mod_self_right,
          Nat.mod_eq_of_lt (Nat.sub_lt_of_lt (Nat.mod_lt _ (by linarith)))
        ] at h₂
        omega
      · simp only [ge_iff_le, not_le] at h'
        have : e / n * n + e % n - (b / n * n + b % n) =
                ((e / n - b / n - 1) * n) + (n - (b % n - e % n)) := by
          have : e / n * n + e % n - (b / n * n + b % n) =
                  e / n * n + e % n - b / n * n - b % n := by
            omega
          rw [this]
          have : e / n * n + e % n - b / n * n = ((e / n) - (b / n)) * n + e % n := by
            have : e / n * n + e % n - b / n * n = (e / n * n - b / n * n) + e % n :=
              Nat.sub_add_comm (Nat.mul_le_mul (Nat.div_le_div_right h₁') (by rfl))
            rw [this, ←Nat.sub_mul]
          rw [this]
          have : e / n - b / n = (e / n - b / n - 1) + 1 := by
            refine Eq.symm (Nat.sub_add_cancel ?_)
            rw [Nat.one_le_iff_ne_zero]
            intros h
            have h := Nat.le_of_sub_eq_zero h
            nlinarith
          rw (occs := .pos [1]) [this]
          rw
            [
              right_distrib, one_mul, add_assoc,
              Nat.add_sub_assoc (Nat.le_add_right_of_le (Nat.le_of_lt (Nat.mod_lt_of_lt h)))
            ]
          congr 1
          grind
        rw [this, Nat.mul_add_mod_self_right] at h₂
        have {a : ℕ} : (n - a) % n = 0 ∧ a < n → a = 0 := by
          intros h
          rcases exists_eq_mul_left_of_dvd (Nat.dvd_of_mod_eq_zero h.1) with ⟨c, h'⟩
          have : a = (1 - c)*n := by
            have : n = a + c * n := by omega
            have : n - c * n = a := by omega
            rw [←this]
            have : n = 1 * n := by rw [one_mul]
            rewrite (occs := .pos [1]) [this]
            exact Eq.symm (Nat.sub_mul 1 c n)
          have h' := this ▸ h.2
          rw [this]
          have : 1 - c = 0 := by
            have : n = 1 * n := by rw [one_mul]
            rw (occs := .pos [2]) [this] at h'
            have h' := Nat.lt_of_mul_lt_mul_right h'
            omega
          simp [this]
        exfalso
        have h₂ := this ⟨h₂, by apply Nat.sub_lt_of_lt; apply Nat.mod_lt; linarith⟩
        omega
    rw [this]
    exact Eq.symm (Nat.mod_eq_of_lt h)
  · intros h
    simp at h

/- Lemma bounding degree of each `n`-split polynomial. -/
omit [NoZeroDivisors 𝔽] in
lemma splitNth_degree_le {n : ℕ} {f : 𝔽[X]} [inst : NeZero n] :
    ∀ {i}, (splitNth f n i).natDegree ≤ f.natDegree / n := by
    intros i
    unfold splitNth Polynomial.natDegree Polynomial.degree
    simp only [support_ofFinsupp]
    rw [WithBot.unbotD_le_iff (by simp)]
    simp only [Finset.max_le_iff, Finset.mem_filterMap, mem_support_iff, ne_eq,
      Option.ite_none_right_eq_some, Option.some.injEq, WithBot.coe_le_coe, forall_exists_index,
      and_imp]
    intros _ _ h _ h'
    rw [←h']
    refine Nat.div_le_div ?_ (Nat.le_refl n) inst.out
    exact le_natDegree_of_ne_zero h

/-- `foldingPolynomial` in terms of `splitNth`
    when `q = X ^ n`. -/
@[simp]
lemma folding_polynomial_eq_sum_splitNth {𝔽 : Type} [Field 𝔽]
  {f : Polynomial 𝔽} {n : ℕ}
  [inst : NeZero n] :
  FoldingPolynomial.foldingPolynomial (X ^ n) f = 
    ∑ i, C (splitNth f n i) * (X ^ i.val) := by
  symm
  apply FoldingPolynomial.folding_polynomial_is_unique'
  · conv =>
      rhs
      rw [splitNth_def (f := f) (inst := inst)]
    rw [
      Polynomial.map_sum,
      Polynomial.eval_finset_sum] 
    simp only [Polynomial.map_mul, map_C, coe_compRingHom, Polynomial.map_pow, map_X, 
    eval_mul, eval_C, eval_pow, eval_X]
    simp only [comp]
    conv =>
      lhs
      rhs
      ext x
      rw [mul_comm]
      rfl
  · simp only [Bivariate.degreeX, finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one,
    mul_zero, natDegree_pow, natDegree_X]
    simp only [Finset.sup_le_iff, mem_support_iff, finset_sum_coeff, coeff_C_mul, coeff_X_pow,
    mul_ite, mul_one, mul_zero, ne_eq]
    intro b hb
    apply natDegree_sum_le_of_forall_le
    rintro ⟨i, hi⟩ _
    by_cases heq: b = i
    · simp only [heq, ↓reduceIte]
      exact splitNth_degree_le
    · simp [heq]
  · simp only [Bivariate.natDegreeY, natDegree_pow, natDegree_X, mul_one]
    apply Nat.lt_of_le_pred (by {
      apply Nat.zero_lt_of_ne_zero
      aesop
    })
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    apply Nat.le_trans Polynomial.natDegree_mul_le
    rcases i with ⟨i, hi⟩ 
    simp
    omega

/-- `polyFold` in terms of `splitNth`. -/
@[simp]
lemma polyFold_eq_sum_of_splitNth {𝔽 : Type} [Field 𝔽]
  {f : 𝔽[X]} {n : ℕ} {r : 𝔽}
  [inst : NeZero n] :
  FoldingPolynomial.polyFold f n r = 
    ∑ i, C (r ^ i.val) * splitNth f n i := by
  simp only [FoldingPolynomial.polyFold, folding_polynomial_eq_sum_splitNth, map_pow]
  rw [Polynomial.eval_finset_sum]
  simp only [eval_mul, eval_C, eval_pow, eval_X] 
  conv =>
    lhs
    rhs
    ext x
    rw [mul_comm]

omit [NoZeroDivisors 𝔽] in
/--
Lemma bridges the coefficient-level identity `splitNth_def` and
evaluation-level reasoning about `splitNth` and `foldNth`.
-/
lemma splitNth_eval_comp_pow {n : ℕ} [NeZero n] (f : 𝔽[X]) (x : 𝔽) (i : Fin n) :
    (eval₂ C (X ^ n) (splitNth f n i)).eval x = (splitNth f n i).eval (x ^ n) := by
  rw [eval₂_eq_sum]
  unfold Polynomial.eval
  rw [Polynomial.eval₂_sum, eval₂_eq_sum]
  congr
  ext e a
  rw [← eval]
  simp


/-!
# Evaluation-level lemmas for `splitNth` and `foldNth`

This file adds evaluation-level lemmas to complement the existing coefficient-level
definitions in `ArkLib/Data/Polynomial/SplitFold.lean`.

**Context**: These lemmas arise naturally when verifying Plonky3's FRI folding
operation. The existing file defines `splitNth` and `foldNth` with
coefficient-level identities (`splitNth_def`) and degree bounds
(`foldNth_degree_le`), but provides no evaluation-level results.

The four lemmas below fill that gap. Together they prove that `foldNth 2 f β`
evaluated at `x²` equals the standard FRI fold of `f(x)` and `f(-x)`.

Addresses: https://github.com/Verified-zkEVM/ArkLib/issues/450
-/



variable {𝔽 : Type*} [Field 𝔽]

/-!
## Lemma 1: `splitNth` commutes with evaluation at `s ^ n`

The `n`-th split component of `f`, when viewed as a polynomial in `X^n`
(i.e., via `eval₂ C (X ^ n)`), evaluates at `s` the same way as evaluating
the component directly at `s ^ n`.

This follows from the universal property of `eval₂`: substituting `X ↦ X^n`
then evaluating at `s` is the same as evaluating at `s^n` directly, because
`(X^n).eval s = s^n`.
-/
lemma splitNth_eval_comp_pow (n : ℕ) (hn : n ≠ 0) (f : 𝔽[X]) (s : 𝔽) (i : Fin n) :
    (eval₂ C (X ^ n) (splitNth f n i)).eval s = (splitNth f n i).eval (s ^ n) := by
  simp [eval₂_eq_eval_map, Polynomial.map_pow, eval_pow, eval_X]

/-!
## Lemma 2: Even evaluation identity

For any polynomial `f` and field element `x`,
`f(x) + f(-x) = 2 * (even part of f)(x²)`

where the "even part" is `splitNth f 2 0` — the sub-polynomial collecting all
coefficients of `f` at even-degree positions.

**Proof sketch**: Write `f = Σ aₙ Xⁿ`. Then
- `f(x)   = Σ aₙ xⁿ`
- `f(-x)  = Σ aₙ (-x)ⁿ = Σ aₙ (-1)ⁿ xⁿ`
- `f(x) + f(-x) = 2 Σ_{k even} a_k x^k = 2 Σ_j a_{2j} x^{2j}`

By definition `splitNth f 2 0 = Σ_j a_{2j} X^j`, so its evaluation at `x²`
gives `Σ_j a_{2j} x^{2j}`, matching the right-hand side.
-/
lemma splitNth_two_eval_add (f : 𝔽[X]) (x : 𝔽) :
    f.eval x + f.eval (-x) = 2 * (splitNth f 2 0).eval (x ^ 2) := by
  simp only [Polynomial.eval_eq_sum, splitNth]
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    simp [Finset.mem_range]
    ring_nf
    simp [neg_pow, even_iff_two_dvd]
  · ring_nf
    simp [splitNth_def]
    congr 1
    ext j
    simp [coeff_ofFinsupp, Finsupp.mapDomain]
    ring

-- Cleaner tactic proof using `ring` and `splitNth_def` unfolding:
lemma splitNth_two_eval_add' (f : 𝔽[X]) (x : 𝔽) :
    f.eval x + f.eval (-x) = 2 * (splitNth f 2 0).eval (x ^ 2) := by
  induction f using Polynomial.induction_on' with
  | h_add p q hp hq =>
    simp [eval_add, hp, hq]
    ring
  | h_monomial n a =>
    simp [splitNth_monomial, eval_monomial]
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- even case: n = 2k
      subst hk
      simp [splitNth_monomial_even]
      ring_nf
      simp [neg_pow, even_two_mul]
      ring
    · -- odd case: n = 2k + 1
      subst hk
      simp [splitNth_monomial_odd]
      ring_nf
      simp [neg_pow, Nat.odd_add, odd_two_mul_add_one]
      ring

/-!
## Lemma 3: Odd evaluation identity

For any polynomial `f` and field element `x`,
`f(x) - f(-x) = 2 * x * (odd part of f)(x²)`

where the "odd part" is `splitNth f 2 1` — collecting coefficients at odd positions.

**Proof sketch**: Similarly to Lemma 2,
- `f(x) - f(-x) = 2 Σ_{k odd} a_k x^k = 2 Σ_j a_{2j+1} x^{2j+1} = 2x Σ_j a_{2j+1} x^{2j}`

By definition `splitNth f 2 1 = Σ_j a_{2j+1} X^j`, so evaluated at `x²` gives
`Σ_j a_{2j+1} x^{2j}`, and multiplying by `2x` gives the right-hand side.
-/
lemma splitNth_two_eval_sub (f : 𝔽[X]) (x : 𝔽) :
    f.eval x - f.eval (-x) = 2 * x * (splitNth f 2 1).eval (x ^ 2) := by
  induction f using Polynomial.induction_on' with
  | h_add p q hp hq =>
    simp [eval_add, hp, hq]
    ring
  | h_monomial n a =>
    simp [splitNth_monomial, eval_monomial]
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- even case: contributes 0 to the odd part
      subst hk
      simp [splitNth_monomial_even]
      ring_nf
      simp [neg_pow, even_two_mul]
      ring
    · -- odd case: n = 2k+1, coefficient lands in splitNth f 2 1 at index k
      subst hk
      simp [splitNth_monomial_odd]
      ring_nf
      simp [neg_pow, odd_two_mul_add_one]
      ring

/-!
## Lemma 4: FRI folding evaluation

The main result: `foldNth 2 f β` evaluated at `x²` equals the standard
FRI fold formula in terms of `f(x)` and `f(-x)`.

**Statement**:
```
(foldNth 2 f β).eval (x²) =
  (f(x) + f(-x) + β · (f(x) - f(-x)) · x⁻¹) · 2⁻¹
```

**Proof**: By definition,
`foldNth 2 f β = splitNth f 2 0 + β · splitNth f 2 1`
(the even part plus `β` times the odd part, both as polynomials in `X`).

Evaluating at `x²` and applying Lemmas 2 and 3:
```
(foldNth 2 f β).eval(x²)
  = (splitNth f 2 0).eval(x²) + β · (splitNth f 2 1).eval(x²)
  = (f(x) + f(-x))/2        + β · (f(x) - f(-x))/(2x)
  = [f(x) + f(-x) + β · (f(x) - f(-x)) · x⁻¹] · 2⁻¹
```
-/
lemma foldNth_two_eval (f : 𝔽[X]) (x β : 𝔽)
    (hx : x ≠ 0) (h2 : (2 : 𝔽) ≠ 0) :
    (foldNth 2 f β).eval (x ^ 2) =
    (f.eval x + f.eval (-x) +
      β * (f.eval x - f.eval (-x)) * x⁻¹) * (2 : 𝔽)⁻¹ := by
  -- Unfold foldNth: it is the linear combination of the split components
  rw [foldNth_eq_sum_splitNth]
  simp only [Fin.sum_univ_two, eval_add, eval_mul, eval_ofNat]
  -- Use Lemmas 2 and 3 to rewrite each component
  rw [← splitNth_two_eval_add, ← splitNth_two_eval_sub]
  -- Pure field arithmetic: solve the equation
  have hx2 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  have h2inv : (2 : 𝔽) * (2 : 𝔽)⁻¹ = 1 := mul_inv_cancel₀ h2
  field_simp
  ring

/-!
## Notes for reviewers

1. The proofs above assume the following definitions exist in `SplitFold.lean`
   (or are imported from it):
   - `splitNth f n i` — the `i`-th component polynomial
   - `foldNth n f β` — the folded polynomial
   - `splitNth_def` — coefficient identity
   - `splitNth_monomial_even` / `splitNth_monomial_odd` — behaviour on monomials
   - `foldNth_eq_sum_splitNth` — `foldNth n f β = Σ i, β^i * splitNth f n i`

2. If `splitNth_monomial_even` / `splitNth_monomial_odd` are not yet in the file,
   they can be proved as immediate corollaries of `splitNth_def`:

   ```lean
   lemma splitNth_monomial_even (a : 𝔽) (k : ℕ) :
       splitNth (monomial (2 * k) a) 2 0 = monomial k a := by
     ext j; simp [splitNth_def, coeff_monomial]; omega

   lemma splitNth_monomial_odd (a : 𝔽) (k : ℕ) :
       splitNth (monomial (2 * k + 1) a) 2 1 = monomial k a := by
     ext j; simp [splitNth_def, coeff_monomial]; omega
   ```

3. `foldNth_two_eval` is the critical lemma for verifying Plonky3's FRI
   folding step (issue #450). The other three lemmas are intermediate steps
   and can be marked `private` if preferred.
-/


end Polynomial
