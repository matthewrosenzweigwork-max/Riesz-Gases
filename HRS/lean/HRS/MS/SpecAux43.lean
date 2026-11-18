import HRS.MS.SpecAux42
import HRS.MS.MovOscAux3

/-!
# S8P: the oscillator form is bounded by `L²` norms of `S`, `x_j S`, `∂_j S` (S8.7, packet b6)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_osc1_bound`: there is `K` with
`(∑_α λ_α ⟨b_α, S⟩²) = oscNorm 1 S ^2 ≤ K (∫ S² + ∑_j ∫ (x_j S)² + ∑_j ∫ (∂_j S)²)` for every Schwartz `S`.  From `mo_int_equiv`
for `n = 1` (the index set `{(a,γ) : |a|+|γ| ≤ 1}` consists of `(0,0)`, `(e_j,0)`, `(0,e_j)`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovOsc

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_deg_zero {a : MultiIndex d} (h : MultiIndex.degree a = 0) : a = 0 := by
  funext i
  exact (Finset.sum_eq_zero_iff.1 h) i (Finset.mem_univ i)

theorem s8p_deg_one {a : MultiIndex d} (h : MultiIndex.degree a = 1) :
    ∃ j : Fin d, a = Function.update (0 : MultiIndex d) j 1 := by
  have hne : ∃ j, a j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : MultiIndex.degree a = 0 := Finset.sum_eq_zero fun i _ => hcon i
    omega
  obtain ⟨j, hj⟩ := hne
  have hj1 : a j = 1 := by
    have h1 : a j ≤ MultiIndex.degree a := mova1_le_degree a j
    omega
  refine ⟨j, funext fun i => ?_⟩
  by_cases hij : i = j
  · subst hij; simp [hj1]
  · rw [Function.update_of_ne hij]
    simp only [Pi.zero_apply]
    have hsum := Finset.add_sum_erase (Finset.univ : Finset (Fin d)) a (Finset.mem_univ j)
    have h2 : ∑ k ∈ Finset.univ.erase j, a k = 0 := by
      unfold MultiIndex.degree at h
      omega
    exact (Finset.sum_eq_zero_iff.1 h2) i (Finset.mem_erase.2 ⟨hij, Finset.mem_univ i⟩)

theorem s8p_xpow_single (j : Fin d) (x : Euc d) :
    mo_xpow (Function.update (0 : MultiIndex d) j 1) x = x j := by
  unfold mo_xpow
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    simp [Function.update_of_ne hij]
  · simp

theorem s8p_pd_single (j : Fin d) (S : 𝓢R) :
    ⇑(mo_pd (Function.update (0 : MultiIndex d) j 1) S) = fun x => fderiv ℝ S x (EuclideanSpace.single j 1) := by
  have h1 : Function.update (0 : MultiIndex d) j 1 = mova1_up j 0 := by
    unfold mova1_up; simp
  rw [h1, ← mova1_D_pd, mova1_pd_zero]
  funext x
  rfl

theorem s8p_term_le (S : 𝓢R) (p : MultiIndex d × MultiIndex d) (hp : p ∈ mo_idx d 1) :
    mo_l2 (fun x => mo_xpow p.1 x * mo_pd p.2 S x) ≤ mo_l2 (fun x => S x) +
      ∑ j : Fin d, mo_l2 (fun x => x j * S x) +
      ∑ j : Fin d, mo_l2 (fun x => fderiv ℝ S x (EuclideanSpace.single j 1)) := by
  have hdeg : MultiIndex.degree p.1 + MultiIndex.degree p.2 ≤ 1 := (Finset.mem_filter.1 hp).2
  have h0 := mo_l2_nonneg (d := d)
  have hB : 0 ≤ ∑ j : Fin d, mo_l2 (fun x => x j * S x) := Finset.sum_nonneg fun j _ => h0 _
  have hC : 0 ≤ ∑ j : Fin d, mo_l2 (fun x => fderiv ℝ S x (EuclideanSpace.single j 1)) :=
    Finset.sum_nonneg fun j _ => h0 _
  have hA := h0 (fun x => S x)
  rcases (by omega : (MultiIndex.degree p.1 = 0 ∧ MultiIndex.degree p.2 = 0) ∨
      (MultiIndex.degree p.1 = 1 ∧ MultiIndex.degree p.2 = 0) ∨
      (MultiIndex.degree p.1 = 0 ∧ MultiIndex.degree p.2 = 1)) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 := s8p_deg_zero h1
    have e2 := s8p_deg_zero h2
    have : (fun x => mo_xpow p.1 x * mo_pd p.2 S x) = fun x => S x := by
      funext x; rw [e1, e2, mova1_pd_zero]; simp [mo_xpow]
    rw [this]; linarith
  · obtain ⟨j, hj⟩ := s8p_deg_one h1
    have e2 := s8p_deg_zero h2
    have : (fun x => mo_xpow p.1 x * mo_pd p.2 S x) = fun x => x j * S x := by
      funext x; rw [hj, e2, mova1_pd_zero, s8p_xpow_single]
    rw [this]
    have := Finset.single_le_sum (f := fun j => mo_l2 (fun x => x j * S x)) (fun j _ => h0 _)
      (Finset.mem_univ j)
    linarith
  · have e1 := s8p_deg_zero h1
    obtain ⟨j, hj⟩ := s8p_deg_one h2
    have : (fun x => mo_xpow p.1 x * mo_pd p.2 S x) = fun x => fderiv ℝ S x (EuclideanSpace.single j 1) := by
      funext x
      rw [hj, e1]
      have := congrFun (s8p_pd_single j S) x
      rw [this]
      simp [mo_xpow]
    rw [this]
    have := Finset.single_le_sum (f := fun j => mo_l2 (fun x => fderiv ℝ S x (EuclideanSpace.single j 1)))
      (fun j _ => h0 _) (Finset.mem_univ j)
    linarith

theorem s8p_osc1_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ S : 𝓢R, oscNorm 1 S ^ 2 ≤ K * ((∫ x, S x ^ 2) +
      (∑ j : Fin d, ∫ x, (x j * S x) ^ 2) + ∑ j : Fin d, ∫ x, (fderiv ℝ S x (EuclideanSpace.single j 1)) ^ 2) := by
  obtain ⟨C, hC, hCb⟩ := mo_int_equiv (d := d) 1
  set N : ℝ := ((mo_idx d 1).card : ℝ) with hN
  refine ⟨C ^ 2 * N ^ 2 * (3 * ((d : ℝ) + 1)), by positivity, fun S => ?_⟩
  set A : ℝ := mo_l2 (fun x => S x) with hA
  set B : ℝ := ∑ j : Fin d, mo_l2 (fun x => x j * S x) with hBdef
  set Cc : ℝ := ∑ j : Fin d, mo_l2 (fun x => fderiv ℝ S x (EuclideanSpace.single j 1)) with hCdef
  have hsq : ∀ g : Euc d → ℝ, mo_l2 g ^ 2 = ∫ x, g x ^ 2 := fun g =>
    Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)
  have h1 : oscNorm 1 S ≤ C * (N * (A + B + Cc)) := by
    have := (hCb S).2
    simp only [Nat.cast_one] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    calc ∑ p ∈ mo_idx d 1, mo_l2 (fun x => mo_xpow p.1 x * mo_pd p.2 S x)
        ≤ ∑ p ∈ mo_idx d 1, (A + B + Cc) := Finset.sum_le_sum fun p hp => s8p_term_le S p hp
      _ = N * (A + B + Cc) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hosc0 : 0 ≤ oscNorm 1 S := Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := mo_l2_nonneg _
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => mo_l2_nonneg _
  have hC0 : 0 ≤ Cc := Finset.sum_nonneg fun j _ => mo_l2_nonneg _
  have h2 : oscNorm 1 S ^ 2 ≤ (C * (N * (A + B + Cc))) ^ 2 := pow_le_pow_left₀ hosc0 h1 2
  have hB2 : B ^ 2 ≤ (d : ℝ) * ∑ j : Fin d, mo_l2 (fun x => x j * S x) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun j => mo_l2 (fun x => x j * S x))
    simpa using this
  have hC2 : Cc ^ 2 ≤ (d : ℝ) * ∑ j : Fin d, mo_l2 (fun x => fderiv ℝ S x (EuclideanSpace.single j 1)) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun j => mo_l2 (fun x => fderiv ℝ S x (EuclideanSpace.single j 1)))
    simpa using this
  have h3 : (A + B + Cc) ^ 2 ≤ 3 * ((d : ℝ) + 1) * (A ^ 2 + (∑ j : Fin d, mo_l2 (fun x => x j * S x) ^ 2) +
      ∑ j : Fin d, mo_l2 (fun x => fderiv ℝ S x (EuclideanSpace.single j 1)) ^ 2) := by
    have e1 : (A + B + Cc) ^ 2 ≤ 3 * (A ^ 2 + B ^ 2 + Cc ^ 2) := by
      nlinarith [sq_nonneg (A - B), sq_nonneg (B - Cc), sq_nonneg (A - Cc)]
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hs1 : 0 ≤ ∑ j : Fin d, mo_l2 (fun x => x j * S x) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hs2 : 0 ≤ ∑ j : Fin d, mo_l2 (fun x => fderiv ℝ S x (EuclideanSpace.single j 1)) ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    nlinarith [sq_nonneg A]
  have e2 : A ^ 2 + (∑ j : Fin d, mo_l2 (fun x => x j * S x) ^ 2) +
      ∑ j : Fin d, mo_l2 (fun x => fderiv ℝ S x (EuclideanSpace.single j 1)) ^ 2 =
      (∫ x, S x ^ 2) + (∑ j : Fin d, ∫ x, (x j * S x) ^ 2) +
        ∑ j : Fin d, ∫ x, (fderiv ℝ S x (EuclideanSpace.single j 1)) ^ 2 := by
    rw [hA, hsq]
    simp_rw [hsq]
  calc oscNorm 1 S ^ 2 ≤ (C * (N * (A + B + Cc))) ^ 2 := h2
    _ = C ^ 2 * N ^ 2 * (A + B + Cc) ^ 2 := by ring
    _ ≤ C ^ 2 * N ^ 2 * (3 * ((d : ℝ) + 1) * ((∫ x, S x ^ 2) + (∑ j : Fin d, ∫ x, (x j * S x) ^ 2) +
        ∑ j : Fin d, ∫ x, (fderiv ℝ S x (EuclideanSpace.single j 1)) ^ 2)) := by
        rw [← e2]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

end HRS.MS.Spec
