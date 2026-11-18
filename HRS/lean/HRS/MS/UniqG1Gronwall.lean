import Mathlib

/-!
# G1 (part 1): Gronwall inequality with a constant source

Route (elementary, no derivatives; `φ` is only measurable).  Induction on `n`, comparing with the
iterates of the integral operator.  Write `x = aτ`.

* `g1_gronwall_source` (the statement as specified, whose hypothesis `hle` parses as
  `φ τ ≤ a * ∫ σ in 0..τ, (φ σ + δ)`): the bound
  `φ τ ≤ δ ∑_{k<n} x^{k+1}/(k+1)! + B x^n/n!` is propagated by the step
  `a ∫_0^τ (g + δ) = δ ∑_{k<n} x^{k+2}/(k+2)! + B x^{n+1}/(n+1)! + δ x`, and
  `∑_{k<n} x^{k+1}/(k+1)! ≤ exp x` (partial sums of `exp x`), so `φ τ ≤ δ exp(aτ)`.
* `g1_gronwall_source_paren` (the intended reading `φ τ ≤ a * (∫ σ in 0..τ, φ σ) + δ`): the bound
  `φ τ ≤ δ ∑_{k<n} x^k/k! + B x^n/n!`, same conclusion.

In both, the remainder `B x^n/n! → 0` (`FloorSemiring.tendsto_pow_div_factorial_atTop`).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace HRS.MS.UniqG1

theorem g1_a_integral_pow_div (a τ : ℝ) (k : ℕ) :
    a * ∫ σ in (0:ℝ)..τ, (a * σ) ^ k / (k.factorial : ℝ) =
      (a * τ) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  have h : ∀ σ : ℝ, (a * σ) ^ k / (k.factorial : ℝ) = (a ^ k / (k.factorial : ℝ)) * σ ^ k := by
    intro σ; rw [mul_pow]; ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero k), sub_zero,
    Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem g1_gronwall_hint (φ : ℝ → ℝ) (t B : ℝ)
    (hφ0 : ∀ τ ∈ Set.Icc 0 t, 0 ≤ φ τ) (hB : ∀ τ ∈ Set.Icc 0 t, φ τ ≤ B)
    (hmeas : AEStronglyMeasurable φ (volume.restrict (Set.Icc 0 t))) :
    ∀ τ ∈ Set.Icc 0 t, IntervalIntegrable φ volume 0 τ := by
  intro τ hτ
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
  have hsub : Set.Icc 0 τ ⊆ Set.Icc 0 t := Set.Icc_subset_Icc_right hτ.2
  refine Integrable.of_bound (hmeas.mono_set hsub) |B| ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun x hx => ?_)
  have hx' : x ∈ Set.Icc 0 t := hsub hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 x hx')]
  exact (hB x hx').trans (le_abs_self B)

theorem g1_gronwall_source (φ : ℝ → ℝ) (t a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hφ0 : ∀ τ ∈ Set.Icc 0 t, 0 ≤ φ τ) (hφB : ∃ B, ∀ τ ∈ Set.Icc 0 t, φ τ ≤ B)
    (hmeas : AEStronglyMeasurable φ (volume.restrict (Set.Icc 0 t)))
    (hle : ∀ τ ∈ Set.Icc 0 t, φ τ ≤ a * ∫ σ in (0:ℝ)..τ, φ σ + δ) :
    ∀ τ ∈ Set.Icc 0 t, φ τ ≤ δ * Real.exp (a * τ) := by
  obtain ⟨B, hB⟩ := hφB
  have hint := g1_gronwall_hint φ t B hφ0 hB hmeas
  have key : ∀ n : ℕ, ∀ τ ∈ Set.Icc 0 t, φ τ ≤
      δ * ∑ k ∈ Finset.range n, (a * τ) ^ (k + 1) / ((k + 1).factorial : ℝ) +
        B * ((a * τ) ^ n / (n.factorial : ℝ)) := by
    intro n
    induction n with
    | zero => intro τ hτ; simpa using hB τ hτ
    | succ n ih =>
      intro τ hτ
      have hτ0 : (0:ℝ) ≤ τ := hτ.1
      have hI := hint τ hτ
      have hGc : Continuous (fun σ : ℝ =>
          δ * ∑ k ∈ Finset.range n, (a * σ) ^ (k + 1) / ((k + 1).factorial : ℝ) +
            B * ((a * σ) ^ n / (n.factorial : ℝ))) := by fun_prop
      have hS : ∀ k ∈ Finset.range n,
          IntervalIntegrable (fun σ : ℝ => (a * σ) ^ (k + 1) / ((k + 1).factorial : ℝ)) volume 0 τ :=
        fun k _ => (show Continuous (fun σ : ℝ => (a * σ) ^ (k + 1) / ((k + 1).factorial : ℝ))
          by fun_prop).intervalIntegrable _ _
      have hSc : Continuous (fun σ : ℝ =>
          δ * ∑ k ∈ Finset.range n, (a * σ) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by fun_prop
      have hPc : Continuous (fun σ : ℝ => B * ((a * σ) ^ n / (n.factorial : ℝ))) := by fun_prop
      have h1 : ∫ σ in (0:ℝ)..τ, (φ σ + δ) ≤ ∫ σ in (0:ℝ)..τ,
          ((δ * ∑ k ∈ Finset.range n, (a * σ) ^ (k + 1) / ((k + 1).factorial : ℝ) +
            B * ((a * σ) ^ n / (n.factorial : ℝ))) + δ) :=
        intervalIntegral.integral_mono_on hτ0 (hI.add intervalIntegrable_const)
          ((hGc.add continuous_const).intervalIntegrable _ _) fun σ hσ => by
            have := ih σ ⟨hσ.1, hσ.2.trans hτ.2⟩
            linarith
      have h2 : ∫ σ in (0:ℝ)..τ,
          ((δ * ∑ k ∈ Finset.range n, (a * σ) ^ (k + 1) / ((k + 1).factorial : ℝ) +
            B * ((a * σ) ^ n / (n.factorial : ℝ))) + δ) =
          δ * (∑ k ∈ Finset.range n, ∫ σ in (0:ℝ)..τ, (a * σ) ^ (k + 1) / ((k + 1).factorial : ℝ)) +
            B * (∫ σ in (0:ℝ)..τ, (a * σ) ^ n / (n.factorial : ℝ)) + δ * τ := by
        rw [intervalIntegral.integral_add (hGc.intervalIntegrable _ _) intervalIntegrable_const,
          intervalIntegral.integral_add (hSc.intervalIntegrable _ _) (hPc.intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hS,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        simp only [smul_eq_mul, sub_zero]
        ring
      have hsum : a * ∑ k ∈ Finset.range n,
          ∫ σ in (0:ℝ)..τ, (a * σ) ^ (k + 1) / ((k + 1).factorial : ℝ) =
          ∑ k ∈ Finset.range n, (a * τ) ^ (k + 1 + 1) / ((k + 1 + 1).factorial : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => g1_a_integral_pow_div a τ (k + 1)
      have h3 : a * ∫ σ in (0:ℝ)..τ, (φ σ + δ) ≤
          δ * ∑ k ∈ Finset.range n, (a * τ) ^ (k + 1 + 1) / ((k + 1 + 1).factorial : ℝ) +
            B * ((a * τ) ^ (n + 1) / ((n + 1).factorial : ℝ)) + δ * (a * τ) := by
        calc a * ∫ σ in (0:ℝ)..τ, (φ σ + δ)
            ≤ a * (δ * (∑ k ∈ Finset.range n,
                  ∫ σ in (0:ℝ)..τ, (a * σ) ^ (k + 1) / ((k + 1).factorial : ℝ)) +
                B * (∫ σ in (0:ℝ)..τ, (a * σ) ^ n / (n.factorial : ℝ)) + δ * τ) :=
              mul_le_mul_of_nonneg_left (h1.trans_eq h2) ha
          _ = δ * (a * ∑ k ∈ Finset.range n,
                  ∫ σ in (0:ℝ)..τ, (a * σ) ^ (k + 1) / ((k + 1).factorial : ℝ)) +
                B * (a * ∫ σ in (0:ℝ)..τ, (a * σ) ^ n / (n.factorial : ℝ)) + δ * (a * τ) := by
              ring
          _ = δ * ∑ k ∈ Finset.range n, (a * τ) ^ (k + 1 + 1) / ((k + 1 + 1).factorial : ℝ) +
                B * ((a * τ) ^ (n + 1) / ((n + 1).factorial : ℝ)) + δ * (a * τ) := by
              rw [hsum, g1_a_integral_pow_div a τ n]
      have hrw : δ * ∑ k ∈ Finset.range (n + 1), (a * τ) ^ (k + 1) / ((k + 1).factorial : ℝ) =
          δ * ∑ k ∈ Finset.range n, (a * τ) ^ (k + 1 + 1) / ((k + 1 + 1).factorial : ℝ) +
            δ * (a * τ) := by
        rw [Finset.sum_range_succ']
        simp only [zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
        ring
      calc φ τ ≤ a * ∫ σ in (0:ℝ)..τ, (φ σ + δ) := hle τ hτ
        _ ≤ δ * ∑ k ∈ Finset.range n, (a * τ) ^ (k + 1 + 1) / ((k + 1 + 1).factorial : ℝ) +
              B * ((a * τ) ^ (n + 1) / ((n + 1).factorial : ℝ)) + δ * (a * τ) := h3
        _ = δ * ∑ k ∈ Finset.range (n + 1), (a * τ) ^ (k + 1) / ((k + 1).factorial : ℝ) +
              B * ((a * τ) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
          rw [hrw]; ring
  intro τ hτ
  have hx : 0 ≤ a * τ := mul_nonneg ha hτ.1
  have hSn : ∀ n : ℕ, ∑ k ∈ Finset.range n, (a * τ) ^ (k + 1) / ((k + 1).factorial : ℝ) ≤
      Real.exp (a * τ) := by
    intro n
    have h := Real.sum_le_exp_of_nonneg hx (n + 1)
    rw [Finset.sum_range_succ'] at h
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
    linarith
  have hlim : Tendsto (fun n : ℕ => δ * Real.exp (a * τ) +
      B * ((a * τ) ^ n / (n.factorial : ℝ))) atTop (𝓝 (δ * Real.exp (a * τ) + B * 0)) :=
    ((FloorSemiring.tendsto_pow_div_factorial_atTop (a * τ)).const_mul B).const_add _
  rw [mul_zero, add_zero] at hlim
  refine le_of_tendsto_of_tendsto' tendsto_const_nhds hlim fun n => ?_
  have hS := mul_le_mul_of_nonneg_left (hSn n) hδ
  have := key n τ hτ
  linarith

theorem g1_gronwall_source_paren (φ : ℝ → ℝ) (t a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hφ0 : ∀ τ ∈ Set.Icc 0 t, 0 ≤ φ τ) (hφB : ∃ B, ∀ τ ∈ Set.Icc 0 t, φ τ ≤ B)
    (hmeas : AEStronglyMeasurable φ (volume.restrict (Set.Icc 0 t)))
    (hle : ∀ τ ∈ Set.Icc 0 t, φ τ ≤ a * (∫ σ in (0:ℝ)..τ, φ σ) + δ) :
    ∀ τ ∈ Set.Icc 0 t, φ τ ≤ δ * Real.exp (a * τ) := by
  obtain ⟨B, hB⟩ := hφB
  have hint := g1_gronwall_hint φ t B hφ0 hB hmeas
  have key : ∀ n : ℕ, ∀ τ ∈ Set.Icc 0 t, φ τ ≤
      δ * ∑ k ∈ Finset.range n, (a * τ) ^ k / (k.factorial : ℝ) +
        B * ((a * τ) ^ n / (n.factorial : ℝ)) := by
    intro n
    induction n with
    | zero => intro τ hτ; simpa using hB τ hτ
    | succ n ih =>
      intro τ hτ
      have hτ0 : (0:ℝ) ≤ τ := hτ.1
      have hI := hint τ hτ
      have hGc : Continuous (fun σ : ℝ =>
          δ * ∑ k ∈ Finset.range n, (a * σ) ^ k / (k.factorial : ℝ) +
            B * ((a * σ) ^ n / (n.factorial : ℝ))) := by fun_prop
      have hS : ∀ k ∈ Finset.range n,
          IntervalIntegrable (fun σ : ℝ => (a * σ) ^ k / (k.factorial : ℝ)) volume 0 τ :=
        fun k _ => (show Continuous (fun σ : ℝ => (a * σ) ^ k / (k.factorial : ℝ))
          by fun_prop).intervalIntegrable _ _
      have hSc : Continuous (fun σ : ℝ =>
          δ * ∑ k ∈ Finset.range n, (a * σ) ^ k / (k.factorial : ℝ)) := by fun_prop
      have hPc : Continuous (fun σ : ℝ => B * ((a * σ) ^ n / (n.factorial : ℝ))) := by fun_prop
      have h1 : ∫ σ in (0:ℝ)..τ, φ σ ≤ ∫ σ in (0:ℝ)..τ,
          (δ * ∑ k ∈ Finset.range n, (a * σ) ^ k / (k.factorial : ℝ) +
            B * ((a * σ) ^ n / (n.factorial : ℝ))) :=
        intervalIntegral.integral_mono_on hτ0 hI (hGc.intervalIntegrable _ _)
          fun σ hσ => ih σ ⟨hσ.1, hσ.2.trans hτ.2⟩
      have h2 : ∫ σ in (0:ℝ)..τ,
          (δ * ∑ k ∈ Finset.range n, (a * σ) ^ k / (k.factorial : ℝ) +
            B * ((a * σ) ^ n / (n.factorial : ℝ))) =
          δ * (∑ k ∈ Finset.range n, ∫ σ in (0:ℝ)..τ, (a * σ) ^ k / (k.factorial : ℝ)) +
            B * (∫ σ in (0:ℝ)..τ, (a * σ) ^ n / (n.factorial : ℝ)) := by
        rw [intervalIntegral.integral_add (hSc.intervalIntegrable _ _) (hPc.intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hS,
          intervalIntegral.integral_const_mul]
      have hsum : a * ∑ k ∈ Finset.range n, ∫ σ in (0:ℝ)..τ, (a * σ) ^ k / (k.factorial : ℝ) =
          ∑ k ∈ Finset.range n, (a * τ) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => g1_a_integral_pow_div a τ k
      have h3 : a * ∫ σ in (0:ℝ)..τ, φ σ ≤
          δ * ∑ k ∈ Finset.range n, (a * τ) ^ (k + 1) / ((k + 1).factorial : ℝ) +
            B * ((a * τ) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
        calc a * ∫ σ in (0:ℝ)..τ, φ σ
            ≤ a * (δ * (∑ k ∈ Finset.range n, ∫ σ in (0:ℝ)..τ, (a * σ) ^ k / (k.factorial : ℝ)) +
                B * (∫ σ in (0:ℝ)..τ, (a * σ) ^ n / (n.factorial : ℝ))) :=
              mul_le_mul_of_nonneg_left (h1.trans_eq h2) ha
          _ = δ * (a * ∑ k ∈ Finset.range n, ∫ σ in (0:ℝ)..τ, (a * σ) ^ k / (k.factorial : ℝ)) +
                B * (a * ∫ σ in (0:ℝ)..τ, (a * σ) ^ n / (n.factorial : ℝ)) := by
              ring
          _ = δ * ∑ k ∈ Finset.range n, (a * τ) ^ (k + 1) / ((k + 1).factorial : ℝ) +
                B * ((a * τ) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
              rw [hsum, g1_a_integral_pow_div a τ n]
      have hrw : δ * ∑ k ∈ Finset.range (n + 1), (a * τ) ^ k / (k.factorial : ℝ) =
          δ * ∑ k ∈ Finset.range n, (a * τ) ^ (k + 1) / ((k + 1).factorial : ℝ) + δ := by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
        ring
      calc φ τ ≤ a * (∫ σ in (0:ℝ)..τ, φ σ) + δ := hle τ hτ
        _ ≤ δ * ∑ k ∈ Finset.range n, (a * τ) ^ (k + 1) / ((k + 1).factorial : ℝ) +
              B * ((a * τ) ^ (n + 1) / ((n + 1).factorial : ℝ)) + δ := by linarith [h3]
        _ = δ * ∑ k ∈ Finset.range (n + 1), (a * τ) ^ k / (k.factorial : ℝ) +
              B * ((a * τ) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
          rw [hrw]; ring
  intro τ hτ
  have hx : 0 ≤ a * τ := mul_nonneg ha hτ.1
  have hlim : Tendsto (fun n : ℕ => δ * Real.exp (a * τ) +
      B * ((a * τ) ^ n / (n.factorial : ℝ))) atTop (𝓝 (δ * Real.exp (a * τ) + B * 0)) :=
    ((FloorSemiring.tendsto_pow_div_factorial_atTop (a * τ)).const_mul B).const_add _
  rw [mul_zero, add_zero] at hlim
  refine le_of_tendsto_of_tendsto' tendsto_const_nhds hlim fun n => ?_
  have hS := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hx n) hδ
  have := key n τ hτ
  linarith

end HRS.MS.UniqG1
