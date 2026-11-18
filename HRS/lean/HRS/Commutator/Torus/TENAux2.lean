import HRS.Commutator.Torus.TENAux1

/-!
# Torus energy layer (packet T-EN), helper part 2: the scale-`η` coercivity bound

Prefix `ten_`.  Given the Fourier data of a continuous kernel `g` (coefficients `c`, with the lower bound
`c_k ≥ c₀ (2π|k|)^{-(d-s)}` for `η|k| ≤ 8`), the low-frequency coercivity
`‖P_{≤4}σ‖²_{Ḣ^{-α}} + η^{d-s}∑_k ‖P_{≤4}σ̂(k)‖² ≤ C ‖σ‖²_g` holds for mass-zero `σ`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- Nonzero lattice points have positive Euclidean length. -/
theorem ten_enorm_pos {k : Lattice d} (hk : k ≠ 0) : 0 < Lattice.enorm k := by
  rcases (norm_nonneg (Lattice.toEuc k)).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hk
    have h' : ‖Lattice.toEuc k‖ = 0 := h.symm
    have h0 : Lattice.toEuc k = 0 := norm_eq_zero.1 h'
    funext i
    have hi := congrArg (fun v : Euc d => v i) h0
    simp only [Lattice.toEuc, PiLp.toLp_apply, PiLp.zero_apply, Int.cast_eq_zero] at hi
    simpa using hi

theorem ten_chi_nonneg (ξ : Euc d) : 0 ≤ Whole.chi ξ := (Whole.chiBump d).nonneg

theorem ten_chi_le_one (ξ : Euc d) : Whole.chi ξ ≤ 1 := (Whole.chiBump d).le_one

theorem ten_chi_zero_of_le {ξ : Euc d} (h : 2 ≤ ‖ξ‖) : Whole.chi ξ = 0 :=
  (Whole.chiBump d).zero_of_le_dist (by rw [dist_zero_right]; exact h)

/-- The coercivity bound on the lattice, scale `η ∈ (0,1]`, mass-zero finite signed measure. -/
theorem ten_scoercive_core {s : ℝ} (hds : 0 < (d : ℝ) - s) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (σ : SMT d) (hσ : σ.IsFinite) (hm : σ.mass = 0)
    {g : Torus d → ℝ} (hg : Continuous g) {c : Lattice d → ℝ} (hc : Summable (fun k => |c k|))
    (hcoef : ∀ k, Torus.fcoef g k = (c k : ℂ)) (hcnn : ∀ k, 0 ≤ c k)
    (c0 : ℝ) (hc0 : 0 < c0)
    (hcb : ∀ k : Lattice d, k ≠ 0 → η * Lattice.enorm k ≤ 8 →
      c0 * (2 * Real.pi * Lattice.enorm k) ^ (-((d : ℝ) - s)) ≤ c k) :
    homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef) +
        ENNReal.ofReal (η ^ ((d : ℝ) - s)) * ∑' k : Lattice d, ‖lowFreqT η 4 σ.coef k‖ₑ ^ 2 ≤
      ENNReal.ofReal ((1 + (16 * Real.pi) ^ ((d : ℝ) - s)) / c0 * kerEnergyT g σ) := by
  set t : ℝ := (d : ℝ) - s with ht
  set C : ℝ := (1 + (16 * Real.pi) ^ t) / c0 with hC
  set M : ℝ := (σ.pos Set.univ).toReal + (σ.neg Set.univ).toReal with hM
  have ht0 : 0 < t := hds
  have hCnn : 0 ≤ C := by
    rw [hC]; have : 0 < (16 * Real.pi) ^ t := Real.rpow_pos_of_pos (by positivity) t
    positivity
  have hexp : 2 * (-Whole.alphaE d s) = -t := by
    unfold Whole.alphaE; rw [ht]; ring
  -- the coefficient at `0` vanishes (mass zero)
  have hcoef0 : σ.coef 0 = 0 := by
    have h1 : σ.coef 0 = tenSint σ (fun _ => ((1 : ℝ) : ℂ)) := by
      unfold SMT.coef tenSint
      simp [Torus.mode_zero]
    have h2 : tenSint σ (fun _ => ((1 : ℝ) : ℂ)) = ((σ.mass : ℝ) : ℂ) :=
      (ten_ofReal σ (fun _ => (1 : ℝ))).symm
    rw [h1, h2, hm]; simp
  -- the lowest mode is killed
  have hF0 : lowFreqT η 4 σ.coef 0 = 0 := by
    simp only [lowFreqT, hcoef0, mul_zero]
  -- the coefficient bound
  have hcoefbd : ∀ k, ‖σ.coef k‖ ≤ M := fun k => ten_coef_norm_le σ hσ k
  -- the summand
  have hterm : ∀ k : Lattice d,
      (if k = 0 then 0 else ENNReal.ofReal ((2 * Real.pi * Lattice.enorm k) ^ (-t)) *
          ‖lowFreqT η 4 σ.coef k‖ₑ ^ 2) +
        ENNReal.ofReal (η ^ t) * ‖lowFreqT η 4 σ.coef k‖ₑ ^ 2 ≤
      ENNReal.ofReal (C * (c k * ‖σ.coef k‖ ^ 2)) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl, hF0]
      simp
    · rw [if_neg hk]
      set χ : ℝ := Whole.chi ((η / 4) • Lattice.toEuc k) with hχ
      have hFk : lowFreqT η 4 σ.coef k = (χ : ℂ) * σ.coef k := rfl
      have hχ0 : 0 ≤ χ := ten_chi_nonneg _
      have hχ1 : χ ≤ 1 := ten_chi_le_one _
      have hFe : ‖lowFreqT η 4 σ.coef k‖ₑ ^ 2 = ENNReal.ofReal ((χ * ‖σ.coef k‖) ^ 2) := by
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), hFk, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg hχ0]
      by_cases hχz : χ = 0
      · rw [hFe, hχz]; simp
      · -- `χ ≠ 0` forces `η |k| < 8`
        have hnorm : η / 4 * Lattice.enorm k < 2 := by
          by_contra hcon
          push_neg at hcon
          apply hχz
          rw [hχ]
          apply ten_chi_zero_of_le
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
          exact hcon
        have hηe : η * Lattice.enorm k ≤ 8 := by linarith
        set e : ℝ := Lattice.enorm k with he
        have he0 : 0 < e := ten_enorm_pos hk
        set a : ℝ := ‖σ.coef k‖ with ha
        have ha0 : 0 ≤ a := norm_nonneg _
        set P : ℝ := (2 * Real.pi * e) ^ (-t) with hP
        have hP0 : 0 ≤ P := Real.rpow_nonneg (by positivity) _
        -- `P ≤ c_k / c₀`
        have hPc : P ≤ c k / c0 := by
          have := hcb k hk hηe
          rw [le_div_iff₀ hc0]
          linarith [this, mul_comm P c0]
        -- `η^t ≤ (16π)^t P`
        have hηP : η ^ t ≤ (16 * Real.pi) ^ t * P := by
          have hpos : 0 < (2 * Real.pi * e) ^ t := Real.rpow_pos_of_pos (by positivity) t
          have hPeq : P = ((2 * Real.pi * e) ^ t)⁻¹ := by
            rw [hP, Real.rpow_neg (by positivity)]
          rw [hPeq, ← div_eq_mul_inv, le_div_iff₀ hpos]
          have hmul : η ^ t * (2 * Real.pi * e) ^ t = (η * (2 * Real.pi * e)) ^ t := by
            rw [Real.mul_rpow hη.le (by positivity)]
          rw [hmul]
          apply Real.rpow_le_rpow (by positivity) _ ht0.le
          nlinarith [Real.pi_pos]
        -- the two terms
        have hχsq : (χ * a) ^ 2 ≤ a ^ 2 := by
          have h1 : χ * a ≤ a := mul_le_of_le_one_left ha0 hχ1
          have h0 : 0 ≤ χ * a := mul_nonneg hχ0 ha0
          nlinarith
        have hT1 : P * (χ * a) ^ 2 ≤ (c k / c0) * a ^ 2 :=
          le_trans (mul_le_mul_of_nonneg_left hχsq hP0) (mul_le_mul_of_nonneg_right hPc (sq_nonneg a))
        have hT2 : η ^ t * (χ * a) ^ 2 ≤ (16 * Real.pi) ^ t * (c k / c0) * a ^ 2 := by
          have h1 : η ^ t * (χ * a) ^ 2 ≤ η ^ t * a ^ 2 :=
            mul_le_mul_of_nonneg_left hχsq (Real.rpow_nonneg hη.le t)
          have h2 : η ^ t * a ^ 2 ≤ (16 * Real.pi) ^ t * P * a ^ 2 :=
            mul_le_mul_of_nonneg_right hηP (sq_nonneg a)
          have h3 : (16 * Real.pi) ^ t * P * a ^ 2 ≤ (16 * Real.pi) ^ t * (c k / c0) * a ^ 2 := by
            have h4 : 0 ≤ (16 * Real.pi) ^ t * a ^ 2 := by
              have : 0 ≤ (16 * Real.pi) ^ t := Real.rpow_nonneg (by positivity) t
              positivity
            have h5 : P ≤ c k / c0 := hPc
            calc (16 * Real.pi) ^ t * P * a ^ 2 = ((16 * Real.pi) ^ t * a ^ 2) * P := by ring
              _ ≤ ((16 * Real.pi) ^ t * a ^ 2) * (c k / c0) := mul_le_mul_of_nonneg_left h5 h4
              _ = (16 * Real.pi) ^ t * (c k / c0) * a ^ 2 := by ring
          linarith
        have hCeq : C * (c k * a ^ 2) = (c k / c0) * a ^ 2 + (16 * Real.pi) ^ t * (c k / c0) * a ^ 2 := by
          rw [hC]; ring
        have hsum : P * (χ * a) ^ 2 + η ^ t * (χ * a) ^ 2 ≤ C * (c k * a ^ 2) := by
          rw [hCeq]; linarith
        have hη_t : 0 ≤ η ^ t := Real.rpow_nonneg hη.le t
        rw [hFe, ← ENNReal.ofReal_mul hP0, ← ENNReal.ofReal_mul hη_t,
          ← ENNReal.ofReal_add (mul_nonneg hP0 (sq_nonneg _)) (mul_nonneg hη_t (sq_nonneg _))]
        exact ENNReal.ofReal_le_ofReal hsum
  have hLHS : homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef) +
      ENNReal.ofReal (η ^ t) * ∑' k : Lattice d, ‖lowFreqT η 4 σ.coef k‖ₑ ^ 2 =
      ∑' k : Lattice d, ((if k = 0 then 0 else ENNReal.ofReal ((2 * Real.pi * Lattice.enorm k) ^ (-t)) *
          ‖lowFreqT η 4 σ.coef k‖ₑ ^ 2) + ENNReal.ofReal (η ^ t) * ‖lowFreqT η 4 σ.coef k‖ₑ ^ 2) := by
    unfold homSqT
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, hexp]
  have hsumC : Summable (fun k : Lattice d => C * (c k * ‖σ.coef k‖ ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg hCnn (mul_nonneg (hcnn k) (sq_nonneg _)))
      (fun k => ?_) ((hc.mul_right (M ^ 2)).mul_left C)
    have h1 : c k * ‖σ.coef k‖ ^ 2 ≤ |c k| * M ^ 2 := by
      rw [abs_of_nonneg (hcnn k)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hcoefbd k) 2) (hcnn k)
    exact mul_le_mul_of_nonneg_left h1 hCnn
  calc homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef) +
        ENNReal.ofReal (η ^ t) * ∑' k : Lattice d, ‖lowFreqT η 4 σ.coef k‖ₑ ^ 2
      = ∑' k : Lattice d, ((if k = 0 then 0 else ENNReal.ofReal ((2 * Real.pi * Lattice.enorm k) ^ (-t)) *
          ‖lowFreqT η 4 σ.coef k‖ₑ ^ 2) + ENNReal.ofReal (η ^ t) * ‖lowFreqT η 4 σ.coef k‖ₑ ^ 2) := hLHS
    _ ≤ ∑' k : Lattice d, ENNReal.ofReal (C * (c k * ‖σ.coef k‖ ^ 2)) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' k : Lattice d, C * (c k * ‖σ.coef k‖ ^ 2)) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun k => mul_nonneg hCnn (mul_nonneg (hcnn k) (sq_nonneg _))) hsumC).symm
    _ = ENNReal.ofReal (C * kerEnergyT g σ) := by
        rw [tsum_mul_left, ten_kerEnergy_fourier σ hσ hg hc hcoef]

end HRS.Commutator.TorusNote
