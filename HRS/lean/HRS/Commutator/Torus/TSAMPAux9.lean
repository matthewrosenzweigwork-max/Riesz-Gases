import HRS.Commutator.Torus.TSAMPAux8

/-!
# T-SAMP helpers, part 9: `potential_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tsamp_continuous_euc {X : Type*} [TopologicalSpace X] {f : X → Euc d}
    (h : ∀ j, Continuous fun x => f x j) : Continuous f := by
  have := (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp (continuous_pi h)
  have e : f = WithLp.toLp 2 ∘ fun a => (f a).ofLp := by funext a; simp
  rw [e]; exact this

lemma tsamp_real_pow_bound {t α q m g s' D : ℝ} (ht : 0 < t) (hα : 2 * α = D - s') (hq : 0 ≤ q)
    (hm0 : 0 ≤ m) (hmt : m ≤ t) :
    t ^ (α - 1) * (m * (q * t ^ (s' - D))) ≤ q * t ^ (-α) := by
  have ha0 : 0 ≤ t ^ (α - 1) := Real.rpow_nonneg ht.le _
  have e : t ^ (α - 1) * t * t ^ (s' - D) = t ^ (-α) := by
    rw [show t ^ (α - 1) * t * t ^ (s' - D) = t ^ (α - 1) * t ^ (1 : ℝ) * t ^ (s' - D) by
      rw [Real.rpow_one], ← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    linarith
  have hr0 : 0 ≤ q * t ^ (s' - D) := mul_nonneg hq (Real.rpow_nonneg ht.le _)
  calc t ^ (α - 1) * (m * (q * t ^ (s' - D))) = m * (t ^ (α - 1) * (q * t ^ (s' - D))) := by ring
    _ ≤ t * (t ^ (α - 1) * (q * t ^ (s' - D))) :=
        mul_le_mul_of_nonneg_right hmt (mul_nonneg ha0 hr0)
    _ = q * (t ^ (α - 1) * t * t ^ (s' - D)) := by ring
    _ = q * t ^ (-α) := by rw [e]

/-- The pointwise bound of the coefficients (the heart of `potential_T`). -/
lemma tsamp_coeff_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ} (hη : 0 < η)
    (σc : Lattice d → ℂ) (j : Fin d) (k : Lattice d) (hk : k ≠ 0) :
    ‖((((2 * Real.pi * Lattice.enorm k) ^ (Whole.alphaE d s - 1) : ℝ) : ℂ)) *
        (((tkrChi η k : ℝ) : ℂ) * tkrCI d s j k * σc k)‖ ≤
      |rieszConst d s| * (2 * Real.pi * Lattice.enorm k) ^ (-Whole.alphaE d s) *
        ‖((Whole.chi ((η / 4) • Lattice.toEuc k) : ℝ) : ℂ) * σc k‖ := by
  set t : ℝ := 2 * Real.pi * Lattice.enorm k with ht
  have hen : 0 < Lattice.enorm k := by
    have := HRS.one_le_enorm k hk
    linarith
  have htpos : 0 < t := by rw [ht]; positivity
  have hα : 2 * Whole.alphaE d s = (d : ℝ) - s := by unfold Whole.alphaE; ring
  have hkj : 2 * Real.pi * |((k j : ℤ) : ℝ)| ≤ t := by
    rw [ht]
    exact mul_le_mul_of_nonneg_left (HRS.KernelAux.abs_coord_le_enorm k j) (by positivity)
  have hcI : ‖(2 * (Real.pi : ℂ) * Complex.I * ((k j : ℤ) : ℂ))‖ = 2 * Real.pi * |((k j : ℤ) : ℝ)| := by
    simp [norm_mul, abs_of_pos Real.pi_pos]
  have hcoef : ‖tkrCI d s j k‖ = 2 * Real.pi * |((k j : ℤ) : ℝ)| * (|rieszConst d s| * t ^ (s - d)) := by
    unfold tkrCI
    rw [norm_mul, hcI, Complex.norm_real, Real.norm_eq_abs]
    congr 1
    unfold rieszCoeff
    simp only [hk, if_false]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg htpos.le _)]
  have hχ : tkrChi η k ≤ Whole.chi ((η / 4) • Lattice.toEuc k) := by
    by_cases h0 : tkrChi η k = 0
    · rw [h0]; exact Whole.cmxFB_chi_nonneg _
    · have h2 : η * Lattice.enorm k < 2 := by
        by_contra hcon
        exact h0 (tkrChi_eq_zero (not_lt.1 hcon) hη)
      have : Whole.chi ((η / 4) • Lattice.toEuc k) = 1 := by
        apply Whole.cmxFB_chi_one
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        unfold Lattice.enorm at h2
        nlinarith
      rw [this]
      exact Whole.cmxFB_chi_le_one _
  have hχ0 : 0 ≤ tkrChi η k := Whole.cmxFB_chi_nonneg _
  have hχ1 : 0 ≤ Whole.chi ((η / 4) • Lattice.toEuc k) := Whole.cmxFB_chi_nonneg _
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hχ0, abs_of_nonneg hχ1,
    abs_of_nonneg (Real.rpow_nonneg htpos.le (Whole.alphaE d s - 1)), hcoef]
  have key := tsamp_real_pow_bound (g := 0) htpos hα (abs_nonneg (rieszConst d s))
    (by positivity : 0 ≤ 2 * Real.pi * |((k j : ℤ) : ℝ)|) hkj
  have hg0 : 0 ≤ ‖σc k‖ := norm_nonneg _
  calc t ^ (Whole.alphaE d s - 1) * (tkrChi η k * (2 * Real.pi * |((k j : ℤ) : ℝ)| *
          (|rieszConst d s| * t ^ (s - d))) * ‖σc k‖)
      = tkrChi η k * (t ^ (Whole.alphaE d s - 1) * (2 * Real.pi * |((k j : ℤ) : ℝ)| *
          (|rieszConst d s| * t ^ (s - d)))) * ‖σc k‖ := by ring
    _ ≤ Whole.chi ((η / 4) • Lattice.toEuc k) * (|rieszConst d s| * t ^ (-Whole.alphaE d s)) * ‖σc k‖ := by
        gcongr
    _ = |rieszConst d s| * t ^ (-Whole.alphaE d s) *
          (Whole.chi ((η / 4) • Lattice.toEuc k) * ‖σc k‖) := by ring


lemma tsamp_eLpNorm_trig {n : ℕ} {c : Lattice d → ℂ} (hc : HRS.PDE.IsTrigPoly n c) {f : Torus d → ℝ}
    (hfc : Continuous f) (hf : ∀ x, ((f x : ℝ) : ℂ) = HRS.PDE.Kern.trig c x) :
    eLpNorm f 2 volume =
      ENNReal.ofReal ((∑ k ∈ HRS.PDE.Kern.boxF d n, ‖c k‖ ^ 2) ^ ((2 : ℝ)⁻¹)) := by
  have hmem : MemLp f 2 volume := HRS.PDE.R2Aux.memLp_of_continuous_real hfc
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  congr 2
  have : ∀ x, ‖f x‖ ^ (2 : ℝ) = ‖HRS.PDE.Kern.trig c x‖ ^ 2 := by
    intro x
    rw [← hf x, Complex.norm_real, Real.rpow_two]
  simp_rw [this]
  exact HRS.PDE.Kern.integral_norm_sq_trig hc

lemma tsamp_sum_le_hom (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ} (hη : 0 < η)
    (σ : SMT d) (j : Fin d) (n : ℕ) :
    ENNReal.ofReal (∑ k ∈ HRS.PDE.Kern.boxF d n,
        ‖((((if k = 0 then 0 else (2 * Real.pi * Lattice.enorm k) ^ (Whole.alphaE d s - 1) : ℝ)) : ℂ)) *
          (((tkrChi η k : ℝ) : ℂ) * tkrCI d s j k * σ.coef k)‖ ^ 2) ≤
      ENNReal.ofReal (rieszConst d s ^ 2) * homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  unfold homSqT
  rw [← ENNReal.tsum_mul_left]
  refine (Finset.sum_le_sum fun k _ => ?_).trans (ENNReal.sum_le_tsum (HRS.PDE.Kern.boxF d n))
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, if_false]
    have hb := tsamp_coeff_bound hd hs0 hsd hη σ.coef j k hk
    set t : ℝ := 2 * Real.pi * Lattice.enorm k with ht
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
    have htpos : 0 < t := by
      have := HRS.one_le_enorm k hk
      rw [ht]; positivity
    rw [mul_pow, mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    have e1 : (t ^ (-Whole.alphaE d s)) ^ 2 = t ^ (2 * (-Whole.alphaE d s)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul htpos.le]; congr 1; push_cast; ring
    have e2 : |rieszConst d s| ^ 2 = rieszConst d s ^ 2 := sq_abs _
    have e3 : ENNReal.ofReal (‖((Whole.chi ((η / 4) • Lattice.toEuc k) : ℝ) : ℂ) * σ.coef k‖ ^ 2) =
        ‖lowFreqT η 4 σ.coef k‖ₑ ^ 2 := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rfl
    rw [e1, e2, e3]
    ring

end HRS.Commutator.TorusNote
