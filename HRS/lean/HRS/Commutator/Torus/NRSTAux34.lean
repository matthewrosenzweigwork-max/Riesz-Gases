import HRS.Commutator.Torus.NRSTAux33

/-!
# NRS-T, part 34: Parseval in the `L²` norm, Bessel weights, real-valued trigonometric polynomials
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

/-- Parseval for trigonometric polynomials in the `L²(𝕋^d)` norm. -/
lemma nrstr_pars (f : NRST.TPA d) :
    eLpNorm (NRST.ev f) 2 volume =
      ENNReal.ofReal (Real.sqrt (∑ k ∈ f.coeff.support, ‖f.coeff k‖ ^ 2)) := by
  have hcont := NRST.continuous_ev f
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2t : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2t]
  have e1 : ∫⁻ x, ‖NRST.ev f x‖ₑ ^ ((2 : ℝ≥0∞).toReal) =
      ENNReal.ofReal (∑ k ∈ f.coeff.support, ‖f.coeff k‖ ^ 2) := by
    rw [← NRST.integral_ev_mul_conj]
    have hi : Integrable (fun x => ‖NRST.ev f x‖ ^ 2) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · exact (hcont.norm).pow 2
      · exact HasCompactSupport.of_compactSpace _
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, show ((2 : ℝ≥0∞).toReal) = 2 by simp,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  rw [e1]
  have hS : 0 ≤ ∑ k ∈ f.coeff.support, ‖f.coeff k‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hS (by norm_num), Real.sqrt_eq_rpow]
  norm_num
  exact hcont.aestronglyMeasurable

/-- Comparison of `L²` norms from a coefficientwise bound. -/
lemma nrstr_N2_le {g f : NRST.TPA d} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ k, ‖g.coeff k‖ ≤ c * ‖f.coeff k‖) :
    eLpNorm (NRST.ev g) 2 volume ≤ ENNReal.ofReal c * eLpNorm (NRST.ev f) 2 volume := by
  rw [nrstr_pars, nrstr_pars, ← ENNReal.ofReal_mul hc]
  refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩)
  rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity), Finset.mul_sum]
  have hsub : g.coeff.support ⊆ f.coeff.support := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk ⊢
    intro hf
    apply hk
    have := h k
    rw [hf, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  calc ∑ k ∈ g.coeff.support, ‖g.coeff k‖ ^ 2 ≤ ∑ k ∈ f.coeff.support, ‖g.coeff k‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ k ∈ f.coeff.support, c ^ 2 * ‖f.coeff k‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (h k) 2

lemma nrstr_N2_lam (β : ℝ) (f : NRST.TPA d) :
    eLpNorm (NRST.ev (NRST.lam β f)) 2 volume = ENNReal.ofReal (Real.sqrt (NRST.hom β f)) := by
  classical
  rw [nrstr_pars]
  congr 2
  unfold NRST.hom
  refine Finset.sum_subset_zero_on_sdiff (NRST.supp_mulSeq_subset _ f) (fun k hk => ?_) (fun k hk => ?_)
  · have hk' := Finset.mem_sdiff.1 hk
    have : (NRST.lam β f).coeff k = 0 := by simpa using hk'.2
    simp only [NRST.lam, NRST.coeff_mulSeq, mul_eq_zero, Complex.ofReal_eq_zero] at this
    rcases this with h | h <;> simp [h]
  · unfold NRST.lam
    rw [NRST.coeff_mulSeq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The Bessel weight `(1+4π²|k|²)^{τ/2}` (period one). -/
def nrstr_jb (τ : ℝ) (k : Lattice d) : ℝ := (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ (τ / 2)

lemma nrstr_jb_pos (τ : ℝ) (k : Lattice d) : 0 < nrstr_jb τ k := by
  unfold nrstr_jb; positivity

lemma nrstr_jb_neg (τ : ℝ) (k : Lattice d) : nrstr_jb τ (-k) = nrstr_jb τ k := by
  unfold nrstr_jb; rw [NRST.enorm_neg]

/-- The Bessel derivative of a trigonometric polynomial. -/
def nrstr_Jb (τ : ℝ) (f : NRST.TPA d) : NRST.TPA d := NRST.mulSeq (fun k => ((nrstr_jb τ k : ℝ) : ℂ)) f

lemma nrstr_lw_le_jb {τ : ℝ} (hτ : 0 ≤ τ) (k : Lattice d) : NRST.lw τ k ≤ nrstr_jb τ k := by
  by_cases hk : k = 0
  · simp [hk, NRST.lw_zero, (nrstr_jb_pos τ 0).le]
  · unfold NRST.lw nrstr_jb
    rw [if_neg hk]
    have he := NRST.enorm_nonneg k
    have : (2 * Real.pi * Lattice.enorm k) ^ τ = ((2 * Real.pi * Lattice.enorm k) ^ 2) ^ (τ / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
    rw [this]
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    nlinarith [sq_nonneg (2 * Real.pi * Lattice.enorm k)]

lemma nrstr_jb_le_lw {τ : ℝ} (hτ : 0 ≤ τ) {k : Lattice d} (hk : k ≠ 0) :
    nrstr_jb τ k ≤ 2 ^ (τ / 2) * NRST.lw τ k := by
  unfold NRST.lw nrstr_jb
  rw [if_neg hk]
  have he1 : 1 ≤ Lattice.enorm k := nrstr_one_le_enorm hk
  have hπ : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have : (2 * Real.pi * Lattice.enorm k) ^ τ = ((2 * Real.pi * Lattice.enorm k) ^ 2) ^ (τ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
  rw [this, ← Real.mul_rpow (by norm_num) (by positivity)]
  refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  have : 1 ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by nlinarith
  nlinarith

lemma nrstr_N2_lam_le_Jb {τ : ℝ} (hτ : 0 ≤ τ) (f : NRST.TPA d) :
    eLpNorm (NRST.ev (NRST.lam τ f)) 2 volume ≤ eLpNorm (NRST.ev (nrstr_Jb τ f)) 2 volume := by
  have := nrstr_N2_le (g := NRST.lam τ f) (f := nrstr_Jb τ f) (c := 1) zero_le_one (fun k => by
    unfold NRST.lam nrstr_Jb
    rw [NRST.coeff_mulSeq, NRST.coeff_mulSeq, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (NRST.lw_nonneg _ _),
      abs_of_nonneg (nrstr_jb_pos _ _).le, one_mul]
    exact mul_le_mul_of_nonneg_right (nrstr_lw_le_jb hτ k) (norm_nonneg _))
  simpa using this

lemma nrstr_N2_Jb_le {τ : ℝ} (hτ : 0 ≤ τ) (g : NRST.TPA d) (hg0 : g.coeff 0 = 0) :
    eLpNorm (NRST.ev (nrstr_Jb τ g)) 2 volume ≤
      ENNReal.ofReal (2 ^ (τ / 2)) * eLpNorm (NRST.ev (NRST.lam τ g)) 2 volume := by
  refine nrstr_N2_le (by positivity) (fun k => ?_)
  unfold NRST.lam nrstr_Jb
  rw [NRST.coeff_mulSeq, NRST.coeff_mulSeq, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (NRST.lw_nonneg _ _),
    abs_of_nonneg (nrstr_jb_pos _ _).le, ← mul_assoc]
  by_cases hk : k = 0
  · subst hk; simp [hg0]
  · exact mul_le_mul_of_nonneg_right (nrstr_jb_le_lw hτ hk) (norm_nonneg _)

end HRS.Commutator.TorusNote
