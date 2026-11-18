import HRS.MS.FixEqP3Aux12

/-!
# S5.7 `fixed_equation` (worker S57P), part 25: the Gram identity `⟪κ_t φ, κ_{t'} ψ⟫ = noiseCovW`
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

theorem s57p_inner_toLp {T : ℝ} {f g : ℝ × Euc d → Euc d} (hf : MemLp f 2 (s57pμ d T)) (hg : MemLp g 2 (s57pμ d T)) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ p, inner ℝ (f p) (g p) ∂(s57pμ d T) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with a ha hb
  rw [ha, hb]

theorem s57p_gram {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ} {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hD : S57pFeData s Q ν c ρ T) (hT : 0 ≤ T) {q : ℝ} (hq : 0 ≤ q)
    (hprob : ∀ t ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (ρ t)) {φ ψ : Euc d → ℝ} {t t' : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (ht' : t' ∈ Set.Icc (0 : ℝ) T)
    (hAφ : Continuous (s57pA (fixedEqCoeff s M Q ν c ρ) t φ)) (hAψ : Continuous (s57pA (fixedEqCoeff s M Q ν c ρ) t' ψ))
    {B1 B2 : ℝ} (hB1 : ∀ p, ‖s57pA (fixedEqCoeff s M Q ν c ρ) t φ p‖ ≤ B1)
    (hB2 : ∀ p, ‖s57pA (fixedEqCoeff s M Q ν c ρ) t' ψ p‖ ≤ B2) :
    inner ℝ (s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t φ) (s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t' ψ) =
      noiseCovW (fixedEqCoeff s M Q ν c ρ) q t t' φ ψ := by
  set C := fixedEqCoeff s M Q ν c ρ with hC
  have hwd := s57p_wdata hD hT hq hprob
  have hM1 := s57p_kf_memLp hwd hAφ.aestronglyMeasurable (t := t) (Ba := B1) (fun p _ => hB1 p)
  have hM2 := s57p_kf_memLp hwd hAψ.aestronglyMeasurable (t := t') (Ba := B2) (fun p _ => hB2 p)
  unfold s57pκ
  rw [s57p_el_eq hM1, s57p_el_eq hM2, s57p_inner_toLp hM1 hM2]
  set m := min t t' with hm
  have hm0 : 0 ≤ m := le_min ht.1 ht'.1
  have hmT : m ≤ T := (min_le_left _ _).trans ht.2
  set F : ℝ × Euc d → ℝ := fun p => if p.1 ≤ m then (2 * q * ρ p.1 p.2) *
    inner ℝ (s57pA C t φ p) (s57pA C t' ψ p) else 0 with hF
  have hpt : ∀ᵐ p ∂(s57pμ d T), inner ℝ (s57pkf (s57pw T q ρ) (s57pA C t φ) t p)
      (s57pkf (s57pw T q ρ) (s57pA C t' ψ) t' p) = F p := by
    filter_upwards [s57p_ae_fst (d := d) T] with p hp
    have hcl : max 0 (min p.1 T) = p.1 := by rw [min_eq_left hp.2, max_eq_right hp.1]
    have hw2 : s57pw T q ρ p * s57pw T q ρ p = 2 * q * ρ p.1 p.2 := by
      simp only [s57pw, s57pρc, hcl]
      exact Real.mul_self_sqrt (mul_nonneg (by positivity) ((hprob p.1 hp).nonneg p.2))
    simp only [s57pkf, hF, hm, le_min_iff]
    by_cases h1 : p.1 ≤ t <;> by_cases h2 : p.1 ≤ t' <;> simp [h1, h2, real_inner_smul_left, real_inner_smul_right, ← hw2]
    ring
  rw [integral_congr_ae hpt]
  have hint : Integrable F (s57pμ d T) := by
    have := L2.integrable_inner (𝕜 := ℝ) (hM1.toLp _) (hM2.toLp _)
    refine this.congr ?_
    filter_upwards [hM1.coeFn_toLp, hM2.coeFn_toLp, hpt] with p h1 h2 h3
    rw [h1, h2, h3]
  unfold s57pμ at hint ⊢
  rw [integral_prod F hint]
  have hin : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫ x, F (r, x) = if r ≤ m then 2 * q * ∫ x, inner ℝ
      (gradient (propagatorW C r t φ) x) (gradient (propagatorW C r t' ψ) x) * ρ r x else 0 := by
    intro r hr
    by_cases hrm : r ≤ m
    · have e1 : max 0 (min r t) = r := by rw [min_eq_left (hrm.trans (min_le_left _ _)), max_eq_right hr.1]
      have e2 : max 0 (min r t') = r := by rw [min_eq_left (hrm.trans (min_le_right _ _)), max_eq_right hr.1]
      simp only [hF, hrm, if_true, s57pA, e1, e2]
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      ring
    · simp [hF, hrm]
  rw [setIntegral_congr_fun measurableSet_Icc (fun r hr => hin r hr)]
  have e : (fun r : ℝ => if r ≤ m then 2 * q * ∫ x, inner ℝ (gradient (propagatorW C r t φ) x)
      (gradient (propagatorW C r t' ψ) x) * ρ r x else 0) =
      (Set.Iic m).indicator (fun r => 2 * q * ∫ x, inner ℝ (gradient (propagatorW C r t φ) x)
        (gradient (propagatorW C r t' ψ) x) * ρ r x) := by
    funext r; simp [Set.indicator_apply]
  rw [e, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have eI : Set.Iic m ∩ Set.Icc (0 : ℝ) T = Set.Icc 0 m := by
    ext r; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hmT⟩
  rw [eI, integral_const_mul]
  rfl

end HRS.MS.FixEq
