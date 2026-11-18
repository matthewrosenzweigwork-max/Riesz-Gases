import HRS.MS.SA16Y3S5b

/-!
# S.A.16 (SA16Y4) S5d: zeroth-component pairings with test functions converging in `L^{p'}`

`sa16y4_ell_Lq_bound`: `|∫ wrep G · N| ≤ ‖G‖ ‖N‖_{L^{p'}}` (`p' = ENNReal.conjExponent (ofReal p)`).
`sa16y4_pair_tendsto_Lq`: if `g_j` are bounded by `Bm` and converge weakly to `G`, and `N_j → N` in `L^{p'}`, then
`∫ wrep g_j · N_j → ∫ wrep G · N`.  (Used for the nonlocal test function `nonlocalTestRd(ρ_n ⋆ μ) ψ → nonlocalTestRd(μ) ψ`.)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section S5d
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y4_holderConj : (ENNReal.ofReal p).HolderConjugate (ENNReal.conjExponent (ENNReal.ofReal p)) :=
  ENNReal.HolderConjugate.conjExponent (by
    have hp2 : (2 : ℝ) ≤ p := Fact.out
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))

theorem sa16y4_ell_Lq_bound {m : ℕ} (G : WmpSpace d m p) {N : Euc d → ℝ}
    (hNm : AEStronglyMeasurable N volume) (hN : MemLp N (ENNReal.conjExponent (ENNReal.ofReal p)) volume) :
    |∫ x, wrep d m p G x * N x| ≤ ‖G‖ * (eLpNorm N (ENNReal.conjExponent (ENNReal.ofReal p)) volume).toReal := by
  haveI := sa16y4_holderConj (p := p)
  have hw : AEStronglyMeasurable (fun x => wrep d m p G x) volume := sa16y3_wrep_aesm G
  have h1 : |∫ x, wrep d m p G x * N x| ≤ ∫ x, ‖wrep d m p G x * N x‖ := by
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := (volume : Measure (Euc d)))
      (fun x => wrep d m p G x * N x)
  refine h1.trans ?_
  have hmul : AEStronglyMeasurable (fun x => wrep d m p G x * N x) volume := hw.mul hNm
  rw [integral_norm_eq_lintegral_enorm hmul]
  have h2 : eLpNorm (fun x => wrep d m p G x * N x) 1 volume ≤
      eLpNorm (fun x => wrep d m p G x) (ENNReal.ofReal p) volume *
        eLpNorm N (ENNReal.conjExponent (ENNReal.ofReal p)) volume := by
    have := eLpNorm_smul_le_mul_eLpNorm (μ := (volume : Measure (Euc d))) (p := ENNReal.ofReal p)
      (q := ENNReal.conjExponent (ENNReal.ofReal p)) (r := 1) hw hNm
    exact this
  rw [← eLpNorm_one_eq_lintegral_enorm hmul]
  have h3 := sa16y3_wrep_eLp G
  have hfin : eLpNorm N (ENNReal.conjExponent (ENNReal.ofReal p)) volume ≠ ⊤ := hN.eLpNorm_lt_top.ne
  have h4 : eLpNorm (fun x => wrep d m p G x * N x) 1 volume ≤
      ENNReal.ofReal ‖G‖ * eLpNorm N (ENNReal.conjExponent (ENNReal.ofReal p)) volume :=
    h2.trans (mul_le_mul' h3 le_rfl)
  have h5 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h4
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)] at h5

theorem sa16y4_pair_tendsto_Lq {m : ℕ} {Bm : ℝ} (gs : ℕ → WmpSpace d m p) (G : WmpSpace d m p)
    (hbd : ∀ j, ‖gs j‖ ≤ Bm)
    (hw : ∀ ℓ : StrongDual ℝ (WmpSpace d m p), Tendsto (fun j => ℓ (gs j)) atTop (𝓝 (ℓ G)))
    (Nn : ℕ → Euc d → ℝ) (N : Euc d → ℝ)
    (hNjm : ∀ j, AEStronglyMeasurable (Nn j) volume) (hNm : AEStronglyMeasurable N volume)
    (hNj : ∀ j, MemLp (Nn j) (ENNReal.conjExponent (ENNReal.ofReal p)) volume)
    (hN : MemLp N (ENNReal.conjExponent (ENNReal.ofReal p)) volume)
    (hconv : Tendsto (fun j => (eLpNorm (fun x => Nn j x - N x) (ENNReal.conjExponent (ENNReal.ofReal p)) volume).toReal)
      atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, wrep d m p (gs j) x * Nn j x) atTop (𝓝 (∫ x, wrep d m p G x * N x)) := by
  have hBm : 0 ≤ Bm := (norm_nonneg _).trans (hbd 0)
  have hwj : ∀ j, MemLp (fun x => wrep d m p (gs j) x) (ENNReal.ofReal p) volume := fun j => sa16y3_wrep_memLp _
  have h1 : Tendsto (fun j => ∫ x, wrep d m p (gs j) x * N x) atTop (𝓝 (∫ x, wrep d m p G x * N x)) := by
    simp_rw [← sa16so_ellN_apply m hN]
    exact hw _
  have hdiff : ∀ j, |(∫ x, wrep d m p (gs j) x * Nn j x) - ∫ x, wrep d m p (gs j) x * N x| ≤
      Bm * (eLpNorm (fun x => Nn j x - N x) (ENNReal.conjExponent (ENNReal.ofReal p)) volume).toReal := by
    intro j
    have hi1 : Integrable (fun x => wrep d m p (gs j) x * Nn j x) :=
      (hwj j).integrable_mul (hNj j)
    have hi2 : Integrable (fun x => wrep d m p (gs j) x * N x) := (hwj j).integrable_mul hN
    have : (∫ x, wrep d m p (gs j) x * Nn j x) - ∫ x, wrep d m p (gs j) x * N x =
        ∫ x, wrep d m p (gs j) x * (Nn j x - N x) := by
      rw [← integral_sub hi1 hi2]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [this]
    exact (sa16y4_ell_Lq_bound (gs j) ((hNjm j).sub hNm) ((hNj j).sub hN)).trans
      (mul_le_mul_of_nonneg_right (hbd j) ENNReal.toReal_nonneg)
  have h2 : Tendsto (fun j => (∫ x, wrep d m p (gs j) x * Nn j x) - ∫ x, wrep d m p (gs j) x * N x)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => ?_) (by simpa using hconv.const_mul Bm)
    rw [Real.norm_eq_abs]; exact hdiff j
  simpa using h2.add h1

end S5d

end HRS.Whole.AppendixA.Phase2SA16R
