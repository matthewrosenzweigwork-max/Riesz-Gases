import HRS.Commutator.Torus.TPOSAux16
import HRS.Commutator.Torus.TENAux1
import HRS.Commutator.Torus.TENAux4

/-!
# Torus energy layer (packet T-EN2), helper part 1: elementary facts

Prefix `ten2_`.  `‖ρ‖_p ≥ 1` for a unit-mass density, finiteness of the charge `ν = μ_N - μ`, positivity of
`‖ν‖²_{g_η}` and the lower bound `f_η^𝕋 ≥ -Kη^{d-s}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

/-- `‖ρ‖_p ≥ 1` for a density of mass one on the unit-volume torus (`1 ≤ p`). -/
theorem ten2_normT_ge_one {p : ℝ≥0∞} (hp : 1 ≤ p) {ρ : Torus d → ℝ} (hρ : BddDensityT ρ) :
    1 ≤ normT p ρ := by
  obtain ⟨B, hB⟩ := hρ.bdd
  have hmem : MemLp ρ p volume :=
    MemLp.of_bound hρ.measurable.aestronglyMeasurable B
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hB x)
  have hint : Integrable ρ :=
    ten_integrable_of_bdd (μ := volume) hρ.measurable B (fun x => by
      rw [Real.norm_eq_abs]; exact hB x)
  have h1 : eLpNorm ρ 1 volume ≤ eLpNorm ρ p volume :=
    eLpNorm_le_eLpNorm_of_exponent_le hp
  have h2 : (eLpNorm ρ 1 volume).toReal ≤ (eLpNorm ρ p volume).toReal :=
    ENNReal.toReal_mono hmem.eLpNorm_lt_top.ne h1
  have h3 : (eLpNorm ρ 1 volume).toReal = ∫ x, ‖ρ x‖ := by
    rw [eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable, integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable]
  have h4 : 1 ≤ ∫ x, ‖ρ x‖ := by
    calc (1 : ℝ) = ∫ x, ρ x := hρ.mass.symm
      _ ≤ ∫ x, ‖ρ x‖ := integral_mono hint hint.norm fun x => Real.le_norm_self _
  unfold normT
  linarith

/-- The charge `ν = μ_N - μ` of a bounded density is finite. -/
theorem ten2_charge_finite {N : ℕ} (hN : 1 ≤ N) (X : Config d N) {ρ : Torus d → ℝ}
    (hρ : BddDensityT ρ) : (chargeT X ρ).IsFinite := by
  obtain ⟨B, hB⟩ := hρ.bdd
  have hint : Integrable ρ :=
    ten_integrable_of_bdd (μ := volume) hρ.measurable B (fun x => by
      rw [Real.norm_eq_abs]; exact hB x)
  have hN0 : 0 < N := by omega
  have := HRS.empirical_isProbabilityMeasure hN0 X
  refine ⟨?_, ?_⟩
  · show IsFiniteMeasure (HRS.empirical X + volume.withDensity fun x => ENNReal.ofReal (-ρ x))
    have : IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (-ρ x)) :=
      isFiniteMeasure_withDensity_ofReal hint.neg.hasFiniteIntegral
    infer_instance
  · show IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (ρ x))
    exact isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral

/-- `‖ν‖²_{g_η} ≥ 0` (all `η > 0`; the Fourier coefficients of `g_η^𝕋` are nonnegative). -/
theorem ten2_kerEnergy_nonneg (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η)
    {N : ℕ} (hN : 1 ≤ N) (X : Config d N) {ρ : Torus d → ℝ} (hρ : BddDensityT ρ) :
    0 ≤ kerEnergyT (gTorus s η) (chargeT X ρ) := by
  obtain ⟨-, hcoef, hsumm, hlift⟩ := tpos_coef_formula hd hs0 hsd η hη
  have hG : Continuous (gTorus s η) := HRS.Torus.continuous_of_continuous_lift hlift
  rw [ten_kerEnergy_fourier _ (ten2_charge_finite hN X hρ) hG hsumm hcoef]
  exact tsum_nonneg fun k => mul_nonneg (tpos_gTcoef_nonneg hs0 hsd hη k) (sq_nonneg _)

/-- The constant `K_s = tScale·c_φ∫φ/(d-s)`: the mean of `perio f_η` is `K_s η^{d-s}`. -/
def ten2K (d : ℕ) (s : ℝ) : ℝ := tScale s * (Whole.cPhi d s * (∫ x : Euc d, Whole.phi x) / ((d : ℝ) - s))

theorem ten2K_nonneg (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) : 0 ≤ ten2K d s := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith
  have hcp := Whole.cPhi_pos d hs0 hs2
  have hphi : 0 ≤ ∫ x : Euc d, Whole.phi x :=
    integral_nonneg fun x => (Whole.phiR_pos (d := d) _).le
  have hds : 0 < (d : ℝ) - s := by linarith
  unfold ten2K
  have := tpos_tScale_pos hs0
  positivity

/-- `f_η^𝕋(x) ≥ -K_s η^{d-s}`. -/
theorem ten2_fTorus_lower (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η)
    (x : Torus d) : -(ten2K d s * η ^ ((d : ℝ) - s)) ≤ fTorus s η x := by
  have hP : 0 ≤ perio (Whole.fTrunc s η : Euc d → ℝ) x :=
    tpos_perio_nonneg (fun z => tpos_fTrunc_nonneg hs0 (by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith) η z) x
  have hts := tpos_tScale_pos hs0
  have hm := tpos_integral_perio_fTrunc (d := d) hs0 hsd hη
  unfold fTorus
  rw [hm]
  unfold ten2K
  have : tScale s * (perio (Whole.fTrunc s η : Euc d → ℝ) x -
      Whole.cPhi d s * (∫ x : Euc d, Whole.phi x) / ((d : ℝ) - s) * η ^ ((d : ℝ) - s)) ≥
      -(tScale s * (Whole.cPhi d s * (∫ x : Euc d, Whole.phi x) / ((d : ℝ) - s)) * η ^ ((d : ℝ) - s)) := by
    nlinarith [mul_nonneg hts.le hP]
  linarith

end HRS.Commutator.TorusNote
