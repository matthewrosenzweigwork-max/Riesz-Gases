import HRS.Torus.Sobolev
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# E214F-Gauss: moment comparison for centred Gaussian processes valued in `E_m = ℓ²`

`gaussian_rpow_moment`: a centred real Gaussian `ξ` has `E|ξ|^s ≤ c_s (E ξ²)^{s/2}`.
`lintegral_norm_rpow_le`: if every coordinate of a random element `Z` of `NegSobolev d m` is a centred
real Gaussian with `E ξ_k² ≤ w_k`, then `E ‖Z‖^s ≤ C_s (∑ w_k)^{s/2}` for `s ≥ 2`
(Minkowski in `L^{s/2}` applied to `‖Z‖² = ∑ ξ_k²`).  No joint Gaussianity of the coordinates is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.E214F

theorem gaussian_rpow_moment {s : ℝ} (hs : 0 < s) :
    ∃ cs : ℝ, 0 ≤ cs ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ξ : Ω → ℝ), HasGaussianLaw ξ μ → μ[ξ] = 0 →
      ∫⁻ ω, ‖ξ ω‖ₑ ^ s ∂μ ≤ ENNReal.ofReal (cs * (∫ ω, ξ ω ^ 2 ∂μ) ^ (s / 2)) := by
  set m : ℝ≥0∞ := ∫⁻ z, ‖z‖ₑ ^ s ∂(gaussianReal 0 1) with hm
  have hfin : m ≠ ⊤ := by
    have hmem := memLp_id_gaussianReal' (μ := 0) (v := 1) (ENNReal.ofReal s) ENNReal.ofReal_ne_top
    have hlt := hmem.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hs) ENNReal.ofReal_ne_top
      hmem.aestronglyMeasurable] at hlt
    rw [ENNReal.toReal_ofReal hs.le] at hlt
    have := ENNReal.rpow_lt_top_iff_of_pos (inv_pos.2 hs) |>.1 (by simpa using hlt)
    simpa [hm] using this.ne
  refine ⟨m.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro Ω _ μ _ ξ hξ h0
  have hmap := hξ.map_eq_gaussianReal
  rw [h0] at hmap
  have hvar : Var[ξ; μ] = ∫ ω, ξ ω ^ 2 ∂μ :=
    variance_of_integral_eq_zero hξ.aemeasurable h0
  have hv0 : 0 ≤ ∫ ω, ξ ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  set v : ℝ≥0 := Var[ξ; μ].toNNReal with hv
  have hvv : (v : ℝ) = ∫ ω, ξ ω ^ 2 ∂μ := by
    rw [hv, Real.coe_toNNReal _ (variance_nonneg _ _), hvar]
  have hlaw : gaussianReal 0 v = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt v.coe_nonneg]
  calc ∫⁻ ω, ‖ξ ω‖ₑ ^ s ∂μ = ∫⁻ x, ‖x‖ₑ ^ s ∂(μ.map ξ) := by
        rw [lintegral_map' (measurable_enorm.pow_const s).aemeasurable hξ.aemeasurable]
    _ = ∫⁻ z, ‖Real.sqrt v * z‖ₑ ^ s ∂(gaussianReal 0 1) := by
        rw [hmap, hlaw, lintegral_map (by fun_prop) (by fun_prop)]
    _ = ENNReal.ofReal (Real.sqrt v ^ s) * m := by
        rw [hm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun z => ?_
        rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hs.le]
        congr 1
        rw [← ofReal_norm, Real.norm_of_nonneg (Real.sqrt_nonneg _), ENNReal.ofReal_rpow_of_nonneg
          (Real.sqrt_nonneg _) hs.le]
    _ = ENNReal.ofReal (m.toReal * (∫ ω, ξ ω ^ 2 ∂μ) ^ (s / 2)) := by
        rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.sqrt_nonneg _) _)]
        simp only [ENNReal.ofReal_toReal hfin]
        congr 1
        rw [mul_comm, Real.sqrt_eq_rpow, ← Real.rpow_mul v.coe_nonneg, ← hvv]
        congr 2
        ring
    _ ≤ _ := le_rfl

section Hilbert

variable {d : ℕ} {m : ℝ}

theorem enorm_rpow_eq_tsum (z : NegSobolev d m) {s : ℝ} (hs : 0 < s) :
    ‖z‖ₑ ^ s = (∑' k : NonzeroLattice d, ENNReal.ofReal (NegSobolev.coord z k ^ 2)) ^ (s / 2) := by
  obtain ⟨hsum, hnorm⟩ := NegSobolev.coord_sq z
  have h1 : ∑' k : NonzeroLattice d, ENNReal.ofReal (NegSobolev.coord z k ^ 2) =
      ENNReal.ofReal (‖z‖ ^ 2) := by
    rw [hnorm, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hsum]
  rw [h1, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs.le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast; ring

theorem eLpNorm_sq_le {s cs : ℝ} (hs : 2 ≤ s) (hcs : 0 ≤ cs)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Ω → ℝ)
    (hξ : HasGaussianLaw ξ μ)
    (hmom : ∫⁻ ω, ‖ξ ω‖ₑ ^ s ∂μ ≤ ENNReal.ofReal (cs * (∫ ω, ξ ω ^ 2 ∂μ) ^ (s / 2))) :
    eLpNorm (fun ω => ξ ω ^ 2) (ENNReal.ofReal (s / 2)) μ ≤
      ENNReal.ofReal (cs ^ (2 / s) * ∫ ω, ξ ω ^ 2 ∂μ) := by
  have hq : 0 < s / 2 := by linarith
  have hv0 : 0 ≤ ∫ ω, ξ ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq) ENNReal.ofReal_ne_top
    ((hξ.aemeasurable.pow_const 2).aestronglyMeasurable), ENNReal.toReal_ofReal hq.le]
  have h1 : ∀ ω, ‖ξ ω ^ 2‖ₑ ^ (s / 2) = ‖ξ ω‖ₑ ^ s := by
    intro ω
    rw [enorm_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    push_cast; ring
  simp_rw [h1]
  calc (∫⁻ ω, ‖ξ ω‖ₑ ^ s ∂μ) ^ (1 / (s / 2))
      ≤ (ENNReal.ofReal (cs * (∫ ω, ξ ω ^ 2 ∂μ) ^ (s / 2))) ^ (1 / (s / 2)) :=
        ENNReal.rpow_le_rpow hmom (by positivity)
    _ = ENNReal.ofReal ((cs * (∫ ω, ξ ω ^ 2 ∂μ) ^ (s / 2)) ^ (1 / (s / 2))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    _ = _ := by
        congr 1
        rw [Real.mul_rpow hcs (by positivity), ← Real.rpow_mul hv0]
        rw [show s / 2 * (1 / (s / 2)) = 1 by field_simp, Real.rpow_one,
          show 1 / (s / 2) = 2 / s by field_simp]

/-- `E ‖Z‖^s ≤ C (∑ w_k)^{s/2}` when the coordinates of `Z` are centred real Gaussians with
`E ξ_k² ≤ w_k` (no joint Gaussianity needed), `s ≥ 2`. -/
theorem lintegral_norm_rpow_le {s : ℝ} (hs : 2 ≤ s) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Z : Ω → NegSobolev d m) (w : NonzeroLattice d → ℝ), (∀ k, 0 ≤ w k) → Summable w →
      (∀ k, HasGaussianLaw (fun ω => NegSobolev.coord (Z ω) k) μ) →
      (∀ k, ∫ ω, NegSobolev.coord (Z ω) k ∂μ = 0) →
      (∀ k, ∫ ω, NegSobolev.coord (Z ω) k ^ 2 ∂μ ≤ w k) →
      ∫⁻ ω, ‖Z ω‖ₑ ^ s ∂μ ≤ ENNReal.ofReal (Cg * (∑' k, w k) ^ (s / 2)) := by
  obtain ⟨cs, hcs, hgm⟩ := gaussian_rpow_moment (show 0 < s by linarith)
  refine ⟨cs, hcs, ?_⟩
  intro Ω _ μ _ Z w hw0 hw hG hc hv
  have hq : 1 ≤ s / 2 := by linarith
  have hq0 : 0 < s / 2 := by linarith
  set S : ℝ := ∑' k, w k with hS
  have hS0 : 0 ≤ S := tsum_nonneg hw0
  set ξ : NonzeroLattice d → Ω → ℝ := fun k ω => NegSobolev.coord (Z ω) k with hξ
  have hmeasξ : ∀ k, AEMeasurable (ξ k) μ := fun k => (hG k).aemeasurable
  -- finite sums
  have hfin : ∀ F : Finset (NonzeroLattice d),
      ∫⁻ ω, (∑ k ∈ F, ENNReal.ofReal (ξ k ω ^ 2)) ^ (s / 2) ∂μ ≤ ENNReal.ofReal (cs * S ^ (s / 2)) := by
    intro F
    have hnorm : ∀ ω, (∑ k ∈ F, ENNReal.ofReal (ξ k ω ^ 2)) = ‖∑ k ∈ F, ξ k ω ^ 2‖ₑ := by
      intro ω
      rw [← ofReal_norm, Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _),
        ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
    have hmink := eLpNorm_sum_le (μ := μ) (f := fun k ω => ξ k ω ^ 2) (s := F)
      (p := ENNReal.ofReal (s / 2)) (by simpa using hq)
    have hbound : ∀ k, eLpNorm (fun ω => ξ k ω ^ 2) (ENNReal.ofReal (s / 2)) μ ≤
        ENNReal.ofReal (cs ^ (2 / s) * w k) := by
      intro k
      refine (eLpNorm_sq_le hs hcs μ (ξ k) (hG k) (hgm μ (ξ k) (hG k) (hc k))).trans ?_
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hv k) (by positivity))
    have h1 : eLpNorm (∑ k ∈ F, fun ω => ξ k ω ^ 2) (ENNReal.ofReal (s / 2)) μ ≤
        ENNReal.ofReal (cs ^ (2 / s) * S) := by
      refine hmink.trans ((Finset.sum_le_sum fun k _ => hbound k).trans ?_)
      rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => by have := hw0 k; positivity]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hw.sum_le_tsum F (fun k _ => hw0 k)) (by positivity)
    have h2 : (∫⁻ ω, ‖∑ k ∈ F, ξ k ω ^ 2‖ₑ ^ (s / 2) ∂μ) =
        eLpNorm (∑ k ∈ F, fun ω => ξ k ω ^ 2) (ENNReal.ofReal (s / 2)) μ ^ (s / 2) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0) ENNReal.ofReal_ne_top
        (by
          refine Finset.aestronglyMeasurable_sum F fun k _ => ?_
          exact (hmeasξ k).pow_const 2 |>.aestronglyMeasurable),
        ENNReal.toReal_ofReal hq0.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne',
        ENNReal.rpow_one]
      simp only [Finset.sum_apply]
    calc ∫⁻ ω, (∑ k ∈ F, ENNReal.ofReal (ξ k ω ^ 2)) ^ (s / 2) ∂μ
        = ∫⁻ ω, ‖∑ k ∈ F, ξ k ω ^ 2‖ₑ ^ (s / 2) ∂μ := by simp_rw [hnorm]
      _ = _ := h2
      _ ≤ (ENNReal.ofReal (cs ^ (2 / s) * S)) ^ (s / 2) := ENNReal.rpow_le_rpow h1 hq0.le
      _ = ENNReal.ofReal ((cs ^ (2 / s) * S) ^ (s / 2)) :=
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le
      _ = _ := by
          congr 1
          rw [Real.mul_rpow (by positivity) hS0, ← Real.rpow_mul hcs,
            show 2 / s * (s / 2) = 1 by field_simp, Real.rpow_one]
  -- limit over finite sets
  have hlim : ∀ ω, ‖Z ω‖ₑ ^ s = ⨆ F : Finset (NonzeroLattice d),
      (∑ k ∈ F, ENNReal.ofReal (ξ k ω ^ 2)) ^ (s / 2) := by
    intro ω
    rw [enorm_rpow_eq_tsum (Z ω) (by linarith), ENNReal.tsum_eq_iSup_sum]
    exact Monotone.map_iSup_of_continuousAt (f := fun x : ℝ≥0∞ => x ^ (s / 2))
      (ENNReal.continuous_rpow_const.continuousAt) (ENNReal.monotone_rpow_of_nonneg hq0.le)
      (by simp [ENNReal.zero_rpow_of_pos hq0])
  simp_rw [hlim]
  rw [lintegral_iSup_directed]
  · exact iSup_le hfin
  · intro F
    have : AEMeasurable (fun ω => ∑ k ∈ F, ENNReal.ofReal (ξ k ω ^ 2)) μ :=
      Finset.aemeasurable_fun_sum F fun k _ => ((hmeasξ k).pow_const 2).ennreal_ofReal
    exact this.pow_const _
  · intro F F'
    refine ⟨F ∪ F', fun ω => ?_, fun ω => ?_⟩ <;>
    · exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (by simp)) hq0.le

end Hilbert

end HRS.MC.E214F

end
