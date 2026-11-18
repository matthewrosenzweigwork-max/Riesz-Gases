import HRS.Commutator.Whole.PRODAux6
import HRS.PDE.ToolboxRd.Fourier

/-!
# CMX-PROD helper file 7: Plancherel and Fatou for the Sobolev seminorm of an `L²` limit
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.PROD

open HRS HRS.Whole HRS.Commutator.Whole
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- Plancherel for the difference of a Schwartz function and a real `L²` function. -/
lemma prod_plancherel_diff (u : SchwartzMap (Euc d) ℂ) {g : Euc d → ℝ} (hg : MemLp g 2 volume) :
    eLpNorm (fun ξ => 𝓕 (⇑u) ξ - fourierL2 g ξ) 2 volume =
      eLpNorm (fun x => u x - ((g x : ℝ) : ℂ)) 2 volume := by
  set U : Lp (α := Euc d) ℂ 2 := u.toLp 2 volume with hU
  set V : Lp (α := Euc d) ℂ 2 := ofRealLp hg with hV
  have h1 : eLpNorm (fun x => u x - ((g x : ℝ) : ℂ)) 2 volume = ‖U - V‖ₑ := by
    rw [Lp.enorm_def]
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub U V, SchwartzMap.coeFn_toLp u 2 (volume : Measure (Euc d)),
      ofRealLp_coe hg] with x h2 h3 h4
    rw [h2]
    simp only [Pi.sub_apply]
    rw [hU, hV, h3, h4]
  have h2 : eLpNorm (fun ξ => 𝓕 (⇑u) ξ - fourierL2 g ξ) 2 volume = ‖FT d U - FT d V‖ₑ := by
    rw [Lp.enorm_def]
    refine eLpNorm_congr_ae ?_
    have e : FT d U = ((𝓕 u : SchwartzMap (Euc d) ℂ)).toLp 2 := SchwartzMap.toLp_fourier_eq _
    filter_upwards [Lp.coeFn_sub (FT d U) (FT d V),
      SchwartzMap.coeFn_toLp (𝓕 u : SchwartzMap (Euc d) ℂ) 2 (volume : Measure (Euc d))] with ξ h2 h3
    rw [h2]
    simp only [Pi.sub_apply]
    rw [e, h3, fourierL2_eq hg, SchwartzMap.fourier_coe]
  rw [h1, h2, ← map_sub, ← ofReal_norm, ← ofReal_norm, LinearIsometryEquiv.norm_map]

lemma prod_rpow_sq {x : ℝ} (hx : 0 ≤ x) (α : ℝ) : (x ^ (α / 2)) ^ 2 = x ^ α := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- The `L²`-Fourier weight identity for Schwartz functions. -/
lemma prod_weighted_fourier (α : ℝ) (u : SchwartzMap (Euc d) ℂ) :
    ∫⁻ ξ, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ α) * ‖𝓕 (⇑u) ξ‖ₑ ^ 2 =
      eLpNorm (besselS α u) 2 volume ^ 2 := by
  have h1 : ∀ ξ : Euc d, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ α) * ‖𝓕 (⇑u) ξ‖ₑ ^ 2 =
      ‖𝓕 (⇑(prod_J α u)) ξ‖ₑ ^ (2 : ℝ) := by
    intro ξ
    rw [prod_fourier_J, enorm_mul, ENNReal.rpow_two, mul_pow]
    congr 1
    have hnn : 0 ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) := by positivity
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hnn, ← ENNReal.ofReal_pow hnn,
      prod_rpow_sq (by positivity)]
  simp_rw [h1]
  rw [SAMP2.lintegral_sq_fourier, prod_besselS_eq, SAMP2.eLpNorm_two_eq, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

/-- Fatou: an `L²` limit of Schwartz functions with `⟨∇⟩^α`-norms bounded by a convergent sequence
has `‖⟨∇⟩^α g‖_{L²} ≤ lim`. -/
theorem prod_fatou_sobolev (α : ℝ) (u : ℕ → SchwartzMap (Euc d) ℂ) {g : Euc d → ℝ}
    (hg : MemLp g 2 volume)
    (hconv : Tendsto (fun n => eLpNorm (fun x => u n x - ((g x : ℝ) : ℂ)) 2 volume) atTop (𝓝 0))
    {U : ℕ → ℝ≥0∞} {T : ℝ≥0∞} (hU : Tendsto U atTop (𝓝 T))
    (hle : ∀ n, eLpNorm (besselS α (u n)) 2 volume ≤ U n) :
    sobSqE α (fourierL2 g) ^ ((1 : ℝ) / 2) ≤ T := by
  have hG : Tendsto (fun n => eLpNorm (fun ξ => 𝓕 (⇑(u n)) ξ - fourierL2 g ξ) 2 volume) atTop
      (𝓝 0) := by
    refine hconv.congr (fun n => ?_)
    rw [prod_plancherel_diff (u n) hg]
  have hmeas : TendstoInMeasure volume (fun n ξ => 𝓕 (⇑(u n)) ξ) atTop (fourierL2 g) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hG
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  set w : Euc d → ℝ≥0∞ := fun ξ => ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ α) with hw
  have hwm : Measurable w := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.pow_const ?_ α
    fun_prop
  have hFm : ∀ k, Measurable (fun ξ => w ξ * ‖𝓕 (⇑(u (ns k))) ξ‖ₑ ^ 2) := by
    intro k
    have hc : Continuous (𝓕 (⇑(u (ns k)))) := by
      rw [← SchwartzMap.fourier_coe]; exact (𝓕 (u (ns k))).continuous
    exact hwm.mul (hc.measurable.enorm.pow_const 2)
  have hfat := lintegral_liminf_le (μ := volume) (u := atTop) hFm
  have hpt : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      Tendsto (fun k => w ξ * ‖𝓕 (⇑(u (ns k))) ξ‖ₑ ^ 2) atTop (𝓝 (w ξ * ‖fourierL2 g ξ‖ₑ ^ 2)) := by
    filter_upwards [hae] with ξ hξ
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
    exact ((ENNReal.continuous_pow 2).tendsto _).comp hξ.enorm
  have hlim : ∫⁻ ξ, w ξ * ‖fourierL2 g ξ‖ₑ ^ 2 ≤
      ∫⁻ ξ, liminf (fun k => w ξ * ‖𝓕 (⇑(u (ns k))) ξ‖ₑ ^ 2) atTop := by
    refine lintegral_mono_ae ?_
    filter_upwards [hpt] with ξ hξ
    rw [hξ.liminf_eq]
  have hsq : Tendsto (fun k => U (ns k) ^ 2) atTop (𝓝 (T ^ 2)) :=
    ((ENNReal.continuous_pow 2).tendsto T).comp (hU.comp hns.tendsto_atTop)
  have hX : sobSqE α (fourierL2 g) ≤ T ^ 2 := by
    calc sobSqE α (fourierL2 g) = ∫⁻ ξ, w ξ * ‖fourierL2 g ξ‖ₑ ^ 2 := rfl
      _ ≤ ∫⁻ ξ, liminf (fun k => w ξ * ‖𝓕 (⇑(u (ns k))) ξ‖ₑ ^ 2) atTop := hlim
      _ ≤ liminf (fun k => ∫⁻ ξ, w ξ * ‖𝓕 (⇑(u (ns k))) ξ‖ₑ ^ 2) atTop := hfat
      _ ≤ liminf (fun k => U (ns k) ^ 2) atTop := by
          refine liminf_le_liminf (Filter.Eventually.of_forall fun k => ?_)
          rw [hw]
          simp only
          rw [prod_weighted_fourier]
          gcongr
          exact hle _
      _ = T ^ 2 := hsq.liminf_eq
  calc sobSqE α (fourierL2 g) ^ ((1 : ℝ) / 2) ≤ (T ^ 2) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hX (by norm_num)
    _ = T := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

end HRS.Commutator.Whole.PROD
