import HRS.MS.QMulAux7

/-!
# MS-QMUL, part 8: density of Schwartz functions in the weighted Fourier space
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.QMul
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem qm_l2_dist {f g : Euc d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ∫⁻ x, ‖f x - g x‖ₑ ^ 2 = ENNReal.ofReal (dist (hf.toLp f) (hg.toLp g)) ^ 2 := by
  have h := qm_lint_sq_eq (hf.sub hg)
  simp only [Pi.sub_apply] at h
  rw [h, dist_eq_norm, ← MemLp.toLp_sub hf hg, Lp.norm_toLp, ENNReal.ofReal_toReal (hf.sub hg).eLpNorm_ne_top]

theorem qm_weights (m : ℕ) (ξ : Euc d) :
    0 < 1 + ‖ξ‖ ^ 2 ∧
    (1 + ‖ξ‖ ^ 2) ^ ((m : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ (-((m : ℝ) / 2)) = 1 ∧
    ((1 + ‖ξ‖ ^ 2) ^ ((m : ℝ) / 2)) ^ 2 ≤ wt ξ ^ m ∧
    wt ξ ^ m * ((1 + ‖ξ‖ ^ 2) ^ (-((m : ℝ) / 2))) ^ 2 ≤ (1 + 4 * Real.pi ^ 2) ^ m := by
  have hr : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hπ : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hgm : ((1 + ‖ξ‖ ^ 2) ^ ((m : ℝ) / 2)) ^ 2 = (1 + ‖ξ‖ ^ 2) ^ m := by
    rw [← Real.rpow_mul_natCast hr.le]
    have : (m : ℝ) / 2 * ((2 : ℕ) : ℝ) = (m : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
  have hhm : ((1 + ‖ξ‖ ^ 2) ^ (-((m : ℝ) / 2))) ^ 2 = ((1 + ‖ξ‖ ^ 2) ^ m)⁻¹ := by
    rw [← Real.rpow_mul_natCast hr.le]
    have : -((m : ℝ) / 2) * ((2 : ℕ) : ℝ) = -(m : ℝ) := by push_cast; ring
    rw [this, Real.rpow_neg hr.le, Real.rpow_natCast]
  refine ⟨hr, ?_, ?_, ?_⟩
  · rw [← Real.rpow_add hr]; simp
  · rw [hgm]
    exact pow_le_pow_left₀ hr.le (by unfold wt; nlinarith [sq_nonneg ‖ξ‖, mul_nonneg (sq_nonneg ‖ξ‖) (sub_nonneg.2 hπ)]) m
  · rw [hhm]
    have h1 : wt ξ ≤ (1 + 4 * Real.pi ^ 2) * (1 + ‖ξ‖ ^ 2) := by
      unfold wt; nlinarith [sq_nonneg ‖ξ‖, sq_nonneg Real.pi, mul_nonneg (sq_nonneg ‖ξ‖) (sq_nonneg Real.pi)]
    have h2 : wt ξ ^ m ≤ (1 + 4 * Real.pi ^ 2) ^ m * (1 + ‖ξ‖ ^ 2) ^ m := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (wt_pos ξ).le h1 m
    have hp : 0 < (1 + ‖ξ‖ ^ 2) ^ m := pow_pos hr m
    calc wt ξ ^ m * ((1 + ‖ξ‖ ^ 2) ^ m)⁻¹ ≤ (1 + 4 * Real.pi ^ 2) ^ m * (1 + ‖ξ‖ ^ 2) ^ m *
          ((1 + ‖ξ‖ ^ 2) ^ m)⁻¹ := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := by field_simp

theorem qm_density (m : ℕ) {v : Euc d → ℂ} (hv : MemLp v 2 volume)
    (hw : ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖v ξ‖ ^ 2) < ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : SchwartzMap (Euc d) ℂ,
      ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖𝓕 (⇑f) ξ - v ξ‖ ^ 2) ≤ ENNReal.ofReal δ := by
  set g : Euc d → ℝ := fun ξ => (1 + ‖ξ‖ ^ 2) ^ ((m : ℝ) / 2) with hgdef
  set h : Euc d → ℝ := fun ξ => (1 + ‖ξ‖ ^ 2) ^ (-((m : ℝ) / 2)) with hhdef
  have hgc : Continuous g := by
    refine Continuous.rpow_const (by fun_prop) fun ξ => Or.inl (qm_weights m ξ).1.ne'
  set u0 : Euc d → ℂ := fun ξ => (g ξ : ℂ) * v ξ with hu0def
  have hu0m : AEStronglyMeasurable u0 volume :=
    (Complex.continuous_ofReal.comp hgc).aestronglyMeasurable.mul hv.aestronglyMeasurable
  have hI : Integrable (fun ξ : Euc d => wt ξ ^ m * ‖v ξ‖ ^ 2) volume := by
    refine ⟨(continuous_wt.pow m).aestronglyMeasurable.mul
      (hv.aestronglyMeasurable.norm.pow 2), ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun ξ => ?_)) hw
    rw [Real.enorm_eq_ofReal (by have := wt_pos (d := d) ξ; positivity)]
  have hu0 : MemLp u0 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm hu0m]
    refine hI.mono' (hu0m.norm.pow 2) (Filter.Eventually.of_forall fun ξ => ?_)
    have h3 := (qm_weights m ξ).2.2.1
    have hg0 : 0 ≤ g ξ := Real.rpow_nonneg (qm_weights m ξ).1.le _
    rw [Real.norm_of_nonneg (by positivity), hu0def]
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hg0]
    calc (g ξ * ‖v ξ‖) ^ 2 = (g ξ) ^ 2 * ‖v ξ‖ ^ 2 := by ring
      _ ≤ wt ξ ^ m * ‖v ξ‖ ^ 2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
  have hK : 0 < (1 + 4 * Real.pi ^ 2) ^ m := by positivity
  have hε1 : 0 < Real.sqrt (δ / (1 + 4 * Real.pi ^ 2) ^ m) := Real.sqrt_pos.2 (div_pos hδ hK)
  obtain ⟨φ, hφ⟩ := (SchwartzMap.denseRange_toLpCLM (E := Euc d) (F := ℂ) (p := 2)
    (μ := volume) ENNReal.ofNat_ne_top).exists_dist_lt (hu0.toLp u0) hε1
  have hφ2 : ∫⁻ ξ, ‖φ ξ - u0 ξ‖ₑ ^ 2 ≤ ENNReal.ofReal (δ / (1 + 4 * Real.pi ^ 2) ^ m) := by
    rw [qm_l2_dist (φ.memLp 2 volume) hu0]
    have hd : dist ((φ.memLp 2 volume).toLp φ) (hu0.toLp u0) ≤ Real.sqrt (δ / (1 + 4 * Real.pi ^ 2) ^ m) := by
      rw [dist_comm]
      exact hφ.le
    calc ENNReal.ofReal (dist ((φ.memLp 2 volume).toLp φ) (hu0.toLp u0)) ^ 2
        ≤ ENNReal.ofReal (Real.sqrt (δ / (1 + 4 * Real.pi ^ 2) ^ m)) ^ 2 := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_pow hε1.le, Real.sq_sqrt (div_pos hδ hK).le]
  have hhg : Function.HasTemperateGrowth h :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow (Euc d) (-((m : ℝ) / 2))
  set ψ : SchwartzMap (Euc d) ℂ := SchwartzMap.smulLeftCLM (𝕜 := ℝ) ℂ h φ with hψ
  refine ⟨(𝓕⁻ ψ : SchwartzMap (Euc d) ℂ), ?_⟩
  have e : 𝓕 (⇑(𝓕⁻ ψ : SchwartzMap (Euc d) ℂ)) = ⇑ψ := by
    rw [← SchwartzMap.fourier_coe, FourierInvPair.fourier_fourierInv_eq]
  rw [e]
  have hpt : ∀ ξ : Euc d, ENNReal.ofReal (wt ξ ^ m * ‖ψ ξ - v ξ‖ ^ 2) ≤
      ENNReal.ofReal ((1 + 4 * Real.pi ^ 2) ^ m) * ‖φ ξ - u0 ξ‖ₑ ^ 2 := by
    intro ξ
    obtain ⟨hr, hgh, _, h4⟩ := qm_weights m ξ
    have hh0 : 0 < h ξ := Real.rpow_pos_of_pos hr _
    have e1 : ψ ξ - v ξ = (h ξ : ℂ) * (φ ξ - u0 ξ) := by
      rw [hψ, SchwartzMap.smulLeftCLM_apply_apply hhg, Complex.real_smul, hu0def]
      have : (h ξ : ℂ) * ((g ξ : ℂ) * v ξ) = v ξ := by
        rw [← mul_assoc, ← Complex.ofReal_mul]
        have : h ξ * g ξ = 1 := by rw [mul_comm]; exact hgh
        rw [this]; simp
      rw [mul_sub, this]
    rw [e1, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh0.le, ← ofReal_norm,
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc wt ξ ^ m * (h ξ * ‖φ ξ - u0 ξ‖) ^ 2 = (wt ξ ^ m * (h ξ) ^ 2) * ‖φ ξ - u0 ξ‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
  calc ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖ψ ξ - v ξ‖ ^ 2)
      ≤ ∫⁻ ξ, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2) ^ m) * ‖φ ξ - u0 ξ‖ₑ ^ 2 := lintegral_mono hpt
    _ = ENNReal.ofReal ((1 + 4 * Real.pi ^ 2) ^ m) * ∫⁻ ξ, ‖φ ξ - u0 ξ‖ₑ ^ 2 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((1 + 4 * Real.pi ^ 2) ^ m) *
          ENNReal.ofReal (δ / (1 + 4 * Real.pi ^ 2) ^ m) := by gcongr
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_mul hK.le]
        congr 1; field_simp

end HRS.MS.QMul
