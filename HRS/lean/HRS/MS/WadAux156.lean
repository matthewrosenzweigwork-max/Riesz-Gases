import HRS.MS.WadAux155

/-!
# S8.3, packet S8G-7: the one-body operator `f ↦ U_t(P_μ f)` satisfies the abstract hypotheses, mean functional

`s8g_meanF`: `q ↦ ∫ ⟨·⟩^M q dμ` is a bounded functional on `C_0`.  `s8g_op_of_2b`: from clause (2b) at order `J` (`s8f_clause2b`) the
operator `T f = U_t (P_μ f)` (`t ≥ 1`) satisfies `S8gOp M T J A` with `A = max C_J 0 * e^{-ct}`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8g_ι_integrable {M : ℝ} {μ : Measure (Euc d)} (hint : Integrable (fun y : Euc d => jbracket y ^ M) μ)
    (q : S8gV d) : Integrable (s8g_ι M q) μ :=
  ((hint.const_mul ‖q‖).mono' ((s85_jb_rpow_continuous M).mul (s8g_cont q)).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      have := s8g_ι_wt M q x
      simpa using this))

/-- The mean functional `q ↦ ∫ ⟨·⟩^M q dμ`. -/
def s8g_meanF {M : ℝ} {μ : Measure (Euc d)} (hint : Integrable (fun y : Euc d => jbracket y ^ M) μ) :
    S8gV d →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun q => ∫ x, s8g_ι M q x ∂μ
      map_add' := fun q1 q2 => by
        simp only [s8g_ι_add, Pi.add_apply]
        exact integral_add (s8g_ι_integrable hint q1) (s8g_ι_integrable hint q2)
      map_smul' := fun c q => by
        simp only [s8g_ι_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
    (∫ x, jbracket x ^ M ∂μ) (fun q => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs]
      have h1 : |∫ x, s8g_ι M q x ∂μ| ≤ ∫ x, ‖q‖ * jbracket x ^ M ∂μ := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le ((hint.const_mul ‖q‖)) (Eventually.of_forall fun x => ?_)
        have := s8g_ι_wt M q x
        simpa [mul_comm] using this
      rw [integral_const_mul] at h1
      linarith [mul_comm ‖q‖ (∫ x, jbracket x ^ M ∂μ)])

theorem s8g_meanF_apply {M : ℝ} {μ : Measure (Euc d)} (hint : Integrable (fun y : Euc d => jbracket y ^ M) μ)
    (q : S8gV d) : s8g_meanF hint q = ∫ x, s8g_ι M q x ∂μ := rfl

theorem s8g_meanF_norm {M : ℝ} {μ : Measure (Euc d)} (hint : Integrable (fun y : Euc d => jbracket y ^ M) μ) :
    ‖s8g_meanF hint‖ ≤ ∫ x, jbracket x ^ M ∂μ :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun x => Real.rpow_nonneg (s83_jb_pos x).le _) _

theorem s8g_projMean_add {ρ : Euc d → ℝ} (hP : HRS.Whole.IsProbDensity ρ) (hg : s84_GaussReg ρ) {M : ℝ}
    (hM : 0 ≤ M) {f g : Euc d → ℝ} (hf : MemCM M f) (hg' : MemCM M g) :
    HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) (f + g) =
      HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) f + HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) g := by
  funext x
  simp only [HRS.Whole.projMean, HRS.Whole.pair, Pi.add_apply]
  rw [integral_add (s8d_integrable_of_memCM hP hg hM hf) (s8d_integrable_of_memCM hP hg hM hg')]
  ring

theorem s8g_projMean_smul {μ : Measure (Euc d)} (c : ℝ) (f : Euc d → ℝ) :
    HRS.Whole.projMean μ (c • f) = c • HRS.Whole.projMean μ f := by
  funext x
  simp only [HRS.Whole.projMean, HRS.Whole.pair, Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul]
  ring

theorem s8g_op_of_2b (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U) {J : ℕ} {Cj c : ℝ}
    (h : ∀ t : ℝ, 1 ≤ t → ∀ f : Euc d → ℝ, MemCM M f →
      MemCMj M J (U t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) ∧
      weightedSupE J (-M) (U t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) ≤
        ENNReal.ofReal (Cj * Real.exp (-c * t)) * weightedSupE 0 (-M) f) {t : ℝ} (ht : 1 ≤ t) :
    S8gOp M (fun f => U t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) J (max Cj 0 * Real.exp (-c * t)) := by
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  have ht0 : 0 ≤ t := by linarith
  refine ⟨mul_nonneg (le_max_right _ _) (Real.exp_pos _).le, ?_, ?_, fun f hf => (h t ht f hf).1, ?_⟩
  · intro f g hf hg'
    rw [s8g_projMean_add hP hg hMpos.le hf hg']
    exact hU.add t ht0 _ _ (s8d_memCM_projMean hMpos hf) (s8d_memCM_projMean hMpos hg')
  · intro c' f hf
    rw [s8g_projMean_smul]
    exact hU.smul t ht0 c' _ (s8d_memCM_projMean hMpos hf)
  · intro f C hf hw i hi idx x
    have hC := hw.nonneg
    have h1 := (h t ht f hf).2
    have h2 : weightedSupE 0 (-M) f ≤ ENNReal.ofReal C := (s83_wsup0_le_iff hC f).2 hw
    have hA0 : 0 ≤ max Cj 0 * Real.exp (-c * t) := mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
    have h3 : weightedSupE J (-M) (U t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) ≤
        ENNReal.ofReal (max Cj 0 * Real.exp (-c * t) * C) := by
      refine h1.trans ?_
      rw [ENNReal.ofReal_mul hA0]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.exp_pos _).le)) h2
    have := (s83_wsup_le_iff (mul_nonneg hA0 hC) J _).1 h3 i hi idx x
    exact this

end HRS.MS.Wad
