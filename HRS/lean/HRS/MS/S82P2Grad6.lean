import HRS.MS.S82P2Grad5

/-!
# S8.2 (S82P2): per-site second moment of the gradient model (UNCOMPILED DRAFT)
Conditional on the centering of `∇_x Q` (hypothesis `hcenter`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

theorem s82p2_gradModel_bound {d : ℕ} (hd : 2 ≤ d) {a beta C0 C1 M : ℝ} (hM : 0 ≤ M)
    (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (G c : ℝ) (hG : 0 < G) (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ CG : ℝ, 0 ≤ CG ∧ ∀ (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ),
      WeakReferenceSetup d a beta rho q h C0 → PinComparison beta rho q h C1 →
      ∀ (A : ℝ), 0 ≤ A → ∀ (f : Euc d → ℝ) (Q : Euc d → Euc d → ℝ),
      PairCorrector a beta rho M A f Q →
      (∀ᵐ x ∂HRS.Whole.withDensityReal rho,
        ∫ z, s82p2_gt Q x z ∂HRS.Whole.withDensityReal rho = 0) →
      ∀ m : ℕ, 1 ≤ m → ∀ i : Fin (m + 1),
      ∫⁻ X, ENNReal.ofReal (‖s82p2_gradModel Q i X‖ ^ 2)
          ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta (m + 1) (m + 1)
            (fun i : Fin 0 => i.elim0) ≤
        ENNReal.ofReal (CG * A ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2) := by
  haveI hmu : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hρ
  obtain ⟨K0, hK00, hrow⟩ := s82p2_gt_row hd M hM G c hG hc rho hρ hρG
  have hMom0 : 0 ≤ HRS.MS.S82N.s82n_Mom d (4 * M) G c :=
    HRS.MS.S82N.s82n_Mom_nonneg (by omega) _ G c (by linarith) hG.le hc
  set Mom := HRS.MS.S82N.s82n_Mom d (4 * M) G c with hMomdef
  refine ⟨(1 + 2 * |C1|) * (4 * (|C0| ^ 2 * (2 + 2 * (1 + 2 * |C1|)) + (8 * |C1| ^ 2 +
    2 * |C1| ^ 2 * (1 + 2 * (1 / (1000 * beta))))) * K0 * Mom), by positivity, ?_⟩
  intro q h hW hP A hA f Q hQ hcenter m hm i
  have hC0 := hW.positive
  have hC1 := s82p2_pinCmp_nonneg hP
  rw [abs_of_pos hC0, abs_of_nonneg hC1]
  set Cs : ℝ := C0 ^ 2 * (2 + 2 * (1 + 2 * C1)) + (8 * C1 ^ 2 +
    2 * C1 ^ 2 * (1 + 2 * (1 / (1000 * beta)))) with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  have hK1 : 0 ≤ 1 + 2 * C1 := by linarith
  set mu := HRS.Whole.withDensityReal rho with hmudef
  have hN : 2 ≤ m + 1 := by omega
  have hNr : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  let pins0 : Fin 0 → Euc d := fun i => i.elim0
  have hprob0 : IsProbabilityMeasure (referenceLaw q h mu beta (m + 1) (m + 1) pins0) :=
    hW.probability (m + 1) hN 0 (m + 1) (by omega) (by omega) pins0
  have hprob1 : ∀ z : Euc d, IsProbabilityMeasure (referenceLaw q h mu beta (m + 1) m
      (Fin.cons z pins0 : Fin (0 + 1) → Euc d)) := fun z =>
    hW.probability (m + 1) hN (0 + 1) m (by omega) (by omega) _
  set Θ : EucConfig d (m + 1) → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (‖s82p2_gradModel Q i X‖ ^ 2) with hΘ
  have hΘm : Measurable Θ :=
    ENNReal.measurable_ofReal.comp ((s82p2_gradModel_measurable Q i).norm.pow_const 2)
  have hB := s82p2_disintegration (mu := mu) hW.short.measurable hW.short.even beta (m + 1)
    (hW.hmeas (m + 1)) pins0 i hprob0 hprob1 Θ hΘm
  set κ : ℝ := 4 * Cs * K0 * A ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hjb : Measurable (fun z : Euc d => jbracket z ^ (4 * M)) := by
    have : Measurable (fun x : Euc d => jbracket x) := by unfold jbracket; fun_prop
    exact this.pow_const _
  -- the inner bound, for mu-a.e. x
  have hinner : ∀ x : Euc d, ∫ z, s82p2_gt Q x z ∂mu = 0 →
      ∫⁻ X', Θ (i.insertNth x X') ∂referenceLaw q h mu beta (m + 1) m
        (Fin.cons x pins0 : Fin (0 + 1) → Euc d) ≤
        ENNReal.ofReal (κ * jbracket x ^ (4 * M)) := by
    intro x hx0
    obtain ⟨hgi, hgb⟩ := hrow a beta A hA f Q hQ x
    have hgm : Measurable (s82p2_gt Q x) :=
      (s82p2_gt_measurable Q).comp (measurable_prodMk_left (x := x))
    have hvec := s82p2_centered_vec_sum_sq (n := m) (p := 0 + 1) (N := m + 1) hd hW hbeta hP
      G c hG hc hρ hρG hN (by norm_num) (by omega) (by omega)
      (Fin.cons x pins0 : Fin (0 + 1) → Euc d) (s82p2_gt Q x) hgm hgi hx0
    have e : ∀ X' : Fin m → Euc d, Θ (i.insertNth x X') = ENNReal.ofReal (4 / ((m + 1 : ℕ) : ℝ) ^ 3) *
        ENNReal.ofReal (‖∑ k, s82p2_gt Q x (X' k)‖ ^ 2) := by
      intro X'
      simp only [hΘ, s82p2_gradModel, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show (2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = 4 / ((m + 1 : ℕ) : ℝ) ^ 3 from by
        have := s82p2_cN_sq (n := m + 1) (by omega) 1
        simpa using this]
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_of_nonneg_left hvec bot_le).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc 4 / ((m + 1 : ℕ) : ℝ) ^ 3 * (Cs * ((m + 1 : ℕ) : ℝ) * ∫ z, ‖s82p2_gt Q x z‖ ^ 2 ∂mu)
        ≤ 4 / ((m + 1 : ℕ) : ℝ) ^ 3 * (Cs * ((m + 1 : ℕ) : ℝ) *
            (A ^ 2 * K0 * jbracket x ^ (4 * M))) := by
          gcongr
      _ = κ * jbracket x ^ (4 * M) := by rw [hκ]; field_simp
  have hdom := s82p2_marg_le_smul hP hN (p := 0) (n := m + 1) (by omega) (by omega) (by omega)
    pins0 i hprob0
  have hac := s82p2_marg_ac q h mu beta (m + 1) pins0 i
  have hae := Filter.Eventually.filter_mono hac.ae_le hcenter
  rw [hB]
  calc ∫⁻ x, ∫⁻ X', Θ (i.insertNth x X')
        ∂referenceLaw q h mu beta (m + 1) m (Fin.cons x pins0 : Fin (0 + 1) → Euc d)
        ∂((referenceLaw q h mu beta (m + 1) (m + 1) pins0).map (fun X => X i))
      ≤ ∫⁻ x, ENNReal.ofReal (κ * jbracket x ^ (4 * M))
        ∂((referenceLaw q h mu beta (m + 1) (m + 1) pins0).map (fun X => X i)) := by
        refine lintegral_mono_ae (hae.mono fun x hx => ?_)
        exact hinner x hx
    _ ≤ ∫⁻ x, ENNReal.ofReal (κ * jbracket x ^ (4 * M)) ∂(ENNReal.ofReal (1 + 2 * C1) • mu) :=
        lintegral_mono' hdom le_rfl
    _ = ENNReal.ofReal (1 + 2 * C1) * ∫⁻ x, ENNReal.ofReal (κ * jbracket x ^ (4 * M)) ∂mu := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ENNReal.ofReal (1 + 2 * C1) * (ENNReal.ofReal κ * ENNReal.ofReal Mom) := by
        gcongr
        have : ∀ x : Euc d, ENNReal.ofReal (κ * jbracket x ^ (4 * M)) =
            ENNReal.ofReal κ * ENNReal.ofReal (jbracket x ^ (4 * M)) :=
          fun x => ENNReal.ofReal_mul hκ0
        simp_rw [this]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr
        exact s82p2_jb_moment hd (4 * M) (by linarith) G c hG hc rho hρ hρG
    _ = ENNReal.ofReal ((1 + 2 * C1) * (4 * Cs * K0 * Mom) * A ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_mul hκ0, ← ENNReal.ofReal_mul hK1]
        congr 1
        rw [hκ]
        ring

end HRS.MS.S82P2
