import HRS.MD.EQRemInt1

/-!
# EQ-REM (b), part 2: calculus of kernels with a singular envelope; linearity of the stationary remainder in `φ`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29 HRS.Quad HRS.External.HeatSplit

variable {d : ℕ} {s : ℝ}

/-! ### Gradient and pair kernel are linear -/

theorem eqrem_grad_add {f g : Torus d → ℝ} (hf : Torus.IsCk 1 f) (hg : Torus.IsCk 1 g) (x : Torus d) :
    Torus.grad (fun y => f y + g y) x = Torus.grad f x + Torus.grad g x := by
  have hf' : ContDiff ℝ 1 (Torus.lift f) := hf
  have hg' : ContDiff ℝ 1 (Torus.lift g) := hg
  unfold Torus.grad
  have : Torus.lift (fun y => f y + g y) = fun z => Torus.lift f z + Torus.lift g z := rfl
  rw [this]
  unfold gradient
  rw [fderiv_fun_add (hf'.differentiable one_ne_zero _) (hg'.differentiable one_ne_zero _), map_add]

theorem eqrem_grad_smul (c : ℝ) {f : Torus d → ℝ} (x : Torus d) :
    Torus.grad (fun y => c * f y) x = c • Torus.grad f x := by
  unfold Torus.grad
  have : Torus.lift (fun y => c * f y) = fun z => c * Torus.lift f z := rfl
  rw [this]
  unfold gradient
  by_cases hdf : DifferentiableAt ℝ (Torus.lift f) (Torus.rep x)
  · rw [fderiv_const_mul hdf, map_smul]
  · by_cases hc : c = 0
    · subst hc; simp
    · have : ¬ DifferentiableAt ℝ (fun z => c * Torus.lift f z) (Torus.rep x) := by
        intro h
        apply hdf
        have := h.const_mul c⁻¹
        simpa [← mul_assoc, inv_mul_cancel₀ hc] using this
      rw [fderiv_zero_of_not_differentiableAt hdf, fderiv_zero_of_not_differentiableAt this]
      simp

theorem eqrem_grad_const (c : ℝ) (x : Torus d) : Torus.grad (fun _ : Torus d => c) x = 0 := by
  unfold Torus.grad
  exact gradient_const _ _

theorem eqrem_pairKernel_add {φ ψ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) (hψ : Torus.IsCk 2 ψ) (x y : Torus d) :
    pairKernel d s (fun z => φ z + ψ z) x y = pairKernel d s φ x y + pairKernel d s ψ x y := by
  have h1 : ∀ {f : Torus d → ℝ}, Torus.IsCk 2 f → Torus.IsCk 1 f := fun {f} hf =>
    PDE.ClassicalAux.isCk_of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)) hf
  unfold pairKernel commKernel
  by_cases hxy : x = y
  · simp [hxy]
  · simp only [hxy, if_false]
    rw [eqrem_grad_add (h1 hφ) (h1 hψ), eqrem_grad_add (h1 hφ) (h1 hψ)]
    rw [← inner_add_left]
    congr 1
    abel

theorem eqrem_pairKernel_smul (c : ℝ) {φ : Torus d → ℝ} (x y : Torus d) :
    pairKernel d s (fun z => c * φ z) x y = c * pairKernel d s φ x y := by
  unfold pairKernel commKernel
  by_cases hxy : x = y
  · simp [hxy]
  · simp only [hxy, if_false]
    rw [eqrem_grad_smul, eqrem_grad_smul, ← smul_sub, inner_smul_left]
    simp

theorem eqrem_pairKernel_const (c : ℝ) (x y : Torus d) :
    pairKernel d s (fun _ : Torus d => c) x y = 0 := by
  unfold pairKernel commKernel
  by_cases hxy : x = y
  · simp [hxy]
  · simp [hxy, eqrem_grad_const]


/-! ### Kernels with a singular envelope -/

/-- A symmetric measurable kernel vanishing on the diagonal and bounded off the diagonal by `B` times the
singular envelope `singEnvelope s (|x-y|)`. -/
structure EnvGood (s B : ℝ) (h : Torus d → Torus d → ℝ) : Prop where
  hB : 0 ≤ B
  meas : Measurable (Function.uncurry h)
  symm : ∀ x y, h x y = h y x
  diag : ∀ x, h x x = 0
  env : ∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)

theorem eqrem_envT_integrable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (envT s : Torus d → ℝ) volume := by
  obtain ⟨c₃, -, hc⟩ := lintegral_envT_le (d := d) hd hs0 hsd
  refine ⟨measurable_envT.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ z : Torus d, ‖envT s z‖ₑ = ∫⁻ z : Torus d, ENNReal.ofReal (envT s z) :=
        lintegral_congr fun z => Real.enorm_of_nonneg (by linarith [one_le_envT (s := s) z])
    _ ≤ ENNReal.ofReal c₃ := hc
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem EnvGood.bound {B : ℝ} {h : Torus d → Torus d → ℝ} (hg : EnvGood s B h) (x y : Torus d) :
    |h x y| ≤ B * envT s (x - y) := by
  by_cases hxy : x = y
  · subst hxy
    rw [hg.diag, abs_zero]
    exact mul_nonneg hg.hB (by linarith [one_le_envT (s := s) (x - x)])
  · have := hg.env x y hxy
    unfold envT
    rw [← eucDist_sub]
    exact this

theorem EnvGood.add {B₁ B₂ : ℝ} {h₁ h₂ : Torus d → Torus d → ℝ} (g₁ : EnvGood s B₁ h₁) (g₂ : EnvGood s B₂ h₂) :
    EnvGood s (B₁ + B₂) (fun x y => h₁ x y + h₂ x y) where
  hB := add_nonneg g₁.hB g₂.hB
  meas := g₁.meas.add g₂.meas
  symm x y := by rw [g₁.symm, g₂.symm]
  diag x := by simp [g₁.diag, g₂.diag]
  env x y hxy := by
    calc |h₁ x y + h₂ x y| ≤ |h₁ x y| + |h₂ x y| := abs_add_le _ _
      _ ≤ B₁ * singEnvelope s (Torus.eucDist x y) + B₂ * singEnvelope s (Torus.eucDist x y) :=
          add_le_add (g₁.env x y hxy) (g₂.env x y hxy)
      _ = _ := by ring

theorem EnvGood.smul {B : ℝ} {h : Torus d → Torus d → ℝ} (g : EnvGood s B h) (c : ℝ) :
    EnvGood s (|c| * B) (fun x y => c * h x y) where
  hB := mul_nonneg (abs_nonneg _) g.hB
  meas := measurable_const.mul g.meas
  symm x y := by rw [g.symm]
  diag x := by simp [g.diag]
  env x y hxy := by
    rw [abs_mul]
    calc |c| * |h x y| ≤ |c| * (B * singEnvelope s (Torus.eucDist x y)) :=
          mul_le_mul_of_nonneg_left (g.env x y hxy) (abs_nonneg _)
      _ = _ := by ring

theorem EnvGood.zero : EnvGood s 0 (fun _ _ : Torus d => (0 : ℝ)) where
  hB := le_rfl
  meas := measurable_const
  symm _ _ := rfl
  diag _ := rfl
  env x y _ := by simp

theorem EnvGood.mono {B B' : ℝ} {h : Torus d → Torus d → ℝ} (g : EnvGood s B h) (hBB : B ≤ B') :
    EnvGood s B' h where
  hB := g.hB.trans hBB
  meas := g.meas
  symm := g.symm
  diag := g.diag
  env x y hxy := (g.env x y hxy).trans (mul_le_mul_of_nonneg_right hBB (by
    have : 1 ≤ singEnvelope s (Torus.eucDist x y) := one_le_singEnvelope' (Real.sqrt_nonneg _)
    linarith))

theorem eqrem_pairKernel_envGood (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ φ : Torus d → ℝ, Torus.IsCk 2 φ → EnvGood s (C₀ * Torus.cbNorm 2 φ) (pairKernel d s φ) := by
  obtain ⟨C₀, hC₀, hC⟩ := eqrem_pairKernel_env hd hs0 hsd
  refine ⟨C₀, hC₀, fun φ hφ => ?_⟩
  exact { hB := mul_nonneg hC₀ (eqrem_cbNorm_nonneg 2 φ)
          meas := eqrem_pairKernel_meas hsd hφ
          symm := eqrem_pairKernel_symm hsd φ
          diag := fun x => by unfold pairKernel commKernel; simp
          env := fun x y hxy => hC φ hφ x y hxy }

/-- `ν`-integrability of the fibres and the uniform bound of the kernel field. -/
theorem EnvGood.fibre (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {B : ℝ} {h : Torus d → Torus d → ℝ}
    (hg : EnvGood s B h) {ν : Measure (Torus d)} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hν : ν ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d))) (x : Torus d) :
    Integrable (fun y => h x y) ν ∧
      |∫ y, h x y ∂ν| ≤ Λ * (B * ∫ z : Torus d, envT s z) := by
  have hI0 := eqrem_envT_integrable (d := d) hd hs0 hsd
  have hgi : Integrable (fun y : Torus d => B * envT s (x - y)) volume :=
    (hI0.comp_sub_left x).const_mul _
  have hνfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    have h := Measure.le_iff'.1 hν Set.univ
    rw [Measure.smul_apply, smul_eq_mul] at h
    exact lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
  have hint : Integrable (fun y : Torus d => B * envT s (x - y)) ν :=
    (hgi.smul_measure ENNReal.ofReal_ne_top).mono_measure hν
  have hmeas : Measurable (fun y => h x y) := hg.meas.comp (measurable_const.prodMk measurable_id)
  have hI : Integrable (fun y => h x y) ν := by
    refine Integrable.mono' hint hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]; exact hg.bound x y
  refine ⟨hI, ?_⟩
  have h1 : ∫ y, |h x y| ∂ν ≤ ∫ y, B * envT s (x - y) ∂ν :=
    integral_mono hI.abs hint (hg.bound x)
  refine (abs_integral_le_integral_abs).trans (h1.trans ?_)
  have hnn : ∀ y : Torus d, 0 ≤ B * envT s (x - y) := fun y =>
    mul_nonneg hg.hB (by linarith [one_le_envT (s := s) (x - y)])
  have h2 := integral_mono_measure hν (Filter.Eventually.of_forall hnn) (hgi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure, ENNReal.toReal_ofReal hΛ, smul_eq_mul] at h2
  refine h2.trans ?_
  have h3 : ∫ y : Torus d, B * envT s (x - y) = B * ∫ z : Torus d, envT s z := by
    rw [integral_const_mul]
    congr 1
    exact integral_sub_left_eq_self (fun z : Torus d => envT s z) volume x
  rw [h3]

theorem EnvGood.kf_meas {B : ℝ} {h : Torus d → Torus d → ℝ} (hg : EnvGood s B h) {ν : Measure (Torus d)}
    [IsFiniteMeasure ν] : Measurable (kernelField h ν) :=
  hg.meas.stronglyMeasurable.integral_prod_right'.measurable


/-! ### Thermal data -/

/-- Probability Gibbs law, density bounds of `μ_β` and of the first marginal `m_N` w.r.t. Lebesgue measure. -/
theorem eqrem_meas_bounds (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ} (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    {N : ℕ} (hN : 2 ≤ N) :
    IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) ∧
    IsProbabilityMeasure (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) ∧
    ∃ Λ Λm : ℝ, 0 ≤ Λ ∧ 0 ≤ Λm ∧
      withDensityReal ρβ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) ∧
      firstMarginal (canonicalGibbs (periodicRiesz d s) V N β) ≤ ENNReal.ofReal Λm • (volume : Measure (Torus d)) := by
  obtain ⟨hρs, Λ, hΛ0, hΛ, hP⟩ := eqrem_setup hd hs0 hsd V hV hβ hρ
  obtain ⟨Mp, hMp0, hMp⟩ := eqrem_marginal_le hd hs0 hsd V hV hβ hρ
  have hN0 : 0 < N := by omega
  have hμ : withDensityReal ρβ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) := eqrem_mu_le_vol hΛ
  have hprob := eqrem_gibbs_prob hd hs0 hsd V hV hβ hρ hN0
  refine ⟨hprob, ?_, Λ, Mp * Λ, hΛ0, mul_nonneg hMp0 hΛ0, hμ, ?_⟩
  · unfold firstMarginal
    rw [dif_pos hN0]
    have := hprob
    infer_instance
  · refine (hMp N hN).trans ?_
    calc ENNReal.ofReal Mp • withDensityReal ρβ
        ≤ ENNReal.ofReal Mp • (ENNReal.ofReal Λ • (volume : Measure (Torus d))) := by
          refine Measure.le_iff'.2 fun A => ?_
          have := Measure.le_iff'.1 hμ A
          rw [Measure.smul_apply, smul_eq_mul] at this
          rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
          exact mul_le_mul' le_rfl this
      _ = ENNReal.ofReal (Mp * Λ) • (volume : Measure (Torus d)) := by
          rw [smul_smul, ENNReal.ofReal_mul hMp0]

/-- `D_N(h; m_N)` is integrable under the Gibbs law for an envelope-bounded kernel. -/
theorem eqrem_quad_integrable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ} (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    {N : ℕ} (hN : 2 ≤ N) {B : ℝ} {h : Torus d → Torus d → ℝ} (hg : EnvGood s B h) :
    Integrable (fun X : Config d N => quadStat h (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) X)
      (canonicalGibbs (periodicRiesz d s) V N β) := by
  obtain ⟨hprob, hmprob, Λ, Λm, hΛ, hΛm, hμ, hm⟩ := eqrem_meas_bounds hd hs0 hsd V hV hβ hρ hN
  obtain ⟨Cq, hCq0, hCq⟩ := EQStat.eq_static_quadratic_proof hd hs0 hsd V hV β β hβ le_rfl
  have hmeas := eqrem_quadStat_meas (N := N) hg.meas
    (hg.kf_meas (ν := firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)))
  have hvar := hCq β ⟨le_rfl, le_rfl⟩ ρβ hρ B h hg.meas hg.symm hg.env N hN _ (Or.inr rfl)
  have hlt : evariance (fun X : Config d N => quadStat h
      (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) X)
      (canonicalGibbs (periodicRiesz d s) V N β) < ⊤ := by
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hvar ENNReal.ofReal_lt_top)
    refine le_mul_of_one_le_left bot_le ?_
    exact_mod_cast (by omega : 1 ≤ N)
  exact ((evariance_lt_top_iff_memLp hmeas.aestronglyMeasurable).1 hlt).integrable one_le_two


/-! ### The remainder functional on kernels -/

/-- The stationary remainder as a functional of the pair kernel `h`. -/
def remA (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρβ : Torus d → ℝ) {N : ℕ}
    (h : Torus d → Torus d → ℝ) (X : Config d N) : ℝ :=
  Real.sqrt N *
      (∫ x, (kernelField h (withDensityReal ρβ) x -
          kernelField h (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) x) ∂(empirical X) -
        ∫ x, (kernelField h (withDensityReal ρβ) x -
          kernelField h (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) x)
          ∂(firstMarginal (canonicalGibbs (periodicRiesz d s) V N β))) -
    (Real.sqrt N / 2) *
      (quadStat h (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) X -
        ∫ Y, quadStat h (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) Y
          ∂(canonicalGibbs (periodicRiesz d s) V N β))

theorem statRemainder_eq_remA (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρβ : Torus d → ℝ) {N : ℕ}
    (φ : Torus d → ℝ) (X : Config d N) :
    statRemainder d s V β ρβ (N := N) φ X = remA d s V β ρβ (pairKernel d s φ) X := rfl

/-- Bounded measurable kernel fields are `m`-integrable. -/
theorem EnvGood.kf_integrable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {B : ℝ} {h : Torus d → Torus d → ℝ}
    (hg : EnvGood s B h) {ν m : Measure (Torus d)} [IsFiniteMeasure ν] [IsFiniteMeasure m] {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hν : ν ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d))) :
    Integrable (kernelField h ν) m :=
  Integrable.of_bound hg.kf_meas.aestronglyMeasurable (Λ * (B * ∫ z : Torus d, envT s z))
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact (hg.fibre hd hs0 hsd hΛ hν x).2)

theorem eqrem_remA_add (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ} (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    {N : ℕ} (hN : 2 ≤ N) {B₁ B₂ : ℝ} {h₁ h₂ : Torus d → Torus d → ℝ} (g₁ : EnvGood s B₁ h₁)
    (g₂ : EnvGood s B₂ h₂) (X : Config d N) :
    remA d s V β ρβ (fun x y => h₁ x y + h₂ x y) X = remA d s V β ρβ h₁ X + remA d s V β ρβ h₂ X := by
  obtain ⟨hprob, hmprob, Λ, Λm, hΛ, hΛm, hμ, hm⟩ := eqrem_meas_bounds hd hs0 hsd V hV hβ hρ hN
  have hN0 : 0 < N := by omega
  set G := canonicalGibbs (periodicRiesz d s) V N β with hG
  set m := firstMarginal G with hmdef
  set μ := withDensityReal ρβ with hμdef
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    have h := Measure.le_iff'.1 hμ Set.univ
    rw [Measure.smul_apply, smul_eq_mul] at h
    exact lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
  have kfμ : ∀ (x : Torus d), kernelField (fun x y => h₁ x y + h₂ x y) μ x =
      kernelField h₁ μ x + kernelField h₂ μ x := fun x =>
    integral_add (g₁.fibre hd hs0 hsd hΛ hμ x).1 (g₂.fibre hd hs0 hsd hΛ hμ x).1
  have kfm : ∀ (x : Torus d), kernelField (fun x y => h₁ x y + h₂ x y) m x =
      kernelField h₁ m x + kernelField h₂ m x := fun x =>
    integral_add (g₁.fibre hd hs0 hsd hΛm hm x).1 (g₂.fibre hd hs0 hsd hΛm hm x).1
  have iμ₁ := g₁.kf_integrable hd hs0 hsd (m := m) hΛ hμ
  have iμ₂ := g₂.kf_integrable hd hs0 hsd (m := m) hΛ hμ
  have im₁ := g₁.kf_integrable hd hs0 hsd (m := m) hΛm hm
  have im₂ := g₂.kf_integrable hd hs0 hsd (m := m) hΛm hm
  -- empirical integral
  have hemp : ∀ f : Torus d → ℝ, ∫ x, f x ∂(empirical X) = (1 / (N : ℝ)) * ∑ i, f (X i) := by
    intro f
    have := pair_empirical hN0 X f
    unfold pair at this
    rw [one_div]; exact this
  -- quadStat additivity
  have e2 : ∫ x, (∫ y, h₁ x y ∂m + ∫ y, h₂ x y ∂m) ∂m =
      (∫ x, ∫ y, h₁ x y ∂m ∂m) + ∫ x, ∫ y, h₂ x y ∂m ∂m := integral_add im₁ im₂
  have hqpt : ∀ Y : Config d N, quadStat (fun x y => h₁ x y + h₂ x y) m Y =
      quadStat h₁ m Y + quadStat h₂ m Y := by
    intro Y
    unfold quadStat
    have e1 : ∀ x : Torus d, ∫ y, (h₁ x y + h₂ x y) ∂m = ∫ y, h₁ x y ∂m + ∫ y, h₂ x y ∂m := kfm
    simp_rw [e1]
    rw [e2]
    simp only [Finset.sum_add_distrib, mul_add]
    ring
  have hq := hqpt X
  have hqG : ∫ Y, quadStat (fun x y => h₁ x y + h₂ x y) m Y ∂G =
      ∫ Y, quadStat h₁ m Y ∂G + ∫ Y, quadStat h₂ m Y ∂G := by
    have : (fun Y : Config d N => quadStat (fun x y => h₁ x y + h₂ x y) m Y) =
        fun Y => quadStat h₁ m Y + quadStat h₂ m Y := funext hqpt
    rw [this]
    exact integral_add (eqrem_quad_integrable hd hs0 hsd V hV hβ hρ hN g₁)
      (eqrem_quad_integrable hd hs0 hsd V hV hβ hρ hN g₂)
  unfold remA
  rw [hq, hqG]
  simp only [← hG, ← hmdef, ← hμdef]
  have hψ : ∀ x, kernelField (fun x y => h₁ x y + h₂ x y) μ x - kernelField (fun x y => h₁ x y + h₂ x y) m x =
      (kernelField h₁ μ x - kernelField h₁ m x) + (kernelField h₂ μ x - kernelField h₂ m x) := by
    intro x; rw [kfμ, kfm]; ring
  simp_rw [hψ]
  have e3 : ∫ x, ((kernelField h₁ μ x - kernelField h₁ m x) + (kernelField h₂ μ x - kernelField h₂ m x)) ∂m =
      ∫ x, (kernelField h₁ μ x - kernelField h₁ m x) ∂m + ∫ x, (kernelField h₂ μ x - kernelField h₂ m x) ∂m :=
    integral_add (iμ₁.sub im₁) (iμ₂.sub im₂)
  rw [e3, hemp, hemp, hemp]
  simp only [Finset.sum_add_distrib, mul_add]
  ring


theorem eqrem_remA_smul {N0 : ℕ} (hN : 0 < N0) (c : ℝ) (h : Torus d → Torus d → ℝ) (X : Config d N0) (V : Torus d → ℝ) (β : ℝ)
    (ρβ : Torus d → ℝ) :
    remA d s V β ρβ (fun x y => c * h x y) X = c * remA d s V β ρβ h X := by
  have kf : ∀ (ν : Measure (Torus d)) (x : Torus d), kernelField (fun x y => c * h x y) ν x = c * kernelField h ν x :=
    fun ν x => integral_const_mul _ _
  have hemp : ∀ f : Torus d → ℝ, ∫ x, f x ∂(empirical X) = (1 / (N0 : ℝ)) * ∑ i, f (X i) := by
    intro f
    have := pair_empirical hN X f
    unfold pair at this
    rw [one_div]; exact this
  have hqpt : ∀ (ν : Measure (Torus d)) (Y : Config d N0), quadStat (fun x y => c * h x y) ν Y = c * quadStat h ν Y := by
    intro ν Y
    unfold quadStat
    have e1 : ∀ x : Torus d, ∫ y, c * h x y ∂ν = c * ∫ y, h x y ∂ν := fun x => integral_const_mul _ _
    simp_rw [e1]
    rw [integral_const_mul]
    simp only [← Finset.mul_sum]
    ring
  unfold remA
  simp_rw [hqpt]
  have hψ : ∀ x, kernelField (fun x y => c * h x y) (withDensityReal ρβ) x -
      kernelField (fun x y => c * h x y) (firstMarginal (canonicalGibbs (periodicRiesz d s) V N0 β)) x =
      c * (kernelField h (withDensityReal ρβ) x -
        kernelField h (firstMarginal (canonicalGibbs (periodicRiesz d s) V N0 β)) x) := by
    intro x; rw [kf, kf]; ring
  simp_rw [hψ]
  rw [integral_const_mul, integral_const_mul, hemp, integral_const_mul]
  ring


/-! ### The pathwise bound -/

/-- The envelope kernel `e(x,y) = envT s (x - y)` off the diagonal. -/
def envK (s : ℝ) (x y : Torus d) : ℝ := if x = y then 0 else envT s (x - y)

theorem envK_good : EnvGood s 1 (envK s : Torus d → Torus d → ℝ) where
  hB := zero_le_one
  meas := by
    unfold envK Function.uncurry
    exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const
      (measurable_envT.comp (measurable_fst.sub measurable_snd))
  symm x y := by
    unfold envK
    by_cases hxy : x = y
    · simp [hxy]
    · have hyx : y ≠ x := fun h => hxy h.symm
      simp only [hxy, hyx, if_false]
      exact envT_sub_comm x y
  diag x := by simp [envK]
  env x y hxy := by
    unfold envK
    rw [if_neg hxy, abs_of_nonneg (by linarith [one_le_envT (s := s) (x - y)])]
    unfold envT
    rw [← eucDist_sub]
    simp

theorem EnvGood.le_envK {B : ℝ} {h : Torus d → Torus d → ℝ} (hg : EnvGood s B h) (x y : Torus d) :
    |h x y| ≤ B * envK s x y := by
  unfold envK
  by_cases hxy : x = y
  · simp [hxy, hg.diag]
  · rw [if_neg hxy]; exact hg.bound x y

/-- `N⁻² ∑_{i≠j} e(x_i,x_j)`. -/
def Qenv (s : ℝ) {N : ℕ} (X : Config d N) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, envK s (X i) (X j)

theorem Qenv_nonneg {N : ℕ} (X : Config d N) : 0 ≤ Qenv s X := by
  unfold Qenv
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
  unfold envK
  split_ifs
  · exact le_rfl
  · linarith [one_le_envT (s := s) (X i - X j)]

theorem eqrem_Qenv_integrable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ} (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    {N : ℕ} (hN : 2 ≤ N) :
    Integrable (fun X : Config d N => Qenv s X) (canonicalGibbs (periodicRiesz d s) V N β) := by
  obtain ⟨hprob, hmprob, Λ, Λm, hΛ, hΛm, hμ, hm⟩ := eqrem_meas_bounds hd hs0 hsd V hV hβ hρ hN
  set G := canonicalGibbs (periodicRiesz d s) V N β with hG
  set m := firstMarginal G with hmdef
  have hg : EnvGood s 1 (envK s : Torus d → Torus d → ℝ) := envK_good
  have h1 := eqrem_quad_integrable hd hs0 hsd V hV hβ hρ hN hg
  have hkm : Measurable (kernelField (envK s : Torus d → Torus d → ℝ) m) := hg.kf_meas
  have hkb : ∀ x, |kernelField (envK s : Torus d → Torus d → ℝ) m x| ≤ Λm * (1 * ∫ z : Torus d, envT s z) :=
    fun x => (hg.fibre hd hs0 hsd hΛm hm x).2
  have h2 := eqrem_avg_integrable (G := G) hkm hkb
  have h3 : Integrable (fun X : Config d N => quadStat (envK s : Torus d → Torus d → ℝ) m X +
      2 * ((1 / (N : ℝ)) * ∑ i, kernelField (envK s : Torus d → Torus d → ℝ) m (X i)) -
      ∫ x, ∫ y, envK s x y ∂m ∂m) G :=
    (h1.add (h2.const_mul 2)).sub (integrable_const _)
  refine h3.congr (ae_of_all _ fun X => ?_)
  show quadStat (envK s : Torus d → Torus d → ℝ) m X + 2 * ((1 / (N : ℝ)) * ∑ i, kernelField (envK s : Torus d → Torus d → ℝ) m (X i)) -
      ∫ x, ∫ y, envK s x y ∂m ∂m = Qenv s X
  unfold quadStat Qenv kernelField
  ring


theorem eqrem_remA_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ} (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    {N : ℕ} (hN : 2 ≤ N) :
    ∃ 𝔅 : Config d N → ℝ, (∀ X, 0 ≤ 𝔅 X) ∧ ∀ (B : ℝ) (h : Torus d → Torus d → ℝ), EnvGood s B h →
      ∀ X : Config d N, |remA d s V β ρβ h X| ≤ B * 𝔅 X := by
  obtain ⟨hprob, hmprob, Λ, Λm, hΛ, hΛm, hμ, hm⟩ := eqrem_meas_bounds hd hs0 hsd V hV hβ hρ hN
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hsq : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hN1 : (0 : ℝ) < 1 / N := one_div_pos.2 hNR
  have hN2 : (0 : ℝ) < 1 / (N : ℝ) ^ 2 := one_div_pos.2 (pow_pos hNR 2)
  set G := canonicalGibbs (periodicRiesz d s) V N β with hG
  set m := firstMarginal G with hmdef
  set μ := withDensityReal ρβ with hμdef
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    have h := Measure.le_iff'.1 hμ Set.univ
    rw [Measure.smul_apply, smul_eq_mul] at h
    exact lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
  set Ie : ℝ := ∫ z : Torus d, envT s z with hIe
  have hIe0 : 0 ≤ Ie := integral_nonneg fun z => show (0 : ℝ) ≤ envT s z by
    linarith [one_le_envT (s := s) z]
  set EQ : ℝ := ∫ Y, Qenv s Y ∂G with hEQ
  have hEQ0 : 0 ≤ EQ := integral_nonneg fun Y => Qenv_nonneg Y
  have hQi := eqrem_Qenv_integrable hd hs0 hsd V hV hβ hρ hN
  have hκ : 0 ≤ (Λ + Λm) * Ie := mul_nonneg (add_nonneg hΛ hΛm) hIe0
  have hc3 : 0 ≤ 3 * Λm * Ie := mul_nonneg (mul_nonneg (by norm_num) hΛm) hIe0
  refine ⟨fun X => Real.sqrt N * (2 * ((Λ + Λm) * Ie)) +
    (Real.sqrt N / 2) * ((Qenv s X + 3 * Λm * Ie) + (EQ + 3 * Λm * Ie)), fun X => ?_, ?_⟩
  · have := Qenv_nonneg (s := s) X
    exact add_nonneg (mul_nonneg hsq (mul_nonneg (by norm_num) hκ))
      (mul_nonneg (div_nonneg hsq (by norm_num)) (add_nonneg (add_nonneg this hc3) (add_nonneg hEQ0 hc3)))
  intro B h hg X
  have hB := hg.hB
  have hemp : ∀ f : Torus d → ℝ, ∫ x, f x ∂(empirical X) = (1 / (N : ℝ)) * ∑ i, f (X i) := by
    intro f
    have := pair_empirical hN0 X f
    unfold pair at this
    rw [one_div]; exact this
  have fμ : ∀ x, |∫ y, h x y ∂μ| ≤ Λ * (B * Ie) := fun x => (hg.fibre hd hs0 hsd hΛ hμ x).2
  have fm : ∀ x, |∫ y, h x y ∂m| ≤ Λm * (B * Ie) := fun x => (hg.fibre hd hs0 hsd hΛm hm x).2
  -- bound on ψ
  have hψ : ∀ x, |kernelField h μ x - kernelField h m x| ≤ B * ((Λ + Λm) * Ie) := by
    intro x
    refine (abs_sub _ _).trans ?_
    have := add_le_add (fμ x) (fm x)
    refine this.trans (le_of_eq ?_)
    ring
  have hκ0 : 0 ≤ B * ((Λ + Λm) * Ie) := mul_nonneg hB hκ
  have hA : |∫ x, (kernelField h μ x - kernelField h m x) ∂(empirical X)| ≤ B * ((Λ + Λm) * Ie) := by
    rw [hemp, abs_mul, abs_of_pos hN1]
    have h1 : |∑ i, (kernelField h μ (X i) - kernelField h m (X i))| ≤ N * (B * ((Λ + Λm) * Ie)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hψ (X i)).trans ?_
      simp
    calc 1 / (N : ℝ) * |∑ i, (kernelField h μ (X i) - kernelField h m (X i))|
        ≤ 1 / (N : ℝ) * (N * (B * ((Λ + Λm) * Ie))) := mul_le_mul_of_nonneg_left h1 hN1.le
      _ = _ := by field_simp
  have hBm : |∫ x, (kernelField h μ x - kernelField h m x) ∂m| ≤ B * ((Λ + Λm) * Ie) := by
    have := norm_integral_le_of_norm_le_const (μ := m) (f := fun x => kernelField h μ x - kernelField h m x)
      (C := B * ((Λ + Λm) * Ie)) (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hψ x)
    rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
    exact this
  -- bound on quadStat
  have hq : ∀ Y : Config d N, |quadStat h m Y| ≤ B * (Qenv s Y + 3 * Λm * Ie) := by
    intro Y
    unfold quadStat
    have t1 : |(1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)| ≤ B * Qenv s Y := by
      rw [abs_mul, abs_of_pos hN2]
      have h1 : |∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)| ≤
          B * ∑ i, ∑ j ∈ Finset.univ.erase i, envK s (Y i) (Y j) := by
        calc |∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)|
            ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, |h (Y i) (Y j)| := by
              refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
              exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, B * envK s (Y i) (Y j) :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hg.le_envK _ _
          _ = B * ∑ i, ∑ j ∈ Finset.univ.erase i, envK s (Y i) (Y j) := by
              simp only [← Finset.mul_sum]
      calc 1 / (N : ℝ) ^ 2 * |∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)|
          ≤ 1 / (N : ℝ) ^ 2 * (B * ∑ i, ∑ j ∈ Finset.univ.erase i, envK s (Y i) (Y j)) :=
            mul_le_mul_of_nonneg_left h1 hN2.le
        _ = B * Qenv s Y := by unfold Qenv; ring
    have t2 : |2 * ((1 / (N : ℝ)) * ∑ i, ∫ y, h (Y i) y ∂m)| ≤ 2 * (Λm * (B * Ie)) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul, abs_of_pos hN1]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have h1 : |∑ i, ∫ y, h (Y i) y ∂m| ≤ N * (Λm * (B * Ie)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => fm (Y i)).trans ?_
        simp
      calc 1 / (N : ℝ) * |∑ i, ∫ y, h (Y i) y ∂m| ≤ 1 / (N : ℝ) * (N * (Λm * (B * Ie))) :=
            mul_le_mul_of_nonneg_left h1 hN1.le
        _ = _ := by field_simp
    have t3 : |∫ x, ∫ y, h x y ∂m ∂m| ≤ Λm * (B * Ie) := by
      have := norm_integral_le_of_norm_le_const (μ := m) (f := fun x => ∫ y, h x y ∂m)
        (C := Λm * (B * Ie)) (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact fm x)
      rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
      exact this
    calc |(1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) -
          2 * ((1 / (N : ℝ)) * ∑ i, ∫ y, h (Y i) y ∂m) + ∫ x, ∫ y, h x y ∂m ∂m|
        ≤ |(1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) -
          2 * ((1 / (N : ℝ)) * ∑ i, ∫ y, h (Y i) y ∂m)| + |∫ x, ∫ y, h x y ∂m ∂m| := abs_add_le _ _
      _ ≤ (|(1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)| +
          |2 * ((1 / (N : ℝ)) * ∑ i, ∫ y, h (Y i) y ∂m)|) + |∫ x, ∫ y, h x y ∂m ∂m| :=
          add_le_add (abs_sub _ _) le_rfl
      _ ≤ (B * Qenv s Y + 2 * (Λm * (B * Ie))) + Λm * (B * Ie) :=
          add_le_add (add_le_add t1 t2) t3
      _ = _ := by ring
  have hEq : |∫ Y, quadStat h m Y ∂G| ≤ B * (EQ + 3 * Λm * Ie) := by
    have hqi : Integrable (fun Y : Config d N => quadStat h m Y) G :=
      eqrem_quad_integrable hd hs0 hsd V hV hβ hρ hN hg
    have h1 : |∫ Y, quadStat h m Y ∂G| ≤ ∫ Y, |quadStat h m Y| ∂G := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := G) (fun Y : Config d N => quadStat h m Y)
    refine h1.trans ?_
    have hri : Integrable (fun Y : Config d N => B * (Qenv s Y + 3 * Λm * Ie)) G :=
      (hQi.add (integrable_const _)).const_mul B
    refine (integral_mono hqi.abs hri hq).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add hQi (integrable_const _), integral_const, probReal_univ, one_smul]
  unfold remA
  simp only [← hG, ← hmdef, ← hμdef]
  set a := ∫ x, (kernelField h μ x - kernelField h m x) ∂(empirical X)
  set b := ∫ x, (kernelField h μ x - kernelField h m x) ∂m
  set q := quadStat h m X
  set Eq := ∫ Y, quadStat h m Y ∂G
  have hq' := hq X
  have e1 : |Real.sqrt N * (a - b)| ≤ Real.sqrt N * (2 * (B * ((Λ + Λm) * Ie))) := by
    rw [abs_mul, abs_of_nonneg hsq]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) hsq
    linarith
  have hs2 : 0 ≤ Real.sqrt N / 2 := div_nonneg hsq (by norm_num)
  have e2 : |Real.sqrt N / 2 * (q - Eq)| ≤ Real.sqrt N / 2 * (B * (Qenv s X + 3 * Λm * Ie) + B * (EQ + 3 * Λm * Ie)) := by
    rw [abs_mul, abs_of_nonneg hs2]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) hs2
    linarith
  calc |Real.sqrt N * (a - b) - Real.sqrt N / 2 * (q - Eq)|
      ≤ |Real.sqrt N * (a - b)| + |Real.sqrt N / 2 * (q - Eq)| := abs_sub _ _
    _ ≤ Real.sqrt N * (2 * (B * ((Λ + Λm) * Ie))) +
        Real.sqrt N / 2 * (B * (Qenv s X + 3 * Λm * Ie) + B * (EQ + 3 * Λm * Ie)) := add_le_add e1 e2
    _ = _ := by ring

end HRS.MD.EQRem

end
