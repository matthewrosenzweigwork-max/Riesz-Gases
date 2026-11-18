import HRS.MS.Fp81S21GaussUnif
import HRS.MS.S21G2_S12F
import HRS.MS.S21K2_P07A
import HRS.MS.Fp81S21RealizePatch

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2 HRS.MS.ProClosureS111 HRS.MS.S111T

private theorem fp81s21_gauss_unif_eval_meas
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (G : GaussianRealization R) (t : ℝ) (ht : 0 ≤ t)
    (φ : Euc p.d → ℝ) (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    Measurable (fun ω => OscDual.eval (G.Z t ω) φ) := by
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have hZU := G.evolution T
  have heq : (fun ω => OscDual.eval (G.Z t ω) φ) = gaussianOscEval
      (⟨φ, hφ⟩ : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ)) ∘ G.Z t := by
    funext ω
    exact (gaussianOscEval_apply
      (⟨φ, hφ⟩ : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ))
      (G.Z t ω)).symm
  rw [heq]
  exact (gaussianOscEval
    (⟨φ, hφ⟩ : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ))).continuous.measurable.comp
      (hZU.meas t)

/-- Every finite collection of evaluations of a supplied realization, and
therefore every continuous linear combination of them, is centered Gaussian. -/
private theorem fp81s21_gauss_unif_obs_linear_centered
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (G : GaussianRealization R) (T : ℝ) {n : ℕ}
    (τ : Fin n → ℝ) (φ : Fin n → Euc p.d → ℝ)
    (hτ : ∀ i, τ i ∈ Icc (0 : ℝ) T)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i))
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    HRS.IsCenteredGaussian
      (G.P.map fun ω => L (WithLp.toLp 2 fun i =>
        OscDual.eval (G.Z (τ i) ω) (φ i))) := by
  let V : G.Ω → EuclideanSpace ℝ (Fin n) := fun ω =>
    WithLp.toLp 2 fun i => OscDual.eval (G.Z (τ i) ω) (φ i)
  let S : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j =>
    HRS.Whole.linearGaussianCov (r26t3_coeff R) p.β⁻¹
      (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ) (τ i) (τ j) (φ i) (φ j)
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := multivariateGaussian 0 S
  have hZU := G.evolution T
  have hLaw : G.P.map V = μ := by
    change law G.P V = μ
    simpa [V, μ, S, HRS.Whole.linearGaussianCov, r26t3_coeff, r26t3_mu] using hZU.gaussian n τ φ hτ hφ
  have hVm : Measurable V := by
    apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    exact measurable_pi_iff.2 fun i => by
      exact fp81s21_gauss_unif_eval_meas G (τ i) (hτ i).1 (φ i) (hφ i)
  have hcenterV : HRS.IsCenteredGaussian (G.P.map V) := by
    rw [hLaw]
    exact HRS.MS.S111BD.s111_isCenteredGaussian_mvg n S
  have hmap : G.P.map (fun ω => L (V ω)) = (G.P.map V).map L := by
    rw [Measure.map_map L.continuous.measurable hVm]
    rfl
  rw [hmap]
  exact HRS.MS.R26T3.s21g2_s12_cg_map hcenterV L

private theorem fp81s21_gauss_unif_enorm_fourth_real (x : ℝ) :
    ‖x‖ₑ ^ (4 : ℝ) = ENNReal.ofReal (x ^ 4) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg x) (by norm_num)]
  congr 1
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.norm_eq_abs]
  calc
    |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
    _ = (x ^ 2) ^ 2 := by rw [sq_abs]
    _ = x ^ 4 := by ring

/-- A centered Gaussian scalar with second moment at most `v` has fourth
moment at most `3v^2`, stated in the form used by the coordinate adapter. -/
private theorem fp81s21_gauss_unif_real_fourth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hcenter : HRS.IsCenteredGaussian (P.map X))
    (v : ℝ) (hv : 0 ≤ v)
    (hsecond : (∫ ω, X ω ^ 2 ∂P) ≤ v) :
    ∫⁻ ω, ‖X ω‖ₑ ^ (4 : ℝ) ∂P ≤ ENNReal.ofReal (3 * v ^ 2) := by
  letI : IsGaussian (P.map X) := hcenter.1
  have hmean : ∫ x : ℝ, x ∂P.map X = 0 := by
    simpa using hcenter.2 (ContinuousLinearMap.id ℝ ℝ)
  have hVar : ProbabilityTheory.variance (id : ℝ → ℝ) (P.map X) =
      ∫ ω, X ω ^ 2 ∂P := by
    calc
      ProbabilityTheory.variance (id : ℝ → ℝ) (P.map X) =
          ∫ x : ℝ, x ^ 2 ∂P.map X := by
        simpa [id] using
          (ProbabilityTheory.variance_of_integral_eq_zero
            (μ := P.map X) (X := id) measurable_id'.aemeasurable hmean)
      _ = ∫ ω, X ω ^ 2 ∂P :=
        integral_map hX.aemeasurable
          (continuous_pow 2).aestronglyMeasurable
  have hVar0 : 0 ≤ ProbabilityTheory.variance (id : ℝ → ℝ) (P.map X) := by
    rw [hVar]
    exact integral_nonneg fun ω => sq_nonneg (X ω)
  have hVarBound : ProbabilityTheory.variance (id : ℝ → ℝ) (P.map X) ≤ v := by
    rw [hVar]
    exact hsecond
  have hDlaw : P.map X = gaussianReal 0
      (Real.toNNReal (ProbabilityTheory.variance (id : ℝ → ℝ) (P.map X))) := by
    have h := IsGaussian.map_eq_gaussianReal
      (μ := P.map X) (ContinuousLinearMap.id ℝ ℝ)
    have hmean' : ∫ x : ℝ, (ContinuousLinearMap.id ℝ ℝ) x ∂P.map X = 0 := by
      simpa using hmean
    have hvar' : ProbabilityTheory.variance (ContinuousLinearMap.id ℝ ℝ)
        (P.map X) = ProbabilityTheory.variance (id : ℝ → ℝ) (P.map X) := by
      rfl
    rw [hmean', hvar'] at h
    simpa using h
  have hfourInt : Integrable (fun ω => X ω ^ 4) P := by
    have hmem : MemLp (id : ℝ → ℝ) 4 (P.map X) :=
      IsGaussian.memLp_id (P.map X) 4 (by norm_num)
    have hfour : Integrable (fun x : ℝ => x ^ 4) (P.map X) := by
      have hnorm := hmem.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
      have heq : (fun x : ℝ => ‖id x‖ ^ 4) = fun x => x ^ 4 := by
        funext x
        simp only [id, Real.norm_eq_abs]
        calc
          |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
          _ = (x ^ 2) ^ 2 := by rw [sq_abs]
          _ = x ^ 4 := by ring
      rw [heq] at hnorm
      exact hnorm
    exact (integrable_map_measure
      (continuous_pow 4).aestronglyMeasurable hX.aemeasurable).1 hfour
  have hrealFourth :
      (∫ ω, X ω ^ 4 ∂P) =
        3 * (ProbabilityTheory.variance (id : ℝ → ℝ) (P.map X)) ^ 2 := by
    calc
      _ = ∫ x : ℝ, x ^ 4 ∂P.map X :=
        (integral_map hX.aemeasurable
          (continuous_pow 4).aestronglyMeasurable).symm
      _ = ∫ x : ℝ, x ^ 4 ∂gaussianReal 0
          (Real.toNNReal (ProbabilityTheory.variance (id : ℝ → ℝ) (P.map X))) := by
        exact congrArg (fun ν : Measure ℝ => ∫ x : ℝ, x ^ 4 ∂ν) hDlaw
      _ = (Real.toNNReal (ProbabilityTheory.variance (id : ℝ → ℝ)
            (P.map X)) : ℝ) ^ 2 * HRS.Yurinskii.c4 :=
        HRS.Yurinskii.integral_pow4_gaussianReal _
      _ = _ := by
        rw [show HRS.Yurinskii.c4 = 3 from HRS.gauss_m4,
          Real.coe_toNNReal
            (ProbabilityTheory.variance (id : ℝ → ℝ) (P.map X)) hVar0]
        ring
  have hEnorm :
      (∫⁻ ω, ‖X ω‖ₑ ^ (4 : ℝ) ∂P) =
        ENNReal.ofReal (3 * (ProbabilityTheory.variance (id : ℝ → ℝ)
          (P.map X)) ^ 2) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (X ω ^ 4) ∂P := by
        apply lintegral_congr
        exact fun ω => fp81s21_gauss_unif_enorm_fourth_real (X ω)
      _ = ENNReal.ofReal (∫ ω, X ω ^ 4 ∂P) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hfourInt
          (ae_of_all _ fun ω => by positivity)
      _ = _ := by rw [hrealFourth]
  calc
    _ = ENNReal.ofReal (3 *
        (ProbabilityTheory.variance (id : ℝ → ℝ) (P.map X)) ^ 2) := hEnorm
    _ ≤ ENNReal.ofReal (3 * v ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [hVar0, hVarBound, hv]

/-- A time slice of a supplied Gaussian realization has a fourth norm moment
bounded by three times the square of its uniform coordinate trace. -/
theorem fp81s21_gauss_unif_one_time_fourth
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (Vbound : ℝ)
    (hTrace : 0 ≤ Vbound ∧
      ∀ t : ℝ, 0 ≤ t → ∀ G : GaussianRealization R,
        Summable (fun α : MultiIndex p.d =>
          ∫ ω, (OscDual.coord (G.Z t ω) α) ^ 2 ∂G.P) ∧
        (∑' α : MultiIndex p.d,
          ∫ ω, (OscDual.coord (G.Z t ω) α) ^ 2 ∂G.P) ≤ Vbound)
    (t : ℝ) (ht : 0 ≤ t) (G : GaussianRealization R) :
    ∫⁻ ω, ‖G.Z t ω‖ₑ ^ (4 : ℝ) ∂G.P ≤ ENNReal.ofReal (3 * Vbound ^ 2) := by
  let v : MultiIndex p.d → ℝ := fun α =>
    ∫ ω, (OscDual.coord (G.Z t ω) α) ^ 2 ∂G.P
  have hv : ∀ α, 0 ≤ v α := by
    intro α
    exact integral_nonneg fun ω => sq_nonneg _
  have hvs : Summable v := by
    simpa [v] using (hTrace.2 t ht G).1
  have hcoord4 : ∀ α : MultiIndex p.d,
      ∫⁻ ω, ‖OscDual.coord (G.Z t ω) α‖ₑ ^ (4 : ℝ) ∂G.P ≤
        ENNReal.ofReal (3 * (v α) ^ 2) := by
    intro α
    let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
    have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ :=
      HRS.MS.GenPath.s56_isOscTest _ α
    let τ : Fin 1 → ℝ := fun _ => t
    let ψ : Fin 1 → Euc p.d → ℝ := fun _ => φ
    let L : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := EuclideanSpace.proj 0
    let X : G.Ω → ℝ := fun ω => OscDual.eval (G.Z t ω) φ
    have hτ : ∀ i : Fin 1, τ i ∈ Icc (0 : ℝ) (t + 1) := by
      intro i
      exact ⟨ht, by linarith⟩
    have hψ : ∀ i : Fin 1, IsOscTest (wholeSpaceIndex p.d : ℝ) (ψ i) := fun _ => hφ
    have hcenter := fp81s21_gauss_unif_obs_linear_centered p R G (t + 1)
      τ ψ hτ hψ L
    have hXcenter : HRS.IsCenteredGaussian (G.P.map X) := by
      have heq : (fun ω => L (WithLp.toLp 2 fun i =>
          OscDual.eval (G.Z (τ i) ω) (ψ i))) = X := by
        funext ω
        simp [L, X, τ, ψ]
      rw [← heq]
      exact hcenter
    have hXmeas : Measurable X :=
      fp81s21_gauss_unif_eval_meas G t ht φ hφ
    have hevalcoord : ∀ ω,
        OscDual.coord (G.Z t ω) α = X ω := by
      intro ω
      exact (OscDual.eval_oscTestFun (G.Z t ω) α).symm
    have hsecond : (∫ ω, X ω ^ 2 ∂G.P) ≤ v α := by
      apply le_of_eq
      dsimp [v]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω =>
        congrArg (fun x : ℝ => x ^ 2) (hevalcoord ω).symm
    have hscalar := fp81s21_gauss_unif_real_fourth X hXmeas hXcenter
      (v α) (hv α) hsecond
    calc
      _ = ∫⁻ ω, ‖X ω‖ₑ ^ (4 : ℝ) ∂G.P := by
        apply lintegral_congr
        exact fun ω => by rw [hevalcoord ω]
      _ ≤ ENNReal.ofReal (3 * (v α) ^ 2) := hscalar
  have hYmeas : Measurable (G.Z t) := (G.evolution (t + 1)).meas t
  have hnorm := fp81s21_coord_fourth_to_norm_fourth
    (G.Z t) hYmeas v hv hvs hcoord4
  have hsum0 : 0 ≤ ∑' α : MultiIndex p.d, v α := tsum_nonneg hv
  calc
    _ ≤ ENNReal.ofReal (3 * (∑' α : MultiIndex p.d, v α) ^ 2) := hnorm
    _ ≤ ENNReal.ofReal (3 * Vbound ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      have hle := (hTrace.2 t ht G).2
      nlinarith [hsum0, hle, hTrace.1]

private theorem fp81s21_gauss_unif_norm_increment_fourth_of_observations
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (H : ℝ) (hH : 0 < H) (a : ℝ) (ha : 0 ≤ a)
    (G : GaussianRealization R) (L : MultiIndex p.d → ℝ)
    (hL0 : ∀ α, 0 ≤ L α) (hLsum : Summable L)
    (hobs : ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
      ∀ α : MultiIndex p.d,
        Integrable (fun ω => |OscDual.eval (G.Z (a + t) ω)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α) -
          OscDual.eval (G.Z (a + s) ω)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)| ^ 2) G.P ∧
        (∫ ω, |OscDual.eval (G.Z (a + t) ω)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α) -
          OscDual.eval (G.Z (a + s) ω)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)| ^ 2 ∂G.P) ≤
          L α * |t - s|)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) H)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) :
    ∫⁻ ω, ‖G.Z (a + t) ω - G.Z (a + s) ω‖ₑ ^ (4 : ℝ) ∂G.P ≤
      ENNReal.ofReal (3 * (∑' α, L α) ^ 2 * |t - s| ^ 2) := by
  let v : MultiIndex p.d → ℝ := fun α => L α * |t - s|
  have hv0 : ∀ α, 0 ≤ v α := by
    intro α
    exact mul_nonneg (hL0 α) (abs_nonneg _)
  have hvs : Summable v := by
    have h := hLsum.mul_left |t - s|
    exact h.congr fun α => by simp [v, mul_comm]
  let Y : G.Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ) :=
    fun ω => G.Z (a + t) ω - G.Z (a + s) ω
  have hYmeas : Measurable Y := by
    have ht0 : 0 ≤ a + t := by linarith [ht.1]
    have hs0 : 0 ≤ a + s := by linarith [hs.1]
    exact ((G.evolution (a + t + 1)).meas (a + t)).sub
      ((G.evolution (a + s + 1)).meas (a + s))
  have hcoord4 : ∀ α : MultiIndex p.d,
      ∫⁻ ω, ‖OscDual.coord (Y ω) α‖ₑ ^ (4 : ℝ) ∂G.P ≤
        ENNReal.ofReal (3 * (v α) ^ 2) := by
    intro α
    let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
    have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ :=
      HRS.MS.GenPath.s56_isOscTest _ α
    have hmom := hobs s hs t ht α
    let u : ℝ := a + t
    let w : ℝ := a + s
    let τ : Fin 2 → ℝ := fun i => if i = 0 then u else w
    let ψ : Fin 2 → Euc p.d → ℝ := fun _ => φ
    let Ldiff : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
      EuclideanSpace.proj 0 - EuclideanSpace.proj 1
    let D : G.Ω → ℝ := fun ω =>
      OscDual.eval (G.Z u ω) φ - OscDual.eval (G.Z w ω) φ
    have hu : 0 ≤ u := by dsimp [u]; linarith [ha, ht.1]
    have hw : 0 ≤ w := by dsimp [w]; linarith [ha, hs.1]
    let T : ℝ := max u w + 1
    have hτ : ∀ i : Fin 2, τ i ∈ Icc (0 : ℝ) T := by
      have huT : u ≤ T := by dsimp [T]; linarith [le_max_left u w]
      have hwT : w ≤ T := by dsimp [T]; linarith [le_max_right u w]
      intro i
      fin_cases i
      · simpa [τ] using (show u ∈ Icc (0 : ℝ) T from ⟨hu, huT⟩)
      · simpa [τ] using (show w ∈ Icc (0 : ℝ) T from ⟨hw, hwT⟩)
    have hψ : ∀ i : Fin 2, IsOscTest (wholeSpaceIndex p.d : ℝ) (ψ i) := fun _ => hφ
    have hcenter := fp81s21_gauss_unif_obs_linear_centered p R G T τ ψ hτ hψ Ldiff
    have hDcenter : HRS.IsCenteredGaussian (G.P.map D) := by
      have heq : (fun ω => Ldiff (WithLp.toLp 2 fun i =>
          OscDual.eval (G.Z (τ i) ω) (ψ i))) = D := by
        funext ω
        simp [D, Ldiff, τ, ψ, u, w]
      rw [← heq]
      exact hcenter
    have hDmeas : Measurable D :=
      (fp81s21_gauss_unif_eval_meas G u hu φ hφ).sub
        (fp81s21_gauss_unif_eval_meas G w hw φ hφ)
    have hsecond : (∫ ω, D ω ^ 2 ∂G.P) ≤ v α := by
      have h' := hmom.2
      simpa [D, u, w, v, sq_abs] using h'
    have hscalar := fp81s21_gauss_unif_real_fourth D hDmeas hDcenter
      (v α) (hv0 α) hsecond
    have hcoord : ∀ ω, OscDual.coord (Y ω) α = D ω := by
      intro ω
      change s111t_coordCLM p.d (wholeSpaceIndex p.d : ℝ) α
        (G.Z (a + t) ω - G.Z (a + s) ω) = _
      rw [map_sub]
      rw [s111t_coordCLM_apply, s111t_coordCLM_apply]
      dsimp [D, u, w]
      rw [← OscDual.eval_oscTestFun, ← OscDual.eval_oscTestFun]
    calc
      _ = ∫⁻ ω, ‖D ω‖ₑ ^ (4 : ℝ) ∂G.P := by
        apply lintegral_congr
        exact fun ω => by rw [hcoord ω]
      _ ≤ ENNReal.ofReal (3 * (v α) ^ 2) := hscalar
  have hNorm := fp81s21_coord_fourth_to_norm_fourth Y hYmeas v hv0 hvs hcoord4
  have hsum : (∑' α : MultiIndex p.d, v α) =
      (∑' α : MultiIndex p.d, L α) * |t - s| := by
    simp [v, tsum_mul_right]
  calc
    _ ≤ ENNReal.ofReal (3 * (∑' α : MultiIndex p.d, v α) ^ 2) := hNorm
    _ = ENNReal.ofReal (3 * (∑' α : MultiIndex p.d, L α) ^ 2 * |t - s| ^ 2) := by
      congr 1
      rw [hsum]
      ring

/-- The supplied-realization fourth-increment bound, with its summable
modewise coefficient chosen before the shift and the realization. -/
theorem fp81s21_gauss_unif_increment_fourth (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ H : ℝ, 0 < H →
          ∃ L : MultiIndex p.d → ℝ,
            (∀ α, 0 ≤ L α) ∧ Summable L ∧
            ∀ a : ℝ, 0 ≤ a → ∀ G : GaussianRealization R,
              ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
                ∫⁻ ω, ‖G.Z (a + t) ω - G.Z (a + s) ω‖ₑ ^ (4 : ℝ) ∂G.P ≤
                  ENNReal.ofReal
                    (3 * (∑' α : MultiIndex p.d, L α) ^ 2 * |t - s| ^ 2) := by
  obtain ⟨δ0, hδ0, hδ0half, hG2⟩ := fp81s21_gaussian_increment_bound p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R H hH
  obtain ⟨L, hL0, hLsum, hInc⟩ := hG2 δ hδ hδle R H hH
  refine ⟨L, hL0, hLsum, ?_⟩
  intro a ha G s hs t ht
  exact fp81s21_gauss_unif_norm_increment_fourth_of_observations
    H hH a ha G L hL0 hLsum (hInc a ha G) s hs t ht

#print axioms fp81s21_gauss_unif_eval_meas
#print axioms fp81s21_gauss_unif_obs_linear_centered
#print axioms fp81s21_gauss_unif_real_fourth
#print axioms fp81s21_gauss_unif_one_time_fourth
#print axioms fp81s21_gauss_unif_increment_fourth

end HRS.Fp81.S21

end
