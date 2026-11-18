import HRS.MS.Fp81S21WickG
import HRS.MS.PROS15dGaussianLimitB18
import HRS.MS.S21G2_S11aC

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

private theorem fp81s21_wickG_centered_of_scalar_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {v : ℝ≥0}
    (hX : P.map X = gaussianReal 0 v) :
    HRS.IsCenteredGaussian (P.map X) := by
  have hGaussian : IsGaussian (P.map X) := by
    rw [hX]
    infer_instance
  have hmean : ∫ x, x ∂(P.map X) = 0 := by
    rw [hX]
    exact integral_id_gaussianReal
  refine ⟨hGaussian, fun L => ?_⟩
  calc
    ∫ x, L x ∂(P.map X) = L (∫ x, id x ∂(P.map X)) :=
      ContinuousLinearMap.integral_comp_comm L (IsGaussian.integrable_id (μ := P.map X))
    _ = L 0 := by
      exact congrArg L (by simpa only [id] using hmean)
    _ = 0 := map_zero L

private theorem fp81s21_wickG_extended_scalar_gaussian
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (G : GaussianRealization R) {u : ℝ} (hu : 0 ≤ u)
    (L : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 G.P)
    (hAgree : ∀ φ : Euc p.d → ℝ,
      IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
      ∀ hφ : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ),
        L (hφ.toLp φ) =ᵐ[G.P] fun w => OscDual.eval (G.Z u w) φ)
    (hTestGaussian : ∀ φ : Euc p.d → ℝ,
      IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
      ∃ v : ℝ≥0, G.P.map (fun w => OscDual.eval (G.Z u w) φ) = gaussianReal 0 v)
    (g : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)) :
    HRS.IsCenteredGaussian (G.P.map fun w => (L g) w) := by
  classical
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  have hμprob : IsProbabilityMeasure μstar :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  letI : IsProbabilityMeasure μstar := hμprob
  let testSub : Submodule ℝ (Euc p.d → ℝ) :=
    HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ)
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hρmeas : Measurable R.ρβ := by
    obtain ⟨-, ψ'', hψ''⟩ := HRS.MS.S21.s21_schwartz_thermal
      p.hd p.hs0 hsd p.ha p.hβ
    rw [hρeq, ← hψ'']
    exact ψ''.continuous.measurable
  obtain ⟨M, hM, hthermal⟩ := HRS.Fp81.S21.sol13_uniform_thermal_sup_bound p
  have htest : ∀ φ ∈ testSub, MemLp φ 2 μstar := by
    intro φ hφ
    exact HRS.MS.S111X1.x1_osc_memLp hρmeas
      (fun x => (HRS.Whole.u4_thermal_pos R.thermal x).le)
      (hthermal δ R) hφ
  let testLp := HRS.MS.TensRel.s111_toLp testSub htest
  have hdense : DenseRange testLp :=
    fp81s21_gaussLin_test_dense p R (by simpa [testSub, μstar] using htest)
  obtain ⟨uSeq, huMem, huTendsto⟩ :=
    mem_closure_iff_seq_limit.1 (hdense g)
  choose φ hφ using huMem
  have huEq : ∀ n, uSeq n = testLp (φ n) := fun n => (hφ n).symm
  let X : ℕ → G.Ω → ℝ := fun n w => (L (uSeq n)) w
  have hXm : ∀ n, AEStronglyMeasurable (X n) G.P := fun n =>
    (Lp.stronglyMeasurable (L (uSeq n))).aestronglyMeasurable
  have hX : ∀ n, HRS.IsCenteredGaussian (G.P.map (X n)) := by
    intro n
    obtain ⟨v, hLawEval⟩ := hTestGaussian (φ n) (φ n).2
    have hAgreeN : L (testLp (φ n)) =ᵐ[G.P]
        fun w => OscDual.eval (G.Z u w) (φ n : Euc p.d → ℝ) := by
      simpa [testLp, HRS.MS.TensRel.s111_toLp] using
        hAgree (φ n : Euc p.d → ℝ) (φ n).2 (htest (φ n) (φ n).2)
    have hLaw : G.P.map (X n) = gaussianReal 0 v := by
      have hfun : (fun w => X n w) = fun w => (L (testLp (φ n))) w := by
        funext w
        simp only [X]
        rw [huEq n]
      have hfun' : X n = fun w => (L (testLp (φ n))) w := by
        funext w
        exact congrFun hfun w
      have hfunAE : X n =ᵐ[G.P] fun w => (L (testLp (φ n))) w :=
        Filter.Eventually.of_forall fun w => congrFun hfun' w
      calc
        G.P.map (X n) = G.P.map (fun w => (L (testLp (φ n))) w) :=
          Measure.map_congr hfunAE
        _ = gaussianReal 0 v := (Measure.map_congr hAgreeN).trans hLawEval
    exact fp81s21_wickG_centered_of_scalar_law hLaw
  have hLconv : Tendsto (fun n => L (uSeq n)) atTop (𝓝 (L g)) :=
    (L.continuous.tendsto g).comp huTendsto
  have hLpTarget : (Lp.memLp (L g)).toLp (fun w => (L g) w) = L g :=
    Lp.toLp_coeFn (L g) (Lp.memLp (L g))
  have hLconv' : Tendsto (fun n => L (uSeq n)) atTop
      (𝓝 ((Lp.memLp (L g)).toLp (fun w => (L g) w))) := by
    rw [hLpTarget]
    exact hLconv
  have hL2 : Tendsto
      (fun n => eLpNorm (fun w => X n w - (L g) w) 2 G.P) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm (fun n => L (uSeq n))
      (fun w => (L g) w) (Lp.memLp (L g))).1 hLconv'
  exact HRS.MS.R26T3.s15d_centered_gaussian_L2_limit
    G.P X (fun w => (L g) w) hXm hX hL2

/-- The Gaussian extension of the oscillator evaluation map has jointly
centered Gaussian finite-dimensional laws for arbitrary reference `L²`
inputs.  The covariance entries are the `L²(G.P)` inner products, equivalently
the second moments because the extension is centered. -/
theorem fp81s21_wickG_extension_joint_gaussian (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ Kstar : ℝ, 0 ≤ Kstar ∧
          ∀ G : GaussianRealization R, ∀ u : ℝ, 0 ≤ u →
            ∃ L : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 G.P,
              ‖L‖ ≤ Kstar ∧
              (∀ φ : Euc p.d → ℝ,
                IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
                ∀ hφ : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ),
                  L (hφ.toLp φ) =ᵐ[G.P]
                    fun w => OscDual.eval (G.Z u w) φ) ∧
              (∀ f : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ),
                ∫ w, (L f) w ∂G.P = 0) ∧
              ∀ n (f : Fin n → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
                HRS.IsCenteredGaussian
                  (G.P.map fun w => fun i => (L (f i)) w) ∧
                ∀ i j,
                  inner ℝ (L (f i)) (L (f j)) =
                    ∫ w, (L (f i)) w * (L (f j)) w ∂G.P := by
  obtain ⟨δe, hδe, hδehalf, hExt⟩ := fp81s21_gaussLin_extension p
  obtain ⟨δg, hδg, hδghalf, hGaussian⟩ := fp81s21_gaussLin_test_gaussian_law p
  let δ0 := min δe δg
  have hδ0 : 0 < δ0 := lt_min hδe hδg
  have hδ0half : δ0 ≤ 1 / 2 := le_trans (min_le_left _ _) hδehalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδ0δ R
  have hδeR : δ ≤ δe := hδ0δ.trans (min_le_left _ _)
  have hδgR : δ ≤ δg := hδ0δ.trans (min_le_right _ _)
  obtain ⟨Kstar, hKstar, hExtR⟩ := hExt δ hδ hδeR R
  refine ⟨Kstar, hKstar, ?_⟩
  intro G u hu
  obtain ⟨L, hL, hAgree, hCenter, hUnique⟩ := hExtR G u hu
  refine ⟨L, hL, hAgree, hCenter, ?_⟩
  intro n f
  let X : G.Ω → (Fin n → ℝ) := fun w i => (L (f i)) w
  have hXm : AEMeasurable X G.P :=
    AEMeasurable.of_eval fun i =>
      (Lp.stronglyMeasurable (L (f i))).aestronglyMeasurable.aemeasurable
  have hComb : ∀ c : Fin n → ℝ,
      ∃ v : ℝ≥0, G.P.map (fun w => ∑ i, c i * X w i) = gaussianReal 0 v := by
    intro c
    let g : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) := ∑ i, c i • f i
    have hScalar := fp81s21_wickG_extended_scalar_gaussian p R G hu L hAgree
      (fun φ hφ => hGaussian δ hδ hδgR R G u hu φ hφ) g
    let Y : G.Ω → ℝ := fun w => ∑ i, c i * X w i
    have hLp : L g = ∑ i, c i • L (f i) := by
      dsimp [g]
      simp only [map_sum, map_smul]
    have hsum : (∑ i : Fin n, c i • L (f i) : Lp ℝ 2 G.P) =ᵐ[G.P]
        fun w => ∑ i, c i * (L (f i)) w := by
      have h1 : (∑ i : Fin n, c i • L (f i) : Lp ℝ 2 G.P) =ᵐ[G.P]
          fun w => ∑ i, (c i • L (f i) : Lp ℝ 2 G.P) w := by
        simpa using HRS.A33.a33_coeFn_sum (P := G.P) Finset.univ
          (fun i => c i • L (f i))
      have h2 : ∀ᵐ w ∂G.P, ∀ i : Fin n,
          (c i • L (f i) : Lp ℝ 2 G.P) w = c i * (L (f i)) w := by
        rw [ae_all_iff]
        intro i
        filter_upwards [Lp.coeFn_smul (c i) (L (f i))] with w hw
        simpa [smul_eq_mul] using hw
      filter_upwards [h1, h2] with w ha hb
      rw [ha]
      exact Finset.sum_congr rfl fun i _ => hb i
    have hLpFun : (fun w => (L g) w) =
        fun w => (∑ i : Fin n, c i • L (f i) : Lp ℝ 2 G.P) w := by
      exact congrArg (fun q : Lp ℝ 2 G.P => (q : G.Ω → ℝ)) hLp
    have hLpAE : (fun w => (L g) w) =ᵐ[G.P]
        fun w => ∑ i, c i * (L (f i)) w := by
      have hfun : (fun w => (L g) w) =ᵐ[G.P]
          fun w => (∑ i : Fin n, c i • L (f i) : Lp ℝ 2 G.P) w :=
        Filter.Eventually.of_forall fun w => congrFun hLpFun w
      exact hfun.trans hsum
    have hYae : Y =ᵐ[G.P] fun w => (L g) w := by
      filter_upwards [hLpAE] with w hw
      exact hw.symm
    have hScalarY : HRS.IsCenteredGaussian (G.P.map Y) := by
      have hmap : G.P.map Y = G.P.map (fun w => (L g) w) := Measure.map_congr hYae
      rw [hmap]
      exact hScalar
    have hYmeas : AEMeasurable Y G.P :=
      (Lp.stronglyMeasurable (L g)).aestronglyMeasurable.aemeasurable.congr hYae.symm
    have hMean : (G.P.map Y)[(ContinuousLinearMap.id ℝ ℝ)] = 0 :=
      hScalarY.2 (ContinuousLinearMap.id ℝ ℝ)
    have hLawId := hScalarY.1.map_eq_gaussianReal (ContinuousLinearMap.id ℝ ℝ)
    have hmapId : (G.P.map Y).map (ContinuousLinearMap.id ℝ ℝ) = G.P.map Y := by
      rw [AEMeasurable.map_map_of_aemeasurable
        (ContinuousLinearMap.id ℝ ℝ).continuous.measurable.aemeasurable hYmeas]
      rfl
    rw [hmapId, hMean] at hLawId
    refine ⟨(Var[(ContinuousLinearMap.id ℝ ℝ); G.P.map Y]).toNNReal, ?_⟩
    simpa [Y] using hLawId
  have hJoint : HRS.IsCenteredGaussian (G.P.map X) :=
    HRS.MS.R26T3.s21g2_s11a_gauss_of_laws hXm hComb
  refine ⟨hJoint, ?_⟩
  intro i j
  rw [L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp
  ring

#print axioms fp81s21_wickG_oscillator_joint_law
#print axioms fp81s21_wickG_extension_joint_gaussian

end HRS.Fp81.S21

end
