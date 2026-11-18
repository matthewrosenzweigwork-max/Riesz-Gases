import HRS.MS.Fp81S21GaussLin
import HRS.MS.ProClosureS111PhysicalWick
import HRS.MS.TensRelAux1

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

private theorem fp81s21_gaussLin_thermal_measurable₂
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) : Measurable R.ρβ := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hcont : Continuous R.ρβ := by
    obtain ⟨-, ψ'', hψ''⟩ := HRS.MS.S21.s21_schwartz_thermal
      p.hd p.hs0 hsd p.ha p.hβ
    rw [hρeq, ← hψ'']
    exact ψ''.continuous
  exact hcont.measurable

/--
The compact smooth tests form a dense subspace of `L²(μstar)`.  Compactly
supported smooth functions are oscillator tests, and their `L²` classes are
dense because `μstar` is finite.
-/
theorem fp81s21_gaussLin_test_dense (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ)
    (hS : ∀ φ ∈ HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ),
      MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ)) :
    DenseRange (HRS.MS.TensRel.s111_toLp
      (HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ))
      hS) := by
  classical
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  have hμprob : IsProbabilityMeasure μstar :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  letI : IsProbabilityMeasure μstar := hμprob
  obtain ⟨M, hM, hthermal⟩ := HRS.Fp81.S21.sol13_uniform_thermal_sup_bound p
  let testSub : Submodule ℝ (Euc p.d → ℝ) :=
    HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ)
  have htest : ∀ φ ∈ testSub, MemLp φ 2 μstar := by
    intro φ hφ
    exact HRS.MS.S111X1.x1_osc_memLp
      (fp81s21_gaussLin_thermal_measurable₂ p R)
      (fun x => (HRS.Whole.u4_thermal_pos R.thermal x).le)
      (hthermal δ R) hφ
  let testLp := HRS.MS.TensRel.s111_toLp testSub htest
  let D : Set (Lp ℝ 2 μstar) := {f | ∃ g : Euc p.d → ℝ,
    f =ᵐ[μstar] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g}
  have hD : Dense D := by
    exact MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (F := ℝ) (E := Euc p.d) (μ := μstar) (p := (2 : ℝ≥0∞)) (by norm_num)
  have hsub : D ⊆ Set.range testLp := by
    rintro f ⟨g, hfg, hgcs, hgcd⟩
    let φ : testSub := ⟨g, HRS.MS.S21E.s21e_isOscTest_of_cc hgcd hgcs
      (wholeSpaceIndex p.d : ℝ)⟩
    have hg : MemLp g 2 μstar := htest g φ.2
    have hfgLp : f = hg.toLp g := by
      apply Lp.ext
      exact hfg.trans hg.coeFn_toLp.symm
    have htestLp : testLp φ = hg.toLp g := by
      dsimp [testLp, HRS.MS.TensRel.s111_toLp]
    refine ⟨φ, ?_⟩
    exact htestLp.trans hfgLp.symm
  have hdense : Dense (Set.range testLp) := hD.mono hsub
  change DenseRange testLp
  exact hdense

/--
Uniform bounded extension of the supplied moving Gaussian evaluation map.  The
output is a continuous linear map on the full reference space.  It agrees with
oscillator tests, is centered on every input, and is uniquely determined by
that dense test agreement.
-/
theorem fp81s21_gaussLin_extension (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ Kstar : ℝ, 0 ≤ Kstar ∧
          ∀ G : GaussianRealization R, ∀ u : ℝ, 0 ≤ u →
            ∃ L : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ]
                Lp ℝ 2 G.P,
              ‖L‖ ≤ Kstar ∧
              (∀ φ : Euc p.d → ℝ,
                IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
                ∀ hφ : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ),
                  L (hφ.toLp φ) =ᵐ[G.P]
                    (fun w => OscDual.eval (G.Z u w) φ)) ∧
              (∀ f : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ),
                ∫ w, (L f) w ∂G.P = 0) ∧
              (∀ L' : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ]
                  Lp ℝ 2 G.P,
                (∀ φ : Euc p.d → ℝ,
                  IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
                  ∀ hφ : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ),
                    L' (hφ.toLp φ) =ᵐ[G.P]
                      (fun w => OscDual.eval (G.Z u w) φ)) →
                L' = L) := by
  obtain ⟨δm, hδm, hδmhalf, hmoment⟩ :=
    fp81s21_gaussLin_test_second_moment_bound p
  obtain ⟨δg, hδg, hδghalf, hgauss⟩ :=
    fp81s21_gaussLin_test_gaussian_law p
  let δ0 := min δm δg
  have hδ0 : 0 < δ0 := lt_min hδm hδg
  have hδ0half : δ0 ≤ 1 / 2 := le_trans (min_le_left _ _) hδmhalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδ0δ R
  have hδmR : δ ≤ δm := hδ0δ.trans (min_le_left _ _)
  have hδgR : δ ≤ δg := hδ0δ.trans (min_le_right _ _)
  obtain ⟨Kstar, hKstar, hMomentR⟩ := hmoment δ hδ hδmR R
  refine ⟨Kstar, hKstar, ?_⟩
  intro G u hu
  classical
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  have hμprob : IsProbabilityMeasure μstar :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  letI : IsProbabilityMeasure μstar := hμprob
  let testSub : Submodule ℝ (Euc p.d → ℝ) :=
    HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ)
  have htest : ∀ φ ∈ testSub, MemLp φ 2 μstar := by
    intro φ hφ
    obtain ⟨M, hM, hthermal⟩ := HRS.Fp81.S21.sol13_uniform_thermal_sup_bound p
    exact HRS.MS.S111X1.x1_osc_memLp
      (fp81s21_gaussLin_thermal_measurable₂ p R)
      (fun x => (HRS.Whole.u4_thermal_pos R.thermal x).le)
      (hthermal δ R) hφ
  let testLp : testSub →ₗ[ℝ] Lp ℝ 2 μstar :=
    HRS.MS.TensRel.s111_toLp testSub htest
  let evalMem : ∀ φ : testSub,
      MemLp (fun w => OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ)) 2 G.P :=
    fun φ => (hMomentR G u hu (φ : Euc p.d → ℝ) φ.2 (htest φ φ.2)).1
  let evalLp : testSub →ₗ[ℝ] Lp ℝ 2 G.P := {
    toFun := fun φ => (evalMem φ).toLp (fun w => OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ))
    map_add' := by
      intro φ ψ
      have hφ := evalMem φ
      have hψ := evalMem ψ
      have hsum := evalMem (φ + ψ)
      have hpoint : ∀ w : G.Ω,
          OscDual.eval (G.Z u w) ((φ + ψ : testSub) : Euc p.d → ℝ) =
            OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ) +
              OscDual.eval (G.Z u w) (ψ : Euc p.d → ℝ) := by
        intro w
        let ev := HRS.MS.ProClosureS111.gaussianTestEvaluation (G.Z u w)
        calc
          _ = ev (φ + ψ) :=
            (HRS.MS.ProClosureS111.gaussianTestEvaluation_apply _ _).symm
          _ = ev φ + ev ψ := ev.map_add φ ψ
          _ = _ := by simp [ev, HRS.MS.ProClosureS111.gaussianTestEvaluation_apply]
      have h := MemLp.toLp_add hφ hψ
      exact (MemLp.toLp_congr _ _ (Filter.Eventually.of_forall hpoint)).trans h
    map_smul' := by
      intro c φ
      have hφ := evalMem φ
      have hsmul := evalMem (c • φ)
      have hpoint : ∀ w : G.Ω,
          OscDual.eval (G.Z u w) ((c • φ : testSub) : Euc p.d → ℝ) =
            c * OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ) := by
        intro w
        let ev := HRS.MS.ProClosureS111.gaussianTestEvaluation (G.Z u w)
        calc
          _ = ev (c • φ) :=
            (HRS.MS.ProClosureS111.gaussianTestEvaluation_apply _ _).symm
          _ = c • ev φ := ev.map_smul c φ
          _ = _ := by simp [ev, HRS.MS.ProClosureS111.gaussianTestEvaluation_apply,
            smul_eq_mul]
      have h := MemLp.toLp_const_smul (μ := G.P) (p := 2) c hφ
      exact (MemLp.toLp_congr _ _ (Filter.Eventually.of_forall hpoint)).trans h
  }
  have hevalBound : ∀ φ : testSub,
      ‖evalLp φ‖ ≤ Kstar * ‖testLp φ‖ := by
    intro φ
    obtain ⟨hm, hsecond, hbound⟩ :=
      hMomentR G u hu (φ : Euc p.d → ℝ) φ.2 (htest φ φ.2)
    have hsource : ‖testLp φ‖ =
        Real.sqrt (∫ x, (φ : Euc p.d → ℝ) x ^ 2 ∂μstar) :=
      HRS.MS.S111X1.x1_toLp_norm (htest φ φ.2)
    have htarget : ‖evalLp φ‖ =
        Real.sqrt (∫ w, OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ) ^ 2 ∂G.P) :=
      HRS.MS.S111X1.x1_toLp_norm (evalMem φ)
    rw [htarget, hsource]
    have hI : 0 ≤ ∫ x, (φ : Euc p.d → ℝ) x ^ 2 ∂μstar :=
      integral_nonneg fun x => sq_nonneg _
    have hJ : 0 ≤ ∫ w, OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ) ^ 2 ∂G.P :=
      integral_nonneg fun w => sq_nonneg _
    have hsq :
        (Real.sqrt (∫ w, OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ) ^ 2 ∂G.P)) ^ 2 ≤
          (Kstar * Real.sqrt (∫ x, (φ : Euc p.d → ℝ) x ^ 2 ∂μstar)) ^ 2 := by
      calc
      (Real.sqrt (∫ w, OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ) ^ 2 ∂G.P)) ^ 2 =
          ∫ w, OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ) ^ 2 ∂G.P :=
        Real.sq_sqrt hJ
      _ ≤ Kstar ^ 2 * ∫ x, (φ : Euc p.d → ℝ) x ^ 2 ∂μstar := hbound
      _ = (Kstar * Real.sqrt (∫ x, (φ : Euc p.d → ℝ) x ^ 2 ∂μstar)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hI]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hKstar (Real.sqrt_nonneg _))).1 hsq
  have hevalEq : ∀ φ ψ : testSub, testLp φ = testLp ψ → evalLp φ = evalLp ψ := by
    intro φ ψ hφψ
    have hsub : testLp (φ - ψ) = 0 := by rw [map_sub, hφψ, sub_self]
    have hle := hevalBound (φ - ψ)
    rw [hsub] at hle
    have hz : evalLp (φ - ψ) = 0 := by
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa using hle) (norm_nonneg _)
    have hdiff : evalLp φ - evalLp ψ = 0 := by
      simpa [map_sub] using hz
    exact sub_eq_zero.mp hdiff
  let testRange : Submodule ℝ (Lp ℝ 2 μstar) := LinearMap.range testLp
  let rep : testRange → testSub := fun x => Classical.choose x.2
  have rep_spec (x : testRange) : testLp (rep x) = (x : Lp ℝ 2 μstar) :=
    Classical.choose_spec x.2
  let J0 : testRange →ₗ[ℝ] Lp ℝ 2 G.P := {
    toFun := fun x => evalLp (rep x)
    map_add' := by
      intro x y
      have hrep : testLp (rep (x + y)) = testLp (rep x + rep y) := by
        calc
          testLp (rep (x + y)) = ((x + y : testRange) : Lp ℝ 2 μstar) := rep_spec (x + y)
          _ = (x : Lp ℝ 2 μstar) + (y : Lp ℝ 2 μstar) := rfl
          _ = testLp (rep x + rep y) := by rw [testLp.map_add, rep_spec x, rep_spec y]
      calc
        _ = evalLp (rep x + rep y) := hevalEq _ _ hrep
        _ = evalLp (rep x) + evalLp (rep y) := evalLp.map_add _ _
    map_smul' := by
      intro c x
      have hrep : testLp (rep (c • x)) = testLp (c • rep x) := by
        calc
          testLp (rep (c • x)) = ((c • x : testRange) : Lp ℝ 2 μstar) := rep_spec (c • x)
          _ = c • (x : Lp ℝ 2 μstar) := rfl
          _ = testLp (c • rep x) := by rw [testLp.map_smul, rep_spec x]
      calc
        _ = evalLp (c • rep x) := hevalEq _ _ hrep
        _ = c • evalLp (rep x) := evalLp.map_smul _ _
  }
  have hJbound : ∀ x : testRange, ‖J0 x‖ ≤ Kstar * ‖(x : Lp ℝ 2 μstar)‖ := by
    intro x
    rw [show J0 x = evalLp (rep x) by rfl, ← rep_spec x]
    exact hevalBound (rep x)
  let J : testRange →L[ℝ] Lp ℝ 2 G.P :=
    LinearMap.mkContinuous J0 Kstar hJbound
  let e : testRange →L[ℝ] Lp ℝ 2 μstar :=
    LinearMap.mkContinuous testRange.subtype 1 (fun x => by simp)
  have heNorm : ∀ x : testRange, ‖e x‖ = ‖(x : Lp ℝ 2 μstar)‖ := fun _ => rfl
  have heUniform : IsUniformInducing e :=
    (AddMonoidHomClass.isometry_of_norm e heNorm).isUniformInducing
  have hdenseTest : DenseRange testLp := fp81s21_gaussLin_test_dense p R
    (by simpa [testSub, μstar] using htest)
  have hrange : Set.range testLp = Set.range e := by
    ext y
    constructor
    · rintro ⟨φ, rfl⟩
      exact ⟨⟨testLp φ, ⟨φ, rfl⟩⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      rcases x with ⟨x, hx⟩
      rcases hx with ⟨φ, rfl⟩
      exact ⟨φ, rfl⟩
  have hdense : DenseRange e := by
    rw [DenseRange, ← hrange]
    exact hdenseTest
  let L : Lp ℝ 2 μstar →L[ℝ] Lp ℝ 2 G.P := ContinuousLinearMap.extend J e
  have hLbound : ‖L‖ ≤ Kstar := by
    have hJnorm : ‖J‖ ≤ Kstar := LinearMap.mkContinuous_norm_le J0 hKstar hJbound
    have hN := ContinuousLinearMap.opNorm_extend_le J hdense (N := (1 : ℝ≥0))
      (fun x => by rw [heNorm]; simpa using hJbound x)
    exact hN.trans (by simpa using hJnorm)
  have hAgreeLp : ∀ φ : testSub, L (testLp φ) = evalLp φ := by
    intro φ
    let x : testRange := ⟨testLp φ, ⟨φ, rfl⟩⟩
    have hx : e x = testLp φ := rfl
    rw [← hx, ContinuousLinearMap.extend_eq (h_dense := hdense) (h_e := heUniform)]
    have hrep : testLp (rep x) = testLp φ := by rw [rep_spec x]
    exact hevalEq _ _ hrep
  have hevalMeas : ∀ φ : testSub,
      Measurable (fun w => OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ)) := by
    intro φ
    have heq : (fun w => OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ)) =
        fun w => HRS.MS.ProClosureS111.gaussianOscEval φ (G.Z u w) := by
      funext w
      exact (HRS.MS.ProClosureS111.gaussianOscEval_apply φ _).symm
    rw [heq]
    exact (HRS.MS.ProClosureS111.gaussianOscEval φ).continuous.measurable.comp
      ((G.evolution (u + 1)).meas u)
  have hLaw : ∀ φ : testSub,
      ∃ v : ℝ≥0,
        G.P.map (fun w => OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ)) = gaussianReal 0 v := by
    intro φ
    exact hgauss δ hδ hδgR R G u hu (φ : Euc p.d → ℝ) φ.2
  let oneMem : MemLp (fun _ : G.Ω => (1 : ℝ)) 2 G.P := memLp_const 1
  let oneLp : Lp ℝ 2 G.P := oneMem.toLp _
  let mean : Lp ℝ 2 G.P →L[ℝ] ℝ := innerSL ℝ oneLp
  have hmeanEq : ∀ f : Lp ℝ 2 G.P,
      mean f = ∫ w, (f : G.Ω → ℝ) w ∂G.P := by
    intro f
    change inner ℝ oneLp f = _
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [oneMem.coeFn_toLp] with w hw
    change (f : G.Ω → ℝ) w * (oneMem.toLp _ w) = (f : G.Ω → ℝ) w
    rw [hw]
    ring
  have hmeanEval : ∀ φ : testSub, mean (evalLp φ) = 0 := by
    intro φ
    obtain ⟨v, hlaw⟩ := hLaw φ
    rw [hmeanEq]
    calc
      ∫ w, (evalLp φ) w ∂G.P =
          ∫ w, OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ) ∂G.P := by
            exact integral_congr_ae (evalMem φ).coeFn_toLp
      _ =
          ∫ x, x ∂(G.P.map (fun w => OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ)) : Measure ℝ) := by
            symm
            exact integral_map ((hevalMeas φ).aemeasurable) (by fun_prop)
      _ = ∫ x, x ∂(gaussianReal 0 v) := by rw [hlaw]
      _ = 0 := integral_id_gaussianReal
  have hmeanOnRange : ∀ x : testRange, mean (J x) = 0 := by
    intro x
    rw [show J x = J0 x by rfl, show J0 x = evalLp (rep x) by rfl]
    exact hmeanEval (rep x)
  have hmeanExtend : mean.comp L = 0 := by
    have hcomp : (⇑(mean.comp L) ∘ ⇑e) =
        (⇑(0 : Lp ℝ 2 μstar →L[ℝ] ℝ) ∘ ⇑e) := by
      funext x
      change mean (L (e x)) = 0
      rw [ContinuousLinearMap.extend_eq
        (h_dense := hdense) (h_e := heUniform)]
      exact hmeanOnRange x
    apply ContinuousLinearMap.ext
    intro f
    exact congrFun (DenseRange.equalizer hdense (mean.comp L).continuous
      (0 : Lp ℝ 2 μstar →L[ℝ] ℝ).continuous hcomp) f
  have hAgree : ∀ φ : testSub,
      L (testLp φ) =ᵐ[G.P] (fun w => OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ)) := by
    intro φ
    have hLp : L (testLp φ) = evalLp φ := hAgreeLp φ
    have hcoe : (L (testLp φ) : G.Ω → ℝ) = (evalLp φ : G.Ω → ℝ) :=
      congrArg (fun z : Lp ℝ 2 G.P => (z : G.Ω → ℝ)) hLp
    have hEvalCoe : (evalLp φ : G.Ω → ℝ) =ᵐ[G.P]
        (fun w => OscDual.eval (G.Z u w) (φ : Euc p.d → ℝ)) := by
      simpa [evalLp] using (evalMem φ).coeFn_toLp
    filter_upwards [hEvalCoe] with w hw
    rw [congrFun hcoe w, hw]
  refine ⟨L, hLbound, ?_, ?_, ?_⟩
  · intro φ hφ hφmem
    let φ' : testSub := ⟨φ, hφ⟩
    have hsrc : testLp φ' = hφmem.toLp φ := by
      apply Lp.ext
      exact (htest φ' φ'.2).coeFn_toLp.trans hφmem.coeFn_toLp.symm
    simpa [φ', hsrc] using hAgree φ'
  · intro f
    calc
      ∫ w, (L f) w ∂G.P = mean (L f) := (hmeanEq (L f)).symm
      _ = 0 := by
        have hf := congrArg (fun T : Lp ℝ 2 μstar →L[ℝ] ℝ => T f) hmeanExtend
        simpa using hf
  · intro L' hL'
    apply ContinuousLinearMap.ext
    intro f
    have hEq : ∀ φ : testSub, L' (testLp φ) = L (testLp φ) := by
      intro φ
      apply Lp.ext
      filter_upwards [hL' (φ : Euc p.d → ℝ) φ.2 (htest φ φ.2), hAgree φ] with w h₁ h₂
      exact h₁.trans h₂.symm
    have hcomp : (L' : Lp ℝ 2 μstar → Lp ℝ 2 G.P) ∘ testLp =
        (L : Lp ℝ 2 μstar → Lp ℝ 2 G.P) ∘ testLp := funext hEq
    have hfun := DenseRange.equalizer hdenseTest L'.continuous L.continuous hcomp
    exact congrFun hfun f

#print axioms fp81s21_gaussLin_test_dense
#print axioms fp81s21_gaussLin_extension

end HRS.Fp81.S21

end
