import HRS.MS.Fp81S21MovingFuture2
import HRS.MS.R2InterpAux2
import HRS.MS.R2InterpAux5
import HRS.MS.S111BDAux4
import HRS.MS.S21K2_P07A

/-!
# S2.1(iii), SOL39 packet 3: identify the path law as an R2 future Gaussian

Finite observation laws imply centered Gaussianity on the full continuous-path
space by the existing projection and a.e.-limit argument. Two-time feature
Gram matrices identify the genuine covariance on arbitrary oscillator tests.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.S111T
open HRS.MS.S111X1
open HRS.MS.ProClosureS111

theorem fp81s21_movingFuture_pathLaw_isR2
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) H)
    (γ : Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hγ : IsProbabilityMeasure γ)
    (hLaw : ∀ n : ℕ, ∀ ts : Fin n → ℝ,
      ∀ φ : Fin n → oscSub p.d (wholeSpaceIndex p.d : ℝ),
      ∀ hts : (∀ j, ts j ∈ Set.Icc (0 : ℝ) H),
      γ.map (fun z => (WithLp.toLp 2 fun j =>
        OscDual.eval (OscPath.at' z ⟨ts j, hts j⟩)
          (φ j : Euc p.d → ℝ) : EuclideanSpace ℝ (Fin n))) =
        multivariateGaussian 0 (Matrix.of fun j k =>
          inner ℝ
            (movingNoiseFeature R u (ts j) (φ j : Euc p.d → ℝ))
            (movingNoiseFeature R u (ts k) (φ k : Euc p.d → ℝ)))) :
    IsR2FutureGaussian (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H u γ := by
  letI : IsProbabilityMeasure γ := hγ
  have hobs : ∀ (n : ℕ) (τ : Fin n → Set.Icc (0 : ℝ) H)
      (α : Fin n → MultiIndex p.d),
      HRS.IsCenteredGaussian
        (γ.map (HRS.MS.R2Interp.s102_obs (m := (wholeSpaceIndex p.d : ℝ)) τ α)) := by
    intro n τ α
    let ts : Fin n → ℝ := fun j => (τ j : ℝ)
    let φ : Fin n → oscSub p.d (wholeSpaceIndex p.d : ℝ) :=
      fun j => initialTestBasis (wholeSpaceIndex p.d : ℝ) (α j)
    have hts : ∀ j, ts j ∈ Set.Icc (0 : ℝ) H := fun j => (τ j).property
    have hlaw := hLaw n ts φ hts
    have hfun : (fun z => (WithLp.toLp 2 fun j =>
        OscDual.eval (OscPath.at' z ⟨ts j, hts j⟩)
          (φ j : Euc p.d → ℝ) : EuclideanSpace ℝ (Fin n))) =
        HRS.MS.R2Interp.s102_obs (m := (wholeSpaceIndex p.d : ℝ)) τ α := by
      funext z
      ext j
      simp [HRS.MS.R2Interp.s102_obs_apply, ts, φ, initialTestBasis,
        OscDual.eval_oscTestFun]
    have hmap : γ.map (HRS.MS.R2Interp.s102_obs
        (m := (wholeSpaceIndex p.d : ℝ)) τ α) =
        multivariateGaussian 0 (Matrix.of fun j k =>
          inner ℝ
            (movingNoiseFeature R u (τ j : ℝ)
              (oscTestFun (wholeSpaceIndex p.d : ℝ) (α j)))
            (movingNoiseFeature R u (τ k : ℝ)
              (oscTestFun (wholeSpaceIndex p.d : ℝ) (α k)))) := by
      rw [← hfun]
      simpa [ts, φ, initialTestBasis] using hlaw
    rw [hmap]
    exact HRS.MS.S111BD.s111_isCenteredGaussian_mvg n _
  have hproj := HRS.MS.S111BD.s111_projection_gaussian
    p.d (wholeSpaceIndex p.d : ℝ) H hH γ hobs
  have hcenter := HRS.MS.S111BD.s111_centered_gaussian_ae_limit γ
    (fun L => HRS.MS.R2Interp.s102_Pj
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) H hH L)
    id
    (fun L => (HRS.MS.R2Interp.s102_Pj
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) H hH L).continuous.measurable.aemeasurable)
    measurable_id.aemeasurable hproj
    (Filter.Eventually.of_forall fun z =>
      (HRS.MS.R2Interp.s102_projection_strong
        (wholeSpaceIndex p.d : ℝ) H hH).2.1 z)
  have hcenter' : HRS.IsCenteredGaussian γ := by
    simpa using hcenter
  refine ⟨hcenter', ?_⟩
  intro ta tb φa φb hφa hφb hta htb
  let ts : Fin 2 → ℝ := fun i => if i = 0 then ta else tb
  let tests : Fin 2 → oscSub p.d (wholeSpaceIndex p.d : ℝ) := fun i =>
    if i = 0 then ⟨φa, hφa⟩ else ⟨φb, hφb⟩
  have hts : ∀ i, ts i ∈ Set.Icc (0 : ℝ) H := by
    intro i
    fin_cases i <;> simp [ts, hta, htb]
  let v : Fin 2 → MovingNoiseHilbert p.d := fun i =>
    movingNoiseFeature R u (ts i) (tests i : Euc p.d → ℝ)
  have hmat : (Matrix.of fun i j =>
      inner ℝ
        (movingNoiseFeature R u (ts i) (tests i : Euc p.d → ℝ))
        (movingNoiseFeature R u (ts j) (tests j : Euc p.d → ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) = Matrix.gram ℝ v := by
    ext i j
    simp [v, Matrix.gram]
  have hpsd : (Matrix.gram ℝ v).PosSemidef := Matrix.posSemidef_gram ℝ v
  let V : OscPath p.d (wholeSpaceIndex p.d : ℝ) H → EuclideanSpace ℝ (Fin 2) :=
    fun z => (WithLp.toLp 2 fun j =>
      OscDual.eval (OscPath.at' z ⟨ts j, hts j⟩)
        (tests j : Euc p.d → ℝ) : EuclideanSpace ℝ (Fin 2))
  have hVmeas : Measurable V := by
    dsimp [V]
    refine (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp
      (measurable_pi_iff.2 fun j => ?_)
    have heval : (fun z : OscPath p.d (wholeSpaceIndex p.d : ℝ) H =>
        OscDual.eval (OscPath.at' z ⟨ts j, hts j⟩)
          (tests j : Euc p.d → ℝ)) =
        fun z => gaussianOscEval (tests j) (OscPath.at' z ⟨ts j, hts j⟩) :=
      funext fun z => (gaussianOscEval_apply (tests j) _).symm
    rw [heval]
    have hEval : Measurable (fun z : OscPath p.d (wholeSpaceIndex p.d : ℝ) H =>
        OscPath.at' z ⟨ts j, hts j⟩) := by
      change Measurable
        (fun z : C(Set.Icc (0 : ℝ) H, OscDual p.d (wholeSpaceIndex p.d : ℝ)) =>
          z ⟨ts j, hts j⟩)
      exact ContinuousMap.measurable_eval (⟨ts j, hts j⟩ : Set.Icc (0 : ℝ) H)
    exact (gaussianOscEval (tests j)).continuous.measurable.comp hEval
  have hlaw₂ := hLaw 2 ts tests hts
  have hVlaw : γ.map V = multivariateGaussian 0 (Matrix.gram ℝ v) := by
    simpa only [hmat] using hlaw₂
  have hprod : Integrable
      (fun x : EuclideanSpace ℝ (Fin 2) => x 0 * x 1)
      (multivariateGaussian 0 (Matrix.gram ℝ v)) := by
    exact HRS.MC.Sec7.S7PIS3.S7PIS3_coord_mul_integrable
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) 0 1
  have hprodMap : Integrable (fun x : EuclideanSpace ℝ (Fin 2) => x 0 * x 1)
      (γ.map V) := by
    rw [hVlaw]
    exact hprod
  have hmapInt :
      ∫ z, V z 0 * V z 1 ∂γ =
        ∫ x, x 0 * x 1 ∂(multivariateGaussian 0 (Matrix.gram ℝ v)) := by
    rw [← hVlaw, integral_map hVmeas.aemeasurable hprodMap.aestronglyMeasurable]
  have hsecond :
      ∫ x, x 0 * x 1 ∂(multivariateGaussian 0 (Matrix.gram ℝ v)) =
        (Matrix.gram ℝ v) 0 1 :=
    HRS.MS.R26T3.s21k2_p07_second hpsd 0 1
  have hV0 : ∀ z, V z 0 = OscDual.eval (r2PathAt z ta) φa := by
    intro z
    rw [HRS.MS.R2Interp.s102_r2PathAt_of_mem z hta]
    simp [V, ts, tests]
  have hV1 : ∀ z, V z 1 = OscDual.eval (r2PathAt z tb) φb := by
    intro z
    rw [HRS.MS.R2Interp.s102_r2PathAt_of_mem z htb]
    simp [V, ts, tests]
  have hpathMoment :
      ∫ z, OscDual.eval (r2PathAt z ta) φa *
        OscDual.eval (r2PathAt z tb) φb ∂γ =
      inner ℝ (movingNoiseFeature R u ta φa) (movingNoiseFeature R u tb φb) := by
    calc
      _ = ∫ z, V z 0 * V z 1 ∂γ := by
        apply integral_congr_ae
        filter_upwards with z
        rw [hV0 z, hV1 z]
      _ = ∫ x, x 0 * x 1 ∂(multivariateGaussian 0 (Matrix.gram ℝ v)) := hmapInt
      _ = inner ℝ (movingNoiseFeature R u ta φa) (movingNoiseFeature R u tb φb) := by
        rw [hsecond]
        simp [Matrix.gram_apply, v, ts, tests]
  have hfeature := (movingNoiseFeature_spec p R hδ hδhalf hH).2
    u hu ta hta tb htb φa φb hφa hφb
  have hnu : (r26t3_coeff R).ν = p.β⁻¹ := rfl
  have hrho : (r26t3_coeff R).ρ = R.ρ := rfl
  refine hpathMoment.trans ?_
  rw [hnu, hrho]
  simpa only [r26t3_U] using hfeature

#print axioms fp81s21_movingFuture_pathLaw_isR2

end HRS.Fp81.S21

end
