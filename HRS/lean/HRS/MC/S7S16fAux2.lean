import HRS.MC.Sec7Vocab

/-!
# Packet `slow_correction` (S16f), part 2: full support of a nondegenerate (diagonal) Gaussian on `R^n`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.MC.Sec7.S16f

theorem s16f_gaussianReal_openPos : (gaussianReal 0 1).IsOpenPosMeasure := by
  refine ⟨fun U hU hne h0 => ?_⟩
  have hac : (volume : Measure ℝ) ≪ gaussianReal 0 1 := gaussianReal_absolutelyContinuous' 0 one_ne_zero
  have := hac h0
  exact (hU.measure_pos volume hne).ne' this

theorem s16f_stdGaussian_openPos {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : Set (EuclideanSpace ℝ ι)) (hV : IsOpen V) (hne : V.Nonempty) :
    0 < stdGaussian (EuclideanSpace ℝ ι) V := by
  haveI := s16f_gaussianReal_openPos
  rw [← map_pi_eq_stdGaussian, Measure.map_apply (by fun_prop) hV.measurableSet]
  have hopen : IsOpen ((WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) ⁻¹' V) :=
    hV.preimage (PiLp.continuous_toLp 2 _)
  obtain ⟨v, hv⟩ := hne
  refine hopen.measure_pos _ ⟨WithLp.ofLp v, ?_⟩
  simpa using hv

theorem s16f_gauss_openPos {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (U : Set (EuclideanSpace ℝ ι)) (hU : IsOpen U) (hne : U.Nonempty) :
    0 < multivariateGaussian 0 (Matrix.diagonal c) U := by
  set S : Matrix ι ι ℝ := Matrix.diagonal c with hS
  have hpd : S.PosDef := Matrix.posDef_diagonal_iff.2 hc
  set T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) with hT
  have hTT : ∀ y, T (T y) = Matrix.toEuclideanCLM (𝕜 := ℝ) S y := by
    intro y
    have := CFC.sqrt_mul_sqrt_self S hpd.posSemidef.nonneg
    conv_rhs => rw [← this]
    rw [map_mul]
    rfl
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : Matrix.toEuclideanCLM (𝕜 := ℝ) S y = 0 := by rw [← hTT, hy]; simp
    have h2 : S.mulVec (WithLp.ofLp y) = 0 := by
      have := Matrix.toEuclideanCLM_toLp (𝕜 := ℝ) S (WithLp.ofLp y)
      rw [WithLp.toLp_ofLp] at this
      rw [h1] at this
      have h3 := congrArg WithLp.ofLp this
      simpa using h3.symm
    rw [hS] at h2
    ext i
    have := congrFun h2 i
    simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hc i).ne'
    · simpa using h
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective (f := (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))).1 hinj
  unfold multivariateGaussian
  rw [Measure.map_apply (by fun_prop) hU.measurableSet]
  refine s16f_stdGaussian_openPos _ (hU.preimage (by fun_prop)) ?_
  obtain ⟨u, hu⟩ := hne
  obtain ⟨y, hy⟩ := hsurj u
  refine ⟨y, ?_⟩
  show 0 + T y ∈ U
  have hy' : T y = u := hy
  rw [hy', zero_add]
  exact hu

end HRS.MC.Sec7.S16f

end
