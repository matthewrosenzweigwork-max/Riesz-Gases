import HRS.MS.Fp81S21MovingFuture
import HRS.MS.S111TermAux7
import HRS.MS.R2InterpAux13

/-!
# S2.1(iii), SOL39 packet 3: the continuous future path marginal

For each fixed admissible `(H,u)`, the generic linear-feature constructor gives
a continuous path pair. We retain its first marginal. The exported
finite-dimensional law is stated on every oscillator test in `oscSub`, and
its covariance is identified with the physical moving-noise feature Gram form.
This is a family of marginal laws; it does not claim a common field or any
adapted coupling as `u` varies.
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

theorem fp81s21_movingFuture_pathLaw (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ H : ℝ, 0 < H → ∀ u ∈ Set.Icc (0 : ℝ) H,
          ∃ γ : Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
            IsProbabilityMeasure γ ∧
            (∀ n : ℕ, ∀ ts : Fin n → ℝ,
              ∀ φ : Fin n → oscSub p.d (wholeSpaceIndex p.d : ℝ),
              ∀ hts : (∀ j, ts j ∈ Set.Icc (0 : ℝ) H),
              γ.map (fun z => (WithLp.toLp 2 fun j =>
                OscDual.eval (OscPath.at' z ⟨ts j, hts j⟩)
                  (φ j : Euc p.d → ℝ) : EuclideanSpace ℝ (Fin n))) =
                multivariateGaussian 0 (Matrix.of fun j k =>
                  inner ℝ
                    (movingNoiseFeature R u (ts j) (φ j : Euc p.d → ℝ))
                    (movingNoiseFeature R u (ts k) (φ k : Euc p.d → ℝ)))) := by
  obtain ⟨δ0, hδ0, hδ0half, hinputs⟩ :=
    fp81s21_movingFuture_constructor_inputs p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R H hH u hu
  obtain ⟨G, hG, hF, hLdata, hGram⟩ := hinputs δ hδ hδle R H hH u hu
  obtain ⟨L, hL, hinc⟩ := hLdata
  obtain ⟨P, hP, hPaths⟩ :=
    gaussian_paths_of_linear_features p.d (wholeSpaceIndex p.d : ℝ) H hH
      gaussianFeatureBasis G hG hF L hL hinc
  letI : IsProbabilityMeasure P := hP
  let γ : Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) := P.map Prod.fst
  have hγprob : IsProbabilityMeasure γ := by
    refine ⟨?_⟩
    dsimp [γ]
    simp [Measure.map_apply_of_aemeasurable
      measurable_fst.aemeasurable MeasurableSet.univ]
  refine ⟨γ, hγprob, ?_⟩
  intro n ts φ hts
  let O : OscPath p.d (wholeSpaceIndex p.d : ℝ) H → EuclideanSpace ℝ (Fin n) :=
    fun z => (WithLp.toLp 2 fun j =>
      OscDual.eval (OscPath.at' z ⟨ts j, hts j⟩)
        (φ j : Euc p.d → ℝ) : EuclideanSpace ℝ (Fin n))
  let OP : PathPair p.d (wholeSpaceIndex p.d : ℝ) H → EuclideanSpace ℝ (Fin n) :=
    fun w => (WithLp.toLp 2 fun j =>
      OscDual.eval (pairedProcess p.d (wholeSpaceIndex p.d : ℝ) H hH.le
        (0 : Fin 2) (ts j) w) (φ j : Euc p.d → ℝ) : EuclideanSpace ℝ (Fin n))
  have hOmeas : Measurable O := by
    dsimp [O]
    refine (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
      (measurable_pi_iff.2 fun j => ?_)
    have heval : (fun z : OscPath p.d (wholeSpaceIndex p.d : ℝ) H =>
        OscDual.eval (OscPath.at' z ⟨ts j, hts j⟩)
          (φ j : Euc p.d → ℝ)) =
        fun z => gaussianOscEval (φ j) (OscPath.at' z ⟨ts j, hts j⟩) :=
      funext fun z => (gaussianOscEval_apply (φ j) _).symm
    rw [heval]
    have hEval : Measurable (fun z : OscPath p.d (wholeSpaceIndex p.d : ℝ) H =>
        OscPath.at' z ⟨ts j, hts j⟩) := by
      change Measurable (fun z : C(Set.Icc (0 : ℝ) H, OscDual p.d (wholeSpaceIndex p.d : ℝ)) =>
        z ⟨ts j, hts j⟩)
      exact ContinuousMap.measurable_eval
        (⟨ts j, hts j⟩ : Set.Icc (0 : ℝ) H)
    exact (gaussianOscEval (φ j)).continuous.measurable.comp
      hEval
  have hclip : ∀ j, clippedTime H hH.le (ts j) = ⟨ts j, hts j⟩ := by
    intro j
    apply Subtype.ext
    exact s111t_clip_of_mem (hts j)
  have hcomp : ∀ w : PathPair p.d (wholeSpaceIndex p.d : ℝ) H,
      O w.1 = OP w := by
    intro w
    ext j
    simp [O, OP, pairedProcess, hclip j]
  have hmap : γ.map O = P.map OP := by
    dsimp [γ]
    rw [Measure.map_map hOmeas measurable_fst]
    congr 1
    funext w
    exact hcomp w
  have hlaw := hPaths n (fun _ : Fin n => (0 : Fin 2)) ts φ hts
  have hmat : (Matrix.of fun j k =>
      inner ℝ (G 0 (ts j) (φ j)) (G 0 (ts k) (φ k)) :
        Matrix (Fin n) (Fin n) ℝ) =
      Matrix.of fun j k =>
        inner ℝ
          (movingNoiseFeature R u (ts j) (φ j : Euc p.d → ℝ))
          (movingNoiseFeature R u (ts k) (φ k : Euc p.d → ℝ)) := by
    ext j k
    exact hGram 0 0 (ts j) (ts k) (hts j) (hts k) (φ j) (φ k)
  calc
    γ.map O = P.map OP := hmap
    _ = multivariateGaussian 0
        (Matrix.of fun j k => inner ℝ (G 0 (ts j) (φ j)) (G 0 (ts k) (φ k))) := hlaw
    _ = multivariateGaussian 0
        (Matrix.of fun j k =>
          inner ℝ
            (movingNoiseFeature R u (ts j) (φ j : Euc p.d → ℝ))
            (movingNoiseFeature R u (ts k) (φ k : Euc p.d → ℝ))) := by rw [hmat]

#print axioms fp81s21_movingFuture_pathLaw

end HRS.Fp81.S21

end
