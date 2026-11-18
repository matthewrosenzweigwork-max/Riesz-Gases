import HRS.MS.GenPathAux45
import HRS.Main.GFB4Aux4

/-!
# S5.6 packet P8e: finite-dimensional laws of the Gaussian `𝒦`-martingale pairings
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MS.S52 HRS.MP.RdRem HRS.Uniform.Q54c HRS.GF

variable {d : ℕ}

theorem s56_isum_const {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (G : ℝ → H) (y : H)
    {T t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (N : ℕ) :
    isum G (fun _ => y) T t N = inner ℝ (G t - G 0) y := by
  unfold isum
  have h1 : ∀ i ∈ Finset.range (N + 1), inner ℝ (G (min (gridPt T N (i + 1)) t) - G (min (gridPt T N i) t)) y =
      inner ℝ (G (min (gridPt T N (i + 1)) t)) y - inner ℝ (G (min (gridPt T N i) t)) y :=
    fun i _ => inner_sub_left _ _ _
  rw [Finset.sum_congr rfl h1, Finset.sum_range_sub (fun i => inner ℝ (G (min (gridPt T N i) t)) y) (N + 1)]
  rw [gridPt_last, gridPt_zero, min_eq_right ht.2, min_eq_left ht.1, inner_sub_left]

theorem s56_Gb_fdd (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) b.T, IsFiniteMeasure (HRS.Whole.withDensityReal (S.ρ N r)))
    (q : ℝ) (hq : 0 ≤ q) {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → KSpace d b.m b.T}
    (hG : IsHilbertMartingaleWithCovariation P ℱ b.T G (fun r _ => s56Db b S N hOM hS q hq r))
    (hGc : ∀ ζ, Continuous fun s => G s ζ) (hGz : ∀ ζ, G 0 ζ = 0)
    (hGm : ∀ t, Measurable (G t)) {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) b.T)
    (αs : Fin p → MultiIndex d) :
    P.map (fun ζ => (WithLp.toLp 2 fun a => inner ℝ (G (ts a) ζ) (s52y1 b.m b.T (ts a) (αs a)) :
        EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun a c => noiseCovW (S.coeff N) q (ts a) (ts c)
        (oscTestFun b.m (αs a)) (oscTestFun b.m (αs c))) := by
  have hT0 : 0 < b.T := hbv.hT
  set ys : Fin p → ℝ → KSpace d b.m b.T := fun a _ => s52y1 b.m b.T (ts a) (αs a) with hys
  set B : ℝ := ∑ a, ‖s52y1 b.m b.T (ts a) (αs a)‖ with hB
  have hXm : Measurable fun ζ => (WithLp.toLp 2 fun a => inner ℝ (G (ts a) ζ) (s52y1 b.m b.T (ts a) (αs a)) :
      EuclideanSpace ℝ (Fin p)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => (hGm _).inner measurable_const)
  have h := gfb4_vec_gaussian hG hGc hGz hT0 ts hts ys (B := B)
    (fun a σ _ => by
      show ‖s52y1 b.m b.T (ts a) (αs a)‖ ≤ B
      exact Finset.single_le_sum (f := fun a => ‖s52y1 b.m b.T (ts a) (αs a)‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ a))
    (fun a x => (continuousOn_const : ContinuousOn (fun _ : ℝ => inner ℝ (s52y1 b.m b.T (ts a) (αs a)) x)
      (Set.Icc 0 (ts a)))) _ hXm
    (fun a => by
      have : ∀ N' ζ, ‖(WithLp.toLp 2 fun a => inner ℝ (G (ts a) ζ) (s52y1 b.m b.T (ts a) (αs a)) :
          EuclideanSpace ℝ (Fin p)) a - isum (fun σ => G σ ζ) (ys a) b.T (ts a) N'‖ₑ ^ 2 = 0 := by
        intro N' ζ
        have e := s56_isum_const (fun σ => G σ ζ) (s52y1 b.m b.T (ts a) (αs a)) (hts a) N'
        have e2 : isum (fun σ => G σ ζ) (ys a) b.T (ts a) N' = inner ℝ (G (ts a) ζ) (s52y1 b.m b.T (ts a) (αs a)) := by
          rw [show ys a = fun _ => s52y1 b.m b.T (ts a) (αs a) from rfl, e, hGz]; simp
        rw [e2]
        simp
      simp_rw [this]
      simp)
  rw [h]
  congr 1
  ext a c
  simp only [Matrix.of_apply]
  exact s56_noiseCov_eq b hbv S N hC hOM hS q hq (hts a) (hts c) (αs a) (αs c)

end HRS.MS.GenPath
