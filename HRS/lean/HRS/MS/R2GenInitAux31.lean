import HRS.MS.R2GenInitAux30

/-!
# S10.5 window comparison, packet D2: finite-dimensional laws of the window Gaussian martingale
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.MH.DualityRd HRS.Uniform.Q54c HRS.GF

variable {d : ℕ}

theorem s105_Gb_fdd {s a β T b : ℝ} {ρ : Euc d → ℝ} (hS : S105Stat d s a β T b ρ) (hb : 0 ≤ b) (hT : 0 < T)
    (q : ℝ) (hq : 0 ≤ q) [IsFiniteMeasure (HRS.Whole.withDensityReal ρ)]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T}
    (hG : IsHilbertMartingaleWithCovariation P ℱ (b + T) G (fun r _ =>
      s105Db _ hS.hF (HRS.Whole.withDensityReal ρ) q hq r))
    (hGc : ∀ ζ, Continuous fun t => G t ζ) (hGz : ∀ ζ, G 0 ζ = 0) (hGm : ∀ t, Measurable (G t))
    {p : ℕ} (us : Fin p → ℝ) (hus : ∀ a, us a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d) :
    P.map (fun ζ => (WithLp.toLp 2 fun a => inner ℝ (G (b + us a) ζ)
        (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)) : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun i j => noiseCovW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) q
        (b + us i) (b + us j) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i))
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j))) := by
  have hτ : 0 < b + T := by linarith
  have hts : ∀ a, b + us a ∈ Set.Icc (0 : ℝ) (b + T) := fun a =>
    ⟨by linarith [(hus a).1], by linarith [(hus a).2]⟩
  set ys : Fin p → ℝ → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T := fun a _ =>
    s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a) with hys
  set B : ℝ := ∑ a, ‖s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)‖ with hB
  have hXm : Measurable fun ζ => (WithLp.toLp 2 fun a => inner ℝ (G (b + us a) ζ)
      (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)) : EuclideanSpace ℝ (Fin p)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => (hGm _).inner measurable_const)
  have h := gfb4_vec_gaussian hG hGc hGz hτ (fun a => b + us a) hts ys (B := B)
    (fun a σ _ => by
      show ‖s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)‖ ≤ B
      exact Finset.single_le_sum (f := fun a => ‖s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ a))
    (fun a x => (continuousOn_const : ContinuousOn (fun _ : ℝ =>
      inner ℝ (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)) x) (Set.Icc 0 (b + us a)))) _ hXm
    (fun a => by
      have : ∀ N' ζ, ‖(WithLp.toLp 2 fun a => inner ℝ (G (b + us a) ζ)
          (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)) : EuclideanSpace ℝ (Fin p)) a -
          isum (fun σ => G σ ζ) (ys a) (b + T) (b + us a) N'‖ₑ ^ 2 = 0 := by
        intro N' ζ
        have e := s56_isum_const (fun σ => G σ ζ) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)) (hts a) N'
        have e2 : isum (fun σ => G σ ζ) (ys a) (b + T) (b + us a) N' =
            inner ℝ (G (b + us a) ζ) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)) := by
          rw [show ys a = fun _ => s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a) from rfl, e, hGz]; simp
        rw [e2]
        simp
      simp_rw [this]
      simp)
  rw [h]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  have := s105_noiseCov_eq hS hb q hq (hus i) (hus j) (αs i) (αs j)
  simpa [min_def, ys] using this

end HRS.MS.R2GenInit
