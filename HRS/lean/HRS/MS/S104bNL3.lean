import HRS.MS.S104bNL2
import HRS.MS.R2GenInitAux39

/-!
# S10.5 (nonlinear), packet S104b-NL3: the initial-path discrepancy is the coupling cost `r2InitCouplingPath` (moving reference)

Moving analogue of `s105_eps_path` (R2GenInitAux39): the initial state `k₀` and the centring use the density `ρ 0`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S104b

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.Uniform.Q54c HRS.MS.R2GenInit HRS.MS.S21m

variable {d : ℕ}

theorem s104b_eps_path {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) (hb : 0 ≤ b) (hT : 0 < T)
    {N : ℕ} (hN : 1 ≤ N) (s' : ℕ → Set.Icc (0 : ℝ) T) (hs' : DenseRange s')
    (g : (ℕ × MultiIndex d → ℝ) → OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T) (x : EucConfig d N)
    (η : (Euc d → ℝ) → ℝ) (c : ℕ × MultiIndex d → ℝ)
    (hcη : ∀ i : ℕ × MultiIndex d, c i = η (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0
      (b + s' i.1) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) i.2)))
    (hmemℓ : ∀ n : ℕ, Memℓp (fun α => c (n, α)) 2)
    (hgc : s56PathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s' (g c) = c)
    (hm : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ))
    (hcont : Continuous fun u : Set.Icc (0 : ℝ) T => (ellVec (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) fun α =>
      Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW ((quadraticGradientDyn d s a β).coeff
        ρ) 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) -
        HRS.Whole.pair (HRS.Whole.withDensityReal (ρ 0)) (propagatorW ((quadraticGradientDyn d s a β).coeff
        ρ) 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) -
        η (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (b + u)
          (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)))) :
    s56EvalPath hT.le (s105k0 (fun (a' : Fin d) (z : Euc d) => r2WindowFeature
      ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b 0 z)
      (Real.sqrt N) (HRS.Whole.empirical x) (HRS.Whole.withDensityReal (ρ 0))) - g c =
    windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0 (fun u => ellVec (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) fun α =>
      Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW ((quadraticGradientDyn d s a β).coeff
        ρ) 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) -
        HRS.Whole.pair (HRS.Whole.withDensityReal (ρ 0)) (propagatorW ((quadraticGradientDyn d s a β).coeff
        ρ) 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) -
        η (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (b + u)
          (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) := by
  have hT0 : 0 ≤ T := hT.le
  refine s56_pathCoords_injective ((wholeSpaceIndex d : ℕ) : ℝ) T s' hs' ?_
  set Yfun : ℝ → OscDual d ((wholeSpaceIndex d : ℕ) : ℝ) := fun u => ellVec (d := d) ((wholeSpaceIndex d : ℕ) : ℝ)
    fun α => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW ((quadraticGradientDyn d s a β).coeff
        ρ) 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) -
        HRS.Whole.pair (HRS.Whole.withDensityReal (ρ 0)) (propagatorW ((quadraticGradientDyn d s a β).coeff
        ρ) 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) -
        η (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (b + u)
          (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) with hYfun
  have hYc : ContinuousOn Yfun (Set.Icc 0 T) := continuousOn_iff_continuous_restrict.2 hcont
  have hw := s56_pathCoords_windowPathOf (d := d) (m := ((wholeSpaceIndex d : ℕ) : ℝ)) (T := T) s'
    (fun u (_ : Unit) => Yfun u) (ζ := ()) hYc
  rw [hw]
  funext i
  obtain ⟨n, α⟩ := i
  have hu : (s' n : ℝ) ∈ Set.Icc (0 : ℝ) T := (s' n).2
  have hprob := hS.hprob (r := 0) ⟨le_rfl, by linarith⟩
  haveI := HRS.MS.Thm.cb_withDensityReal_isProb hprob
  haveI : IsProbabilityMeasure (HRS.Whole.empirical x) := HRS.Whole.empirical_isProbabilityMeasure (by omega) x
  have hk := s105_k0_eval _ hb rfl hS.hC (Real.sqrt N) hprob hS.hρ2 hN x hu α hS.hF
    (fun a' z => hS.hK a' 0 ⟨le_rfl, by linarith [hu.1, hu.2]⟩ z) (hS.hcl α (b + s' n) (by linarith [hu.1]))
  have hlhs : s56PathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s' (s56EvalPath hT0 (s105k0
      (fun (a' : Fin d) (z : Euc d) => r2WindowFeature ((quadraticGradientDyn d s a β).coeff ρ)
        ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b 0 z) (Real.sqrt N) (HRS.Whole.empirical x)
        (HRS.Whole.withDensityReal (ρ 0))) - g c) (n, α) =
      Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW ((quadraticGradientDyn d s a β).coeff
        ρ) 0 (b + s' n) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) -
        HRS.Whole.pair (HRS.Whole.withDensityReal (ρ 0)) (propagatorW ((quadraticGradientDyn d s a β).coeff
        ρ) 0 (b + s' n) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) - c (n, α) := by
    simp only [s56PathCoords, OscPath.at']
    show OscDual.coord (((show C(Set.Icc (0 : ℝ) T, OscDual d ((wholeSpaceIndex d : ℕ) : ℝ)) from s56EvalPath hT0 _) -
      (show C(Set.Icc (0 : ℝ) T, OscDual d ((wholeSpaceIndex d : ℕ) : ℝ)) from g c)) (s' n)) α = _
    rw [ContinuousMap.sub_apply, s56_coord_sub, s56EvalPath_apply, hk]
    have h2 := congrFun hgc (n, α)
    simp only [s56PathCoords, OscPath.at'] at h2
    rw [h2]
  rw [hlhs]
  simp only [hYfun]
  have hmemarr : Memℓp (fun α => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x)
      (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (b + s' n)
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) - HRS.Whole.pair (HRS.Whole.withDensityReal (ρ 0))
      (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (b + s' n)
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) - η (propagatorW ((quadraticGradientDyn d s a β).coeff
      ρ) 0 (b + s' n) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) 2 := by
    set E : OscDual d ((wholeSpaceIndex d : ℕ) : ℝ) := (s105k0 (fun (a' : Fin d) (z : Euc d) => r2WindowFeature
      ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b 0 z)
      (Real.sqrt N) (HRS.Whole.empirical x) (HRS.Whole.withDensityReal (ρ 0))).evalA (s' n : ℝ) with hE
    have h1 : Memℓp (fun α => OscDual.coord E α) 2 := by
      have := OscDual.coord_sq_summable' E
      exact (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).2 (by simpa using this)
    have h2 := h1.sub (hmemℓ n)
    have heq : (fun α => OscDual.coord E α) - (fun α => c (n, α)) = fun α => Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0
          (b + s' n) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) - HRS.Whole.pair (HRS.Whole.withDensityReal (ρ 0))
          (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (b + s' n)
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) - η (propagatorW ((quadraticGradientDyn d s a β).coeff
          ρ) 0 (b + s' n) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) := by
      funext α'
      have hk' := s105_k0_eval _ hb rfl hS.hC (Real.sqrt N) hprob hS.hρ2 hN x hu α' hS.hF
        (fun a' z => hS.hK a' 0 ⟨le_rfl, by linarith [hu.1, hu.2]⟩ z) (hS.hcl α' (b + s' n) (by linarith [hu.1]))
      simp only [Pi.sub_apply, hE]
      rw [hk', hcη (n, α')]
    rw [heq] at h2
    exact h2
  rw [s52_coord_ellVec hmemarr, hcη (n, α)]

end HRS.MS.S104b
