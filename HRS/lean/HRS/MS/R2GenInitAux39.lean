import HRS.MS.R2GenInitAux38

/-!
# S10.5 window comparison, packet E5: the initial-path discrepancy is the coupling cost `r2InitCouplingPath`

`s105Hfun C m T b σ ν g x c = ‖A(k₀(x)) - g(c)‖`; `s105Hfun_meas`; `s105_eps_pointwise`: if the array `c` is the array of the prescribed field along the
window and `g c` has these coordinates, the path `A(k₀) - g(c)` equals the window path of the initial coupling field, so the cost term of the abstract
comparison is `‖r2InitCouplingPath‖`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem

variable {d : ℕ}

/-- The initial-path discrepancy `‖A(k₀(x)) - g(c)‖` as a function of the configuration and the array. -/
def s105Hfun (C : WholeCoeff d) (m T b σ : ℝ) (ν : Measure (Euc d)) (hT : 0 ≤ T) {N : ℕ}
    (g : (ℕ × MultiIndex d → ℝ) → OscPath d m T) (x : EucConfig d N) (c : ℕ × MultiIndex d → ℝ) : ℝ≥0∞ :=
  ‖s56EvalPath hT (s105k0 (fun (a : Fin d) (z : Euc d) => r2WindowFeature C m T (gradComp a) b 0 z) σ
    (HRS.Whole.empirical x) ν) - g c‖ₑ

theorem s105Hfun_meas (C : WholeCoeff d) (m T b σ : ℝ) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hρ2 : Integrable (fun x : Euc d => ‖x‖ ^ 2 * ρ x)) (hT : 0 ≤ T) {N : ℕ} (hN : 1 ≤ N) {τ₀ : ℝ} (hτ : b ≤ τ₀)
    (hb : 0 ≤ b) (hF : S105Feat d m T τ₀ (fun a r x => r2WindowFeature C m T (gradComp a) b r x))
    (g : (ℕ × MultiIndex d → ℝ) → OscPath d m T) (hg : Measurable g) :
    Measurable fun z : EucConfig d N × (ℕ × MultiIndex d → ℝ) =>
      s105Hfun C m T b σ (HRS.Whole.withDensityReal ρ) hT g z.1 z.2 := by
  unfold s105Hfun
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) τ₀ := ⟨le_rfl, hb.trans hτ⟩
  obtain ⟨B, hB0, hB⟩ := hF.bound
  have hmeas : ∀ a : Fin d, Measurable fun z : Euc d => r2WindowFeature C m T (gradComp a) b 0 z :=
    fun a => (hF.cont_x a 0 h0).measurable
  have := HRS.MS.Thm.cb_withDensityReal_isProb hρ
  have hμint := s56_integrable_norm_withDensity hρ hρ2
  have h1 : Measurable fun x : EucConfig d N => s56EvalPath hT
      (s105k0 (fun (a : Fin d) (z : Euc d) => r2WindowFeature C m T (gradComp a) b 0 z) σ
        (HRS.Whole.empirical x) (HRS.Whole.withDensityReal ρ)) :=
    (s56EvalPath hT).continuous.measurable.comp (s105_k0_meas _ σ B hB0 hmeas (fun a z => hB a 0 h0 z)
      (by omega) _ hμint)
  exact ((h1.comp measurable_fst).sub (hg.comp measurable_snd)).enorm

theorem s105_eps_path {s a β T b : ℝ} {ρ : Euc d → ℝ} (hS : S105Stat d s a β T b ρ) (hb : 0 ≤ b) (hT : 0 < T)
    {N : ℕ} (hN : 1 ≤ N) (s' : ℕ → Set.Icc (0 : ℝ) T) (hs' : DenseRange s')
    (g : (ℕ × MultiIndex d → ℝ) → OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T) (x : EucConfig d N)
    (η : (Euc d → ℝ) → ℝ) (c : ℕ × MultiIndex d → ℝ)
    (hcη : ∀ i : ℕ × MultiIndex d, c i = η (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0
      (b + s' i.1) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) i.2)))
    (hmemℓ : ∀ n : ℕ, Memℓp (fun α => c (n, α)) 2)
    (hgc : s56PathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s' (g c) = c)
    (hm : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ))
    (hcont : Continuous fun u : Set.Icc (0 : ℝ) T => (ellVec (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) fun α =>
      Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW ((quadraticGradientDyn d s a β).coeff
        (fun _ => ρ)) 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) -
        HRS.Whole.pair (HRS.Whole.withDensityReal ρ) (propagatorW ((quadraticGradientDyn d s a β).coeff
        (fun _ => ρ)) 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) -
        η (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (b + u)
          (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)))) :
    s56EvalPath hT.le (s105k0 (fun (a' : Fin d) (z : Euc d) => r2WindowFeature
      ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b 0 z)
      (Real.sqrt N) (HRS.Whole.empirical x) (HRS.Whole.withDensityReal ρ)) - g c =
    windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0 (fun u => ellVec (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) fun α =>
      Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW ((quadraticGradientDyn d s a β).coeff
        (fun _ => ρ)) 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) -
        HRS.Whole.pair (HRS.Whole.withDensityReal ρ) (propagatorW ((quadraticGradientDyn d s a β).coeff
        (fun _ => ρ)) 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) -
        η (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (b + u)
          (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) := by
  have hT0 : 0 ≤ T := hT.le
  refine s56_pathCoords_injective ((wholeSpaceIndex d : ℕ) : ℝ) T s' hs' ?_
  set Yfun : ℝ → OscDual d ((wholeSpaceIndex d : ℕ) : ℝ) := fun u => ellVec (d := d) ((wholeSpaceIndex d : ℕ) : ℝ)
    fun α => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW ((quadraticGradientDyn d s a β).coeff
        (fun _ => ρ)) 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) -
        HRS.Whole.pair (HRS.Whole.withDensityReal ρ) (propagatorW ((quadraticGradientDyn d s a β).coeff
        (fun _ => ρ)) 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) -
        η (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (b + u)
          (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) with hYfun
  have hYc : ContinuousOn Yfun (Set.Icc 0 T) := continuousOn_iff_continuous_restrict.2 hcont
  have hw := s56_pathCoords_windowPathOf (d := d) (m := ((wholeSpaceIndex d : ℕ) : ℝ)) (T := T) s'
    (fun u (_ : Unit) => Yfun u) (ζ := ()) hYc
  rw [hw]
  funext i
  obtain ⟨n, α⟩ := i
  have hu : (s' n : ℝ) ∈ Set.Icc (0 : ℝ) T := (s' n).2
  have hprob := hS.hprob
  haveI := HRS.MS.Thm.cb_withDensityReal_isProb hprob
  haveI : IsProbabilityMeasure (HRS.Whole.empirical x) := HRS.Whole.empirical_isProbabilityMeasure (by omega) x
  have hk := s105_k0_eval _ hb rfl hS.hC (Real.sqrt N) hprob hS.hρ2 hN x hu α hS.hF
    (fun a' z => hS.hK a' 0 ⟨le_rfl, by linarith [hu.1, hu.2]⟩ z) (hS.hcl α (b + s' n) (by linarith [hu.1]))
  have hlhs : s56PathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s' (s56EvalPath hT0 (s105k0
      (fun (a' : Fin d) (z : Euc d) => r2WindowFeature ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
        ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b 0 z) (Real.sqrt N) (HRS.Whole.empirical x)
        (HRS.Whole.withDensityReal ρ)) - g c) (n, α) =
      Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW ((quadraticGradientDyn d s a β).coeff
        (fun _ => ρ)) 0 (b + s' n) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) -
        HRS.Whole.pair (HRS.Whole.withDensityReal ρ) (propagatorW ((quadraticGradientDyn d s a β).coeff
        (fun _ => ρ)) 0 (b + s' n) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) - c (n, α) := by
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
      (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (b + s' n)
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) - HRS.Whole.pair (HRS.Whole.withDensityReal ρ)
      (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (b + s' n)
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) - η (propagatorW ((quadraticGradientDyn d s a β).coeff
      (fun _ => ρ)) 0 (b + s' n) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) 2 := by
    set E : OscDual d ((wholeSpaceIndex d : ℕ) : ℝ) := (s105k0 (fun (a' : Fin d) (z : Euc d) => r2WindowFeature
      ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b 0 z)
      (Real.sqrt N) (HRS.Whole.empirical x) (HRS.Whole.withDensityReal ρ)).evalA (s' n : ℝ) with hE
    have h1 : Memℓp (fun α => OscDual.coord E α) 2 := by
      have := OscDual.coord_sq_summable' E
      exact (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).2 (by simpa using this)
    have h2 := h1.sub (hmemℓ n)
    have heq : (fun α => OscDual.coord E α) - (fun α => c (n, α)) = fun α => Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0
          (b + s' n) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) - HRS.Whole.pair (HRS.Whole.withDensityReal ρ)
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (b + s' n)
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) - η (propagatorW ((quadraticGradientDyn d s a β).coeff
          (fun _ => ρ)) 0 (b + s' n) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) := by
      funext α'
      have hk' := s105_k0_eval _ hb rfl hS.hC (Real.sqrt N) hprob hS.hρ2 hN x hu α' hS.hF
        (fun a' z => hS.hK a' 0 ⟨le_rfl, by linarith [hu.1, hu.2]⟩ z) (hS.hcl α' (b + s' n) (by linarith [hu.1]))
      simp only [Pi.sub_apply, hE]
      rw [hk', hcη (n, α')]
    rw [heq] at h2
    exact h2
  rw [s52_coord_ellVec hmemarr, hcη (n, α)]

end HRS.MS.R2GenInit
