import HRS.MS.R2InterpAux47
import HRS.MC.S7PIG6A

/-!
# S10.2 (worker S102), part 48 (packet F8): the drift Riemann--Stieltjes integral of a cylindrical functional
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIL HRS.MC.Sec7.S7PIF6 HRS.MS.FixEq HRS.MC.Sec7.S7PIG6

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}
  {b : ℝ → (Euc d → ℝ) → ℝ} {Mb : ℝ → ℝ}

/-- **F8**: the sums `∑ D u_{G∘obs}(τ, Y_τ)[𝒟_b((a,a'])]` converge to `∫_{(0,T]} ∑_i ∂_iF(r, obs Y_r) b^r(obsTest_i r) dr`. -/
theorem s102_F8 (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) (hT : 0 < T)
    (γ : ℝ → Measure (OscPath d m T)) (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    {q : ℕ} (τ : Fin q → Icc (0 : ℝ) T) (α : Fin q → MultiIndex d)
    (hcov : ∀ k k', ContinuousOn (fun u => s102_obsCov C m τ α u k k') (Icc 0 T))
    {G : EuclideanSpace ℝ (Fin q) → ℝ} (hG : MemCb 2 G) (Y : ℝ → OscPath d m T)
    (hY : ContinuousOn Y (Icc 0 T)) :
    IsR2RS T (fun t a a' => fderiv ℝ (r2HeatFn γ (fun w => G (s102_obs τ α w)) t) (Y t)
        (r2DriftInc C m T b a a'))
      (∫ u in Ioc 0 T, ∑ i, fderiv ℝ (gaussHeat (s102_obsCov C m τ α) G u) (s102_obs τ α (Y u))
        (EuclideanSpace.single i 1) * s102_hh C m τ α b i u) := by
  set g : Fin q → ℝ → ℝ := fun i t => fderiv ℝ (gaussHeat (s102_obsCov C m τ α) G t) (s102_obs τ α (Y t))
    (EuclideanSpace.single i 1) with hgdef
  have hcont := HRS.MC.Sec7.S7PIS3.s7_PIH_heat_cont_proof T _ hcov
    (fun u hu => (s102_obs_law C (hγ u hu) τ α).1) G 2 hG 1 (by norm_num)
  have hg : ∀ i, ContinuousOn (g i) (Icc 0 T) := by
    intro i
    have h1 : ContinuousOn (fun t : ℝ => (t, s102_obs τ α (Y t))) (Icc 0 T) :=
      continuousOn_id.prodMk ((s102_obs τ α).continuous.comp_continuousOn hY)
    have h2 := hcont.comp h1 (fun t ht => ⟨ht, mem_univ _⟩)
    have h3 := ((S7PIL_ev (fun _ : Fin 1 => (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin q)))).continuous.comp_continuousOn h2)
    refine h3.congr fun t ht => ?_
    simp only [Function.comp_apply, S7PIL_ev_apply, iteratedFDeriv_one_apply, hgdef]
  have hI := HRS.MC.Sec7.S7PIS2.S7PIS2_RS_density T hT g (fun i => s102_hh C m τ α b i) hg
    (fun i => s102_hh_integrableOn hP hD hb τ α i)
  refine (s102_isR2RS_iff _ _ _).2 (S7PIG6_IsRS_congr hI fun t a a' ht ha haa' ha'T => ?_)
  rw [s102_heat_fderiv_apply γ hγ τ α hG ht]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s102_obs_driftInc hP hD hlin hb hT τ α ha (ha.trans haa') i, s102_hh_integral]

end HRS.MS.R2Interp

end
