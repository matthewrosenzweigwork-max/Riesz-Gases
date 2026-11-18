import HRS.MS.WsInitGAux12
import HRS.Main.Headline

/-!
# S21 packet G, part 13: the smooth half of the initial-path input (`s21g_init_smooth`)

`s21g_init_smooth`: the smooth half of `S21InitAt` at `m = wholeSpaceIndex d` (with `s21IP` unfolded as `s56EvalPath (s56k0 ..)`): there is `C ≥ 0` such that for the
thermal equilibrium `ρ` and every `N ≥ 2` there is a probability measure `γ_0` on `C([0,T];B_m)` whose finite-dimensional laws are
`multivariateGaussian 0 (HRS.Whole.susceptibilityCov (U^{0,t_i}φ_{α_i}, U^{0,t_j}φ_{α_j}))` (matrix positive semidefinite) and
`d_{C_b²}(Law A(k_0), γ_0) ≤ C √δ_N`.  The measure is `γ_0 = Φ_* γ`, independent of `N` (`s21g_struct`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath
open HRS (Euc cbNorm MemCb smoothDist)

variable {d : ℕ}

theorem s21g_init_smooth (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ → ∀ N : ℕ, 2 ≤ N →
      ∃ γ0 : Measure (OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T), IsProbabilityMeasure γ0 ∧
        (∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
          (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
            (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts i)
              (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i)))
            (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts j)
              (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j)))).PosSemidef ∧
          γ0.map (fun w : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => (WithLp.toLp 2 fun i =>
              OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p))) =
            multivariateGaussian 0 (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s)
              (HRS.Whole.withDensityReal ρ) β
              (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts i)
                (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i)))
              (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts j)
                (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j))))) ∧
        smoothDist 2 ((HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β).map
            (fun x : EucConfig d N => s56EvalPath hT.le (s56k0 ((quadraticGradientDyn d s a β).coeff (fun _ => ρ))
              ((wholeSpaceIndex d : ℕ) : ℝ) T (Real.sqrt N) (HRS.Whole.empirical x)
              (HRS.Whole.meanEmpirical (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β))))) γ0 ≤
          C * Real.sqrt (HRS.deltaN d s N) := by
  classical
  by_cases hex : ∃ ρ₁ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ₁
  swap
  · exact ⟨0, le_rfl, fun ρ hρ => absurd ⟨ρ, hρ⟩ hex⟩
  obtain ⟨ρ₁, h₁⟩ := hex
  obtain ⟨φ, γ, Φ, Cst, hφ, hγp, hΦ, hγ, hst, hpath, hfdd⟩ := s21g_struct hd hs0 hsd ha hβ hT h₁
  set S : ℝ := featureSum (s21gJ d) φ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun i => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hcJ := s11p_cJ_pos T
  refine ⟨max 1 (s11p_cJ T ^ 2) * (max Cst 0 * (S + S ^ 2)), by positivity, fun ρ hρ N hN => ?_⟩
  have hρeq : ρ = ρ₁ := (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ).trans
    (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ h₁).symm
  subst hρeq
  refine ⟨γ.map Φ, ?_, hfdd, ?_⟩
  · haveI := hγp
    exact (Measure.isProbabilityMeasure_map_iff Φ.continuous.measurable.aemeasurable).2 inferInstance
  · obtain ⟨-, hfm, hsm, -⟩ := hst N hN
    set P := HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β with hP
    set fv := featureVec φ (HRS.Whole.firstMarginal P) with hfv
    obtain ⟨Cs, -, hSall⟩ := S45.s45_static_all hd hs0 hsd ha hβ
    haveI hP0 : IsProbabilityMeasure P := (hSall N hN).prob
    have hmapeq : P.map (fun x : EucConfig d N => s56EvalPath hT.le (s56k0
        ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T (Real.sqrt N)
        (HRS.Whole.empirical x) (HRS.Whole.meanEmpirical P))) = (P.map fv).map Φ := by
      rw [Measure.map_map Φ.continuous.measurable hfm]
      congr 1
      funext x
      exact hpath N hN x
    rw [hmapeq]
    haveI := hγp
    haveI hPp : IsProbabilityMeasure (P.map fv) := (Measure.isProbabilityMeasure_map_iff hfm.aemeasurable).2 inferInstance
    have h1 := HRS.Main.smoothDist_map_clm_le Φ 2 (P.map fv) γ
    refine h1.trans ?_
    have hn : max 1 (‖Φ‖ ^ 2) ≤ max 1 (s11p_cJ T ^ 2) :=
      max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hΦ 2)
    have hX : 0 ≤ (S + S ^ 2) * Real.sqrt (HRS.deltaN d s N) := by positivity
    have hsm' : smoothDist 2 (P.map fv) γ ≤ max Cst 0 * (S + S ^ 2) * Real.sqrt (HRS.deltaN d s N) := by
      refine hsm.trans ?_
      have : Cst * (S + S ^ 2) * Real.sqrt (HRS.deltaN d s N) ≤
          max Cst 0 * (S + S ^ 2) * Real.sqrt (HRS.deltaN d s N) := by
        have := mul_le_mul_of_nonneg_right (le_max_left Cst 0) hX
        nlinarith
      exact this
    calc max 1 (‖Φ‖ ^ 2) * smoothDist 2 (P.map fv) γ
        ≤ max 1 (s11p_cJ T ^ 2) * (max Cst 0 * (S + S ^ 2) * Real.sqrt (HRS.deltaN d s N)) :=
          mul_le_mul hn hsm' (smoothDist_nonneg 2 _ _) (by positivity)
      _ = _ := by ring

end HRS.MS.S21
