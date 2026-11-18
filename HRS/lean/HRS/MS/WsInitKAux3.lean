import HRS.MS.WsInitKAux2
import HRS.MS.WsInitGAux14
import HRS.MS.WsInitHAux13
import HRS.MS.WsStatAux39

/-!
# S21 packet K, part 3: gluing G and H, the full `S21Init`

`s21k_init_at`: `S21Init d s a β T _` for `d ≥ 2`, `0 ≤ s < d`, `a, β, T > 0`.  One Gaussian path measure `γ_0 = Φ_* γ` (packet G,
`s21k_struct`, independent of `N`) serves the fdd clause, the smooth clause (`d_{C_b²}(Law A(k_0), γ_0) ≤ C √δ_N`, the proof of `s21g_init_smooth` with the
same `γ_0`) and the `W_1` clause (`s21h_w1_half` with `ι = Φ`, the product decay `s21k_decay`, `γ_0 = (m - I)/2 > 5d/4`).
(`S21Init` unfolds to `S21InitAt` at `m = wholeSpaceIndex d`; `s21k_init_at` is stated in that form.)
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

theorem s21k_init_at (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {T : ℝ} (hT : 0 < T) : S21Init d s a β T hT.le := by
  classical
  by_cases hex : ∃ ρ₁ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ₁
  swap
  · exact ⟨0, le_rfl, fun ρ hρ => absurd ⟨ρ, hρ⟩ hex⟩
  obtain ⟨ρ₁, h₁⟩ := hex
  obtain ⟨φ, γ, Φ, Cst, hφ, hγp, hΦ, hγ, hst, hpath, hfdd, σ, hσφ⟩ := s21k_struct hd hs0 hsd ha hβ hT h₁
  obtain ⟨A, γ₀, hγ₀, hdec⟩ := s21k_decay hd hs0 hsd ha hβ hT h₁
  have hdecay : ∀ k, cbNorm (s21gJ d) (φ k) ≤ A * (((1 : ℝ) + ((σ k).1 : ℝ)) ^ (-(5 : ℝ) / 4) *
      oscEigenvalue d (σ k).2 ^ (-γ₀)) := fun k => by
    rw [hσφ k]; exact hdec _ _
  obtain ⟨CW, hCW0, hCW⟩ := s21h_w1_half hd hs0 hsd ha hβ (s21gJ_gt d) ((wholeSpaceIndex d : ℕ) : ℝ) T hT.le
    ((quadraticGradientDyn d s a β).coeff (fun _ => ρ₁)) σ Φ φ hφ hγ₀ hdecay γ hγ
  set S : ℝ := featureSum (s21gJ d) φ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun i => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hcJ := s11p_cJ_pos T
  set C1 : ℝ := max 1 (s11p_cJ T ^ 2) * (max Cst 0 * (S + S ^ 2)) with hC1
  have hC10 : 0 ≤ C1 := by positivity
  refine ⟨max C1 CW, le_max_of_le_left hC10, fun ρ hρ N hN => ?_⟩
  have hρeq : ρ = ρ₁ := (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ).trans
    (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ h₁).symm
  subst hρeq
  have hγpm : IsProbabilityMeasure (γ.map Φ) := by
    haveI := hγp
    exact (Measure.isProbabilityMeasure_map_iff Φ.continuous.measurable.aemeasurable).2 inferInstance
  have hδ : 0 < HRS.deltaN d s N := s21_deltaN_pos hs0 hsd N (by omega)
  refine ⟨γ.map Φ, hγpm, hfdd, ?_, ?_⟩
  · obtain ⟨-, hfm, hsm, -⟩ := hst N hN
    set P := HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β with hP
    set fv := featureVec φ (HRS.Whole.firstMarginal P) with hfv
    obtain ⟨Cs, -, hSall⟩ := S45.s45_static_all hd hs0 hsd ha hβ
    haveI hP0 : IsProbabilityMeasure P := (hSall N hN).prob
    have hmapeq : P.map (s21IP ((wholeSpaceIndex d : ℕ) : ℝ) T hT.le
        ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) N (HRS.Whole.meanEmpirical P)) = (P.map fv).map Φ := by
      rw [Measure.map_map Φ.continuous.measurable hfm]
      congr 1
      funext x
      exact hpath N hN x
    rw [hmapeq]
    haveI := hγp
    haveI hPp : IsProbabilityMeasure (P.map fv) :=
      (Measure.isProbabilityMeasure_map_iff hfm.aemeasurable).2 inferInstance
    have h1 := HRS.Main.smoothDist_map_clm_le Φ 2 (P.map fv) γ
    have hn : max 1 (‖Φ‖ ^ 2) ≤ max 1 (s11p_cJ T ^ 2) :=
      max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hΦ 2)
    have hX : 0 ≤ (S + S ^ 2) * Real.sqrt (HRS.deltaN d s N) := by positivity
    have hsm' : smoothDist 2 (P.map fv) γ ≤ max Cst 0 * (S + S ^ 2) * Real.sqrt (HRS.deltaN d s N) := by
      refine hsm.trans ?_
      have := mul_le_mul_of_nonneg_right (le_max_left Cst 0) hX
      nlinarith
    have h2 : max 1 (‖Φ‖ ^ 2) * smoothDist 2 (P.map fv) γ ≤ C1 * Real.sqrt (HRS.deltaN d s N) :=
      calc max 1 (‖Φ‖ ^ 2) * smoothDist 2 (P.map fv) γ
          ≤ max 1 (s11p_cJ T ^ 2) * (max Cst 0 * (S + S ^ 2) * Real.sqrt (HRS.deltaN d s N)) :=
            mul_le_mul hn hsm' (smoothDist_nonneg 2 _ _) (by positivity)
        _ = _ := by rw [hC1]; ring
    refine (h1.trans h2).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  · refine (hCW N hN (fun x => hpath N hN x)).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hδ.le _)

end HRS.MS.S21
