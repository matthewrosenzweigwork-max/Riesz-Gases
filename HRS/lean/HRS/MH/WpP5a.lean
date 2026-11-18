import HRS.MH.WpSpec2
import HRS.MH.WpP3b
import HRS.MH.WpP4
import HRS.MH.WpQ1

/-!
# P5a: `HRS.MH.Wp.gff_core_Wp_trace`

Order-`p` copy-edit of `HRS.GF.gff_core` (GFFinal3.lean:18-262), trace-norm coupling, gradient clause.
Stage 1 is `gff_stage1_p_proof` (P3b), stage 2 is `gff_stage2_p_proof` (P4); `En ≠ ⊤` gives the a.s. finiteness of
`E_ω = ∫⁻_{[0,T]} ofReal 𝓔` through `gfwp_energy_aux_proof`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.WpP

open HRS HRS.GF HRS.Uniform HRS.Uniform.Kot

set_option maxHeartbeats 1600000 in
theorem gff_core_Wp_trace_proof : type_of% @HRS.MH.Wp.gff_core_Wp_trace := by
  intro d b p hp
  have hp0 : 0 < p := by linarith
  obtain ⟨K, hK0, hev⟩ := gf_ev_grad_proof b
  obtain ⟨C₀a, hs1⟩ := gff_stage1_p_proof b (-1) K p hp0
  refine ⟨C₀a, fun C₀ hC₀ => ?_⟩
  by_cases hex : ∃ S₀ : GeneralSetup d, S₀.Within { b with C₀ := C₀ }
  swap
  · exact ⟨1, one_pos, fun S hS => absurd ⟨S, hS⟩ hex⟩
  obtain ⟨S₀, hS₀⟩ := hex
  have hbT : 0 ≤ b.T := by rw [← hS₀.2.1]; exact S₀.hT.le
  obtain ⟨Cr, hCr, hs1'⟩ := hs1 C₀ hC₀
  obtain ⟨C2, hC20, hs2⟩ := gff_stage2_p_proof b.T K p hbT hp
  set C : ℝ := C2 + Cr + 1 with hCdef
  have hCpos : 0 < C := by linarith
  refine ⟨C, hCpos, ?_⟩
  intro S hS hMF hPos N hN Ω mΩ P _ X₀ W _ X hX hF η₀ hη hind Y hY
  dsimp only
  intro hEn
  have hST : S.T = b.T := hS.2.1
  have hT' : 0 ≤ S.T := S.hT.le
  have hSw : S.Within { b with C₀ := S.C₀ } := by
    have hC : S.C₀ = C₀ := hS.2.2.2.2.2.1
    rw [hC]; exact hS
  obtain ⟨EV, hEV⟩ := hev S hSw hMF hPos N
  have hm : (S.γ : ℝ) ≤ (S.γ : ℝ) := le_rfl
  have hj : ∀ x, EV.j x = x := fun x => by rw [hEV.j_eq, embed_self]
  set Y₀ : Ω → NegSobolev d (S.γ : ℝ) := fun ω => AN S N • η₀ ω with hY₀def
  have hY₀m : Measurable Y₀ := hη.const_smul (AN S N)
  have hY₀ : ∀ ω, Y₀ ω = EV.j (AN S N • η₀ ω) := fun ω => by rw [hj]
  -- finiteness of the energy integral from `En ≠ ⊤`
  obtain ⟨-, hmeasE, -⟩ := gfwp_energy_aux_proof S (-1) hMF N hN P X₀ W X hX hF
  have hIfin : (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) S.T,
      ENNReal.ofReal (S.energyCompletion N (X (Real.toNNReal t) ω) t)) ^ p ∂P) ≠ ⊤ := by
    intro h
    apply hEn
    rw [h]
    exact ENNReal.top_rpow_of_pos (by positivity)
  have hEfin : ∀ᵐ ω ∂P, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
      ENNReal.ofReal (S.energyCompletion N (X (Real.toNNReal r) ω) r)) < ⊤ := by
    filter_upwards [ae_lt_top (hmeasE.pow_const p) hIfin] with ω hω
    exact (ENNReal.rpow_lt_top_iff_of_pos hp0).1 hω
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, π₁, hπ₁, ℱ₁, η', Mart, Z, Bm, hS1, hX₁, hF₁, hlaw, hinit, hBm⟩ :=
    hs1' S hS hMF N hN (S.γ : ℝ) hm EV hEV P X₀ W X hX hF hEfin η₀ hη hind Y₀ hY₀m hY₀ Y hY
  set X₁ : ℝ≥0 → Ω₁ → Config d N := fun t ω => X t (π₁ ω) with hX₁def
  have hq0 := qN_nonneg S N
  have hσ0 := sigN_nonneg S N
  -- the trace-norm coupling on the first enlargement
  set Sg : ℝ → Ω₁ → (NegSobolev d (S.γ : ℝ) →L[ℝ] NegSobolev d (S.γ : ℝ) →L[ℝ] ℝ) :=
    fun r ω => covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω)) with hSg
  set Cb := covDensT (S.γ : ℝ) (qN S N) S.T (S.ρ N) with hCb
  have hcpl := gff_adapted_coupling_trace P₁ ℱ₁ S.T hT' ⟨ℱ₁ 0, le_rfl⟩ Mart Sg hS1.mart Cb hS1.det
  have hcostm : AEMeasurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T,
      ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) P₁ :=
    (measurable_trace_integral hS1.mart hS1.det).aemeasurable
  have hW := hs2 S hST (-1) hMF N hN (S.γ : ℝ) hm EV hEV P P₁ ℱ₁ X₁ η' Mart Z Bm Y₀ Y hS1
    (fun r ω => traceNormForm (Sg r ω - Cb r)) hcpl hcostm
  rw [hlaw] at hW
  -- measurability of the covariance-error integral on `Ω`
  obtain ⟨ℱ, W', hF'⟩ := hF
  obtain ⟨MartP, -, hMartP⟩ := gf_particle_martingale_proof S N (by omega) P ℱ W' W X hF'
  have hdet := gf_detCovDensity_proof S (-1) hMF N (qN S N) hq0
  have hmeasCv : Measurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
      (covForm (S.γ : ℝ) (qN S N) (empirical (X (Real.toNNReal r) ω)) -
        covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) := by
    have h := measurable_trace_integral hMartP hdet
    convert h using 1
    funext ω
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    simp only [covDensT, if_pos hr]
  -- transfer of the cost term from `P₁` to `P`
  have hconvc : ∀ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
      ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) =
      ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
        (covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω)) -
          covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r)))) := fun ω => by
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    simp only [hSg, hCb, covDensT, if_pos hr]
  have hcostEq : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
      ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ^ (p / 2) ∂P₁) =
      ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
        (covForm (S.γ : ℝ) (qN S N) (empirical (X (Real.toNNReal r) ω)) -
          covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) ^ (p / 2) ∂P := by
    simp_rw [hconvc]
    exact lintegral_comp_mp hπ₁ (f := fun ω => (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
      (traceNormForm (covForm (S.γ : ℝ) (qN S N) (empirical (X (Real.toNNReal r) ω)) -
        covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) ^ (p / 2))
      (hmeasCv.pow_const (p / 2)).aemeasurable
  rw [hcostEq, hinit] at hW
  have hσ : ENNReal.ofReal (Cr * sigN S N) = ENNReal.ofReal Cr * ENNReal.ofReal (sigN S N) :=
    ENNReal.ofReal_mul hCr.le
  have hC2 : ENNReal.ofReal C2 ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (by rw [hCdef]; linarith)
  have hCr' : ENNReal.ofReal Cr ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (by rw [hCdef]; linarith)
  calc _ ≤ _ := hW
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (AN S N) * (∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ)
            (empirical (X₀ ω)) (withDensityReal (S.ρ N 0)) - η₀ ω‖ₑ ^ p ∂P) ^ (1 / p)) +
        ENNReal.ofReal C * (ENNReal.ofReal (sigN S N) * (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) S.T,
          ENNReal.ofReal (S.energyCompletion N (X (Real.toNNReal t) ω) t)) ^ p ∂P) ^ (1 / p)) +
        ENNReal.ofReal C * (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
          (covForm (S.γ : ℝ) (qN S N) (empirical (X (Real.toNNReal r) ω)) -
            covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) ^ (p / 2) ∂P) ^ (1 / p) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · gcongr
        · refine hBm.trans ?_
          rw [hσ, mul_assoc]
          gcongr
        · gcongr
    _ = _ := by ring
