import HRS.MH.WpSpec2
import HRS.MH.WpP3a
import HRS.MH.WpQ1
import HRS.MH.WpQ3

/-!
# P3b: `HRS.MH.Wp.gff_stage1_p`

Copy-edit of `HRS.GF.gff_stage1` (GFFinal2.lean:64) at order `p > 0`, without `S.EnergyMomentFinite` and `InitialErrorFinite`.
The energy facts come from `gfwp_energy_aux_proof`, the remainder bound from `gff_remainder_bound_ae_proof`, the initial term from
`gff_initial_term_eq_lintegral_proof`; the pathwise bound is `Bm ω = ofReal (Cr σ) * E_ω` with `E_ω = ∫⁻_{[0,T]} ofReal 𝓔`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.WpP

open HRS HRS.GF HRS.Uniform HRS.Uniform.Kot

set_option maxHeartbeats 800000 in
theorem gff_stage1_p_proof : type_of% @HRS.MH.Wp.gff_stage1_p := by
  intro d b M K p hp
  obtain ⟨C₀min, hrem⟩ := gff_remainder_bound_ae_proof b M K
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  obtain ⟨Cr, hCr, hrem'⟩ := hrem C₀ hC₀
  refine ⟨Cr, hCr, ?_⟩
  intro S hS hMF N hN m hm EV hEV Ω mΩ P _ X₀ W X hX hF hEfin η₀ hη hind Y₀ hY₀m hY₀ Y hY
  have hT : 0 ≤ S.T := S.hT.le
  obtain ⟨ℱ, W', hF'⟩ := hF
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, π₁, hπ₁, ℱ₁, η', hfilt, hF₁, hη'0, hlawI⟩ :=
    gf_init_enlargement_proof S N P X₀ W X ℱ W' hF' hX.init η₀ hη hind
  set X₁ : ℝ≥0 → Ω₁ → Config d N := fun t ω => X t (π₁ ω) with hX₁def
  set W₁ : ℝ≥0 → Ω₁ → (Fin N → Euc d) := fun t ω => W t (π₁ ω) with hW₁def
  set W'₁ : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ := fun t ω k => W' t (π₁ ω) k with hW'₁def
  have hX₁ : IsStrongSolution P₁ (S.dynM M N) S.T (fun ω => X₀ (π₁ ω)) W₁ X₁ :=
    isStrongSolution_comp hπ₁ hX
  have hγm : (d : ℝ) / 2 < (S.γ : ℝ) := by
    have h1 : 2 * d + 10 < S.γ := S.hγ
    have h2 : ((2 * d + 10 : ℕ) : ℝ) < (S.γ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  -- energy facts on `Ω₁` and on `Ω`
  obtain ⟨hnn, hmeasE₁, hintE₁⟩ :=
    gfwp_energy_aux_proof S M hMF N hN P₁ (fun ω => X₀ (π₁ ω)) W₁ X₁ hX₁ ⟨ℱ₁, W'₁, hF₁⟩
  obtain ⟨-, hmeasE, -⟩ := gfwp_energy_aux_proof S M hMF N hN P X₀ W X hX ⟨ℱ, W', hF'⟩
  have hfin₁ : ∀ᵐ ω ∂P₁, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
      ENNReal.ofReal (S.energyCompletion N (X₁ (Real.toNNReal r) ω) r)) < ⊤ :=
    hπ₁.quasiMeasurePreserving.ae hEfin
  have hint' : ∀ᵐ ω ∂P₁, IntegrableOn (fun r => S.energyCompletion N (X₁ (Real.toNNReal r) ω) r)
      (Set.Icc (0 : ℝ) S.T) := by
    filter_upwards [hintE₁, hfin₁] with ω h1 h2
    exact (h1 h2).1
  -- the particle martingale and its stochastic convolution
  obtain ⟨Mart, hMartIto, hMartHM⟩ := gf_particle_martingale_proof S N (by omega) P₁ ℱ₁ W'₁ W₁ X₁ hF₁
  obtain ⟨Cm, hCm0, hmax⟩ := Q45.maximal_estimate_meas S.T K hT
  obtain ⟨Z₀, hZ₀, hZ₀c, hZ₀m, -⟩ := hmax Ω₁ P₁ ℱ₁ (NegSobolev d (S.γ : ℝ)) (NegSobolev d m) EV hEV.maxHyp
    Mart (fun r ω => covForm (S.γ : ℝ) (qN S N) (empirical (X₁ (Real.toNNReal r) ω))) hMartHM
  obtain ⟨Z, hZm, hZc, hZeq⟩ := gf_measurable_modification_proof P₁ S.T Z₀ hZ₀c hZ₀m
  have hZ : ∀ t ∈ Set.Icc (0 : ℝ) S.T, IsStochConv P₁ EV.VE EV.j Mart 0 t (Z t) :=
    fun t ht => isStochConv_congr_ae (hZ₀ t ht) (hZeq t ht).symm
  -- continuity of the fluctuation path
  obtain ⟨hΞc, hΞm⟩ := gf_fluc_continuous_proof S M hMF N m hm P₁ (fun ω => X₀ (π₁ ω)) W₁ X₁ hX₁ (sigN S N)
  obtain ⟨-, hΞmP⟩ := gf_fluc_continuous_proof S M hMF N m hm P X₀ W X hX (sigN S N)
  -- the remainder
  have hR := hrem' S hS hMF N hN m hm EV hEV P₁ (fun ω => X₀ (π₁ ω)) W₁ X₁ hX₁ ℱ₁ W'₁ hF₁ hnn hint' Mart
    hMartIto Z hZ (fun t _ => hZm t) (Filter.Eventually.of_forall hZc) hΞc
  set Bm : Ω₁ → ℝ≥0∞ := fun ω => ENNReal.ofReal (Cr * sigN S N) *
    ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (S.energyCompletion N (X₁ (Real.toNNReal r) ω) r) with hBm
  have hc0 : 0 ≤ Cr * sigN S N := mul_nonneg hCr.le (sigN_nonneg S N)
  have hbound : ∀ᵐ ω ∂P₁, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ‖flucProc m (sigN S N) X₁ (S.ρ N) t ω -
          EV.VE t 0 (EV.j (flucProc (S.γ : ℝ) (sigN S N) X₁ (S.ρ N) 0 ω)) - Z t ω‖ₑ ≤ Bm ω := by
    filter_upwards [hR, hnn, hintE₁, hfin₁] with ω hω hn hi hlt t ht
    obtain ⟨hint, heq⟩ := hi hlt
    have h1 : ‖flucProc m (sigN S N) X₁ (S.ρ N) t ω -
          EV.VE t 0 (EV.j (flucProc (S.γ : ℝ) (sigN S N) X₁ (S.ρ N) 0 ω)) - Z t ω‖ ≤
        Cr * sigN S N * ∫ r in Set.Icc (0 : ℝ) S.T, S.energyCompletion N (X₁ (Real.toNNReal r) ω) r := by
      refine (hω t ht).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hc0
      rw [intervalIntegral.integral_of_le ht.1]
      exact setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hn))
        (HasSubset.Subset.eventuallyLE (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2)))
    rw [← ofReal_norm]
    calc _ ≤ ENNReal.ofReal (Cr * sigN S N * ∫ r in Set.Icc (0 : ℝ) S.T,
            S.energyCompletion N (X₁ (Real.toNNReal r) ω) r) := ENNReal.ofReal_le_ofReal h1
      _ = Bm ω := by
        simp only [hBm]
        rw [ENNReal.ofReal_mul hc0, heq]
  have hBmm : AEMeasurable Bm P₁ := (hmeasE₁.const_mul (ENNReal.ofReal (Cr * sigN S N))).aemeasurable
  -- the `L^p` norm of `Bm`
  have hBmp : (∫⁻ ω, Bm ω ^ p ∂P₁) ^ (1 / p) ≤ ENNReal.ofReal (Cr * sigN S N) *
      (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
        ENNReal.ofReal (S.energyCompletion N (X (Real.toNNReal r) ω) r)) ^ p ∂P) ^ (1 / p) := by
    refine le_of_eq ?_
    have e : ∀ ω, Bm ω ^ p = ENNReal.ofReal (Cr * sigN S N) ^ p * (∫⁻ r in Set.Icc (0 : ℝ) S.T,
        ENNReal.ofReal (S.energyCompletion N (X₁ (Real.toNNReal r) ω) r)) ^ p :=
      fun ω => ENNReal.mul_rpow_of_nonneg _ _ hp.le
    simp_rw [e]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top),
      lintegral_comp_mp hπ₁ (f := fun ω => (∫⁻ r in Set.Icc (0 : ℝ) S.T,
        ENNReal.ofReal (S.energyCompletion N (X (Real.toNNReal r) ω) r)) ^ p)
        (hmeasE.pow_const p).aemeasurable,
      ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hp.le), ← ENNReal.rpow_mul,
      mul_one_div_cancel hp.ne', ENNReal.rpow_one]
  -- the law of the initial value
  have hη'm : Measurable η' := hη'0.mono (ℱ₁.le 0) le_rfl
  have hX₀m : AEMeasurable X₀ P := (hX.adapted 0).aemeasurable.congr hX.init
  have hm1 : AEMeasurable (fun ω' => (X₀ (π₁ ω'), η' ω')) P₁ :=
    (hX₀m.comp_quasiMeasurePreserving hπ₁.quasiMeasurePreserving).prodMk hη'm.aemeasurable
  have hm2 : AEMeasurable (fun ω => (X₀ ω, η₀ ω)) P := hX₀m.prodMk hη.aemeasurable
  have hmapη : P.map η₀ = P₁.map η' := by
    have e1 : P₁.map η' = (P₁.map (fun ω' => (X₀ (π₁ ω'), η' ω'))).map Prod.snd := by
      rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hm1]; rfl
    have e2 : P.map η₀ = (P.map (fun ω => (X₀ ω, η₀ ω))).map Prod.snd := by
      rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hm2]; rfl
    rw [e1, hlawI, ← e2]
  have hg : Measurable (fun x : NegSobolev d (S.γ : ℝ) => EV.j (AN S N • x)) :=
    EV.j.continuous.measurable.comp (measurable_const_smul _)
  have hlawY : P.map Y₀ = P₁.map (fun ω => EV.j (AN S N • η' ω)) := by
    have e : Y₀ = fun ω => EV.j (AN S N • η₀ ω) := funext hY₀
    rw [e, show (fun ω => EV.j (AN S N • η₀ ω)) = (fun x => EV.j (AN S N • x)) ∘ η₀ from rfl,
      ← Measure.map_map hg hη, hmapη, Measure.map_map hg hη'm]
    rfl
  refine ⟨Ω₁, mΩ₁, P₁, hP₁, π₁, hπ₁, ℱ₁, η', Mart, Z, Bm, ⟨hF₁.adapted, hη'0,
    fun τ => (hMartIto.adapted τ).mono (ℱ₁.le τ) le_rfl, hMartHM,
    gf_detCovDensity_proof S M hMF N (qN S N) (qN_nonneg S N), hZ, Filter.Eventually.of_forall hZc, hZm, hΞc, hΞm,
    hBmm, hbound, hY₀m, hY, hlawY⟩, hX₁, ⟨ℱ₁, W'₁, hF₁⟩, ?_, ?_, hBmp⟩
  · exact law_comp_mp hπ₁ hΞmP
  · exact gff_initial_term_eq_lintegral_proof S hπ₁ X₀ X hX.init hX₀m η₀ η' hη hη'm hlawI hγm p hp

end HRS.MH.WpP
