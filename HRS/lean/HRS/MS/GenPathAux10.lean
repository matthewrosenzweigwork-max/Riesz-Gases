import HRS.MS.GenPathAux9
import HRS.Main.GFSpec3Tie

/-!
# S5.6 packet P9b: the `W_p` comparison of reconstructed `𝒦`-valued martingale paths, `p ∈ {1,2}`

`s56_wasserstein_abstract`: the single-window Wasserstein comparison `gf_wasserstein_comparison_proof` (Section 3,
adapted coupling of the martingales with difference martingale of covariation `Sd`, `‖Sd‖₁ ≤ cost`) on the Hilbert
space `𝒦` with the identity evolution, followed by `𝒯` (`wassersteinE_map_clm_le`) and the remainder `R`
(coupling bound `wassersteinE_le_of_coupling`, triangle inequality):
`W_p(Law(A(k₀) + 𝒯M + R), Law(A(k₀) + 𝒯G)) ≤ C (E∫_0^T cost_r dr)^{1/2} + ‖R‖_{L^p(C_tℓ²)}`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.U9

instance s56_oscPath_complete {d : ℕ} {m T : ℝ} : CompleteSpace (OscPath d m T) :=
  inferInstanceAs (CompleteSpace C(Set.Icc (0 : ℝ) T, OscDual d m))

variable {d : ℕ}

theorem s56_wasserstein_abstract (m T : ℝ) (hT : 0 ≤ T) (p : ℝ) (hp : p = 1 ∨ p = 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (k0 : Ω → KSpace d m T), Measurable k0 →
      ∀ (M G : ℝ → Ω → KSpace d m T), (∀ t, Measurable (M t)) → (∀ t, Measurable (G t)) →
      ∀ (Sd : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)) (cost : ℝ → Ω → ℝ),
      IsHilbertMartingaleWithCovariation P ℱ T (fun τ ζ => M (min τ T) ζ - G (min τ T) ζ)
        (fun r ζ => if r ≤ T then Sd r ζ else 0) →
      (∀ᵐ ζ ∂P, ∀ r : ℝ, 0 ≤ r → r ≤ T → traceNormForm (Sd r ζ) ≤ cost r ζ) →
      (∀ᵐ ζ ∂P, ContinuousOn (fun t => M t ζ) (Set.Icc 0 T)) → (∀ᵐ ζ ∂P, M 0 ζ = 0) →
      (∀ᵐ ζ ∂P, ContinuousOn (fun t => G t ζ) (Set.Icc 0 T)) → (∀ᵐ ζ ∂P, G 0 ζ = 0) →
      ∀ (R : ℝ → Ω → OscDual d m), (∀ᵐ ζ ∂P, ContinuousOn (fun t => R t ζ) (Set.Icc 0 T)) →
      (∀ t, Measurable (R t)) → ∀ (Ξ Yh : Ω → OscPath d m T),
      (∀ᵐ ζ ∂P, Ξ ζ = windowPathOf m T 0
        (fun t => (k0 ζ).evalA t + reconstructPath m T M ζ t + R t ζ)) →
      (∀ᵐ ζ ∂P, Yh ζ = windowPathOf m T 0
        (fun t => (k0 ζ).evalA t + reconstructPath m T G ζ t)) →
      wassersteinE p (law P Ξ) (law P Yh) ≤
        ENNReal.ofReal C * (∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ζ)) ∂P) ^ (1 / 2 : ℝ) +
        (∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ^ p ∂P) ^ (1 / p) := by
  have hp1 : 1 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  have hp0 : 0 < p := by linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := HRS.GF.gf_wasserstein_comparison_proof T 1 hT p hp
  refine ⟨max 1 (3 + Real.sqrt T) * C₁, by positivity, ?_⟩
  intro Ω mΩ P hP ℱ k0 hk0m M G hMm hGm Sd cost hdiff hcost hMc hM0 hGc hG0 R hRc hRm Ξ Yh hΞ hYh
  set X : ℝ → Ω → KSpace d m T := fun t ζ => k0 ζ + (M t ζ - M 0 ζ) with hXdef
  set Xb : ℝ → Ω → KSpace d m T := fun t ζ => k0 ζ + (G t ζ - G 0 ζ) with hXbdef
  have hZc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => M t ζ - M 0 ζ) (Set.Icc 0 T) := by
    filter_upwards [hMc] with ζ hζ
    exact hζ.sub continuousOn_const
  have hZbc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => G t ζ - G 0 ζ) (Set.Icc 0 T) := by
    filter_upwards [hGc] with ζ hζ
    exact hζ.sub continuousOn_const
  have hsp := hC₁ Ω P ℱ (KSpace d m T) (KSpace d m T) (s56_idEvol _) (s56_idEvol_maxHyp T) k0 k0 hk0m hk0m
    M G hMm hGm Sd cost hdiff hcost (fun t ζ => M t ζ - M 0 ζ) (fun t ζ => G t ζ - G 0 ζ) (fun _ _ => 0)
    (fun t _ => s56_isStochConv_id P M 0 t) (fun t _ => s56_isStochConv_id P G 0 t) hZc hZbc
    (Filter.Eventually.of_forall fun _ => continuousOn_const)
    (fun t => (hMm t).sub (hMm 0)) (fun t => (hGm t).sub (hGm 0)) (fun _ => measurable_const) X Xb
    (fun t _ ζ => by simp [hXdef, s56_idEvol]) (fun t _ ζ => by simp [hXbdef, s56_idEvol])
  have hz1 : ∀ ζ, ‖k0 ζ - k0 ζ‖ₑ ^ p = 0 := fun ζ => by
    simp [ENNReal.zero_rpow_of_pos hp0]
  have hz2 : ∀ ζ, ‖windowPath 0 T (fun (_ : ℝ) (_ : Ω) => (0 : KSpace d m T)) ζ‖ₑ ^ p = 0 := fun ζ => by
    have : ‖windowPath 0 T (fun (_ : ℝ) (_ : Ω) => (0 : KSpace d m T)) ζ‖ₑ = 0 :=
      le_antisymm (HRS.GF.gfb4_windowPath_enorm_le T _ ζ 0 (fun t _ => by simp)) bot_le
    rw [this, ENNReal.zero_rpow_of_pos hp0]
  have hsp' : wassersteinE p (law P (windowPath 0 T X)) (law P (windowPath 0 T Xb)) ≤
      ENNReal.ofReal C₁ * (∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ζ)) ∂P) ^ (1 / 2 : ℝ) := by
    have e1 : ∫⁻ ζ, ‖k0 ζ - k0 ζ‖ₑ ^ p ∂P = 0 := by simp only [hz1, lintegral_zero]
    have e2 : ∫⁻ ζ, ‖windowPath 0 T (fun (_ : ℝ) (_ : Ω) => (0 : KSpace d m T)) ζ‖ₑ ^ p ∂P = 0 := by
      simp only [hz2, lintegral_zero]
    rw [e1, e2, ENNReal.zero_rpow_of_pos (one_div_pos.2 hp0), mul_zero, zero_add, zero_add] at hsp
    exact hsp
  have hXm : ∀ t, Measurable (X t) := fun t => hk0m.add ((hMm t).sub (hMm 0))
  have hXbm : ∀ t, Measurable (Xb t) := fun t => hk0m.add ((hGm t).sub (hGm 0))
  have hXc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => X t ζ) (Set.Icc 0 T) := by
    filter_upwards [hZc] with ζ h
    exact continuousOn_const.add h
  have hXbc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => Xb t ζ) (Set.Icc 0 T) := by
    filter_upwards [hZbc] with ζ h
    exact continuousOn_const.add h
  have hwX : AEMeasurable (windowPath 0 T X) P :=
    HRS.GF.gfb4_aemeasurable_windowPath P hT X (fun t _ => hXm t) hXc
  have hwXb : AEMeasurable (windowPath 0 T Xb) P :=
    HRS.GF.gfb4_aemeasurable_windowPath P hT Xb (fun t _ => hXbm t) hXbc
  have hRp0 : AEMeasurable (windowPath 0 T R) P :=
    HRS.GF.gfb4_aemeasurable_windowPath P hT R (fun t _ => hRm t) hRc
  set L := s56_reconCLM (d := d) (m := m) hT with hL
  set A : Ω → OscPath d m T := fun ζ => L (windowPath 0 T X ζ) with hAdef
  set Ab : Ω → OscPath d m T := fun ζ => L (windowPath 0 T Xb ζ) with hAbdef
  set Rp : Ω → OscPath d m T := fun ζ => windowPathOf m T 0 (fun t => R t ζ) with hRpdef
  have hA : AEMeasurable A P := L.continuous.measurable.comp_aemeasurable hwX
  have hAb : AEMeasurable Ab P := L.continuous.measurable.comp_aemeasurable hwXb
  have hRp : AEMeasurable Rp P := hRp0
  have hΞ' : ∀ᵐ ζ ∂P, Ξ ζ = A ζ + Rp ζ := by
    filter_upwards [hΞ, hMc, hM0, hRc] with ζ h1 h2 h3 h4
    rw [h1]
    exact s56_key_eq hT k0 M R ζ h2 h3 h4
  have hYh' : ∀ᵐ ζ ∂P, Yh ζ = Ab ζ := by
    filter_upwards [hYh, hGc, hG0] with ζ h1 h2 h3
    rw [h1]
    have := s56_key_eq hT k0 G (fun _ _ => (0 : OscDual d m)) ζ h2 h3 continuousOn_const
    simp only [add_zero] at this
    rw [this, s56_wpo_zero, add_zero]
  have hlaw1 : law P Ξ = P.map (fun ζ => A ζ + Rp ζ) := Measure.map_congr hΞ'
  have hlaw2 : law P Yh = P.map Ab := Measure.map_congr hYh'
  rw [hlaw1, hlaw2]
  have hmap1 : P.map A = (P.map (windowPath 0 T X)).map L :=
    (AEMeasurable.map_map_of_aemeasurable L.continuous.aemeasurable hwX).symm
  have hmap2 : P.map Ab = (P.map (windowPath 0 T Xb)).map L :=
    (AEMeasurable.map_map_of_aemeasurable L.continuous.aemeasurable hwXb).symm
  have hw1 : wassersteinE p (P.map (fun ζ => A ζ + Rp ζ)) (P.map A) ≤
      (∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ^ p ∂P) ^ (1 / p) := by
    refine (wassersteinE_le_of_coupling P p hp1 (fun ζ => A ζ + Rp ζ) A (hA.add hRp) hA).trans
      (le_of_eq ?_)
    congr 1
    refine lintegral_congr fun ζ => ?_
    rw [add_sub_cancel_left, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
  have hLn : ‖L‖ ≤ 3 + Real.sqrt T := s56_reconCLM_norm_le hT
  have hw2 : wassersteinE p (P.map A) (P.map Ab) ≤
      ENNReal.ofReal (max 1 (3 + Real.sqrt T)) *
        wassersteinE p (law P (windowPath 0 T X)) (law P (windowPath 0 T Xb)) := by
    rw [hmap1, hmap2]
    refine (HRS.Main.wassersteinE_map_clm_le L p hp1 _ _).trans ?_
    gcongr
    exact hLn.trans (le_max_right _ _)
  have hmax : 0 ≤ max 1 (3 + Real.sqrt T) := le_trans zero_le_one (le_max_left _ _)
  calc wassersteinE p (P.map (fun ζ => A ζ + Rp ζ)) (P.map Ab)
      ≤ wassersteinE p (P.map (fun ζ => A ζ + Rp ζ)) (P.map A) + wassersteinE p (P.map A) (P.map Ab) :=
        wassersteinE_triangle p hp1 _ (P.map A) _
    _ ≤ (∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ^ p ∂P) ^ (1 / p) +
          ENNReal.ofReal (max 1 (3 + Real.sqrt T)) *
            wassersteinE p (law P (windowPath 0 T X)) (law P (windowPath 0 T Xb)) := add_le_add hw1 hw2
    _ ≤ (∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ^ p ∂P) ^ (1 / p) +
          ENNReal.ofReal (max 1 (3 + Real.sqrt T)) *
            (ENNReal.ofReal C₁ * (∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ζ)) ∂P) ^ (1 / 2 : ℝ)) := by
        gcongr
    _ = ENNReal.ofReal (max 1 (3 + Real.sqrt T) * C₁) *
          (∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ζ)) ∂P) ^ (1 / 2 : ℝ) +
        (∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ^ p ∂P) ^ (1 / p) := by
        rw [ENNReal.ofReal_mul hmax, mul_assoc, add_comm]

end HRS.MS.GenPath
