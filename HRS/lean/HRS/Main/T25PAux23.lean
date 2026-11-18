import HRS.Main.T25PAux22

/-!
# T25P, part 23: the law-identification hypothesis `hid` of `t25p_core_gen` for the window law of a linear solution

For a linear fluctuation solution `(Y₀, Y)` on `[0, a+T]`, the window law `Λ = law (Y^{a+·})` satisfies `hid` of
`t25p_core_gen`, for any initial law `ν₀ = law Y₀`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.Uniform.Q45 HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem t25p_hid (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) {T : ℝ} (hT : 0 < T) {a : ℝ} (ha : 0 ≤ a) {Cr cr Cmax : ℝ}
    (hCr : 0 < Cr) (hcr : 0 < cr)
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    (hEv : T25Ev m Cr cr T Cmax Vev)
    {Ω' : Type} [mΩ' : MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y₀ : Ω' → NegSobolev d m) (hY₀ : Measurable Y₀) (Y : ℝ → Ω' → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P' htr.dyn ρ m β⁻¹ (a + T) Y₀ Y)
    (ν₀ : Measure (NegSobolev d m)) (hν₀ : P'.map Y₀ = ν₀)
    (Λ : Measure (PathSp T (NegSobolev d m))) (hΛ : Λ = law P' (HRS.Main.windowPath m T a Y)) :
    ∀ (Ω₂ : Type) [mΩ₂ : MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (ℱ₂ : Filtration ℝ mΩ₂) (ξ : Ω₂ → NegSobolev d m) (G : ℝ → Ω₂ → NegSobolev d m),
      Measurable ξ →
      IsHilbertMartingaleWithCovariation P₂ ℱ₂ (a + T) G (fun r _ => covDensT m β⁻¹ (a + T) ρ r) →
      Indep (MeasurableSpace.comap ξ inferInstance)
        (⨆ τ ∈ Set.Icc (0 : ℝ) (a + T), MeasurableSpace.comap (G τ) inferInstance) P₂ →
      P₂.map ξ = ν₀ →
      ∀ Zb : ℝ → Ω₂ → NegSobolev d m,
        (∀ t ∈ Set.Icc (0 : ℝ) (a + T),
          IsStochConv P₂ Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zb t)) →
        (∀ᵐ ω ∂P₂, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T))) →
        (∀ t, Measurable (Zb t)) →
        Λ = law P₂ (windowPath a T (fun t ω => Vev t 0 (ξ ω) + Zb t ω)) := by
  intro Ω₂ mΩ₂ P₂ hP₂ ℱ₂ ξ G hξ hG hind hξlaw Zb hZb hZbc hZbm
  have hT' : 0 < a + T := by linarith
  have hplain : IsPlainEvolution Vev (a + T) := hEv.plain _ hT'.le
  have hK : 0 ≤ Cr := hCr.le
  have hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖Vev t r‖ ≤ Cr := by
    intro r t hr hrt _
    refine (hEv.decay r t hr hrt).trans ?_
    have : Real.exp (-cr * (t - r)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith
  have hCd0 : ∀ σ, σ ∉ Set.Icc 0 (a + T) → covDensT m β⁻¹ (a + T) ρ σ = 0 := by
    intro σ hσ
    simp [covDensT, hσ]
  obtain ⟨G', hG', hGc, hGz, hGG⟩ := gfb4_modify P₂ ℱ₂ hT'.le G
    (fun r => covDensT m β⁻¹ (a + T) ρ r) hCd0 hG
  have hZb' : ∀ t ∈ Set.Icc (0 : ℝ) (a + T),
      IsStochConv P₂ Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G' 0 t (Zb t) :=
    fun t ht => gfb4_isStochConv_congr P₂ Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) ht.1
      (fun τ hτ => hGG τ ⟨hτ.1, hτ.2.trans ht.2⟩) (hZb t ht)
  have hG0m : ∀ τ ∈ Set.Icc (0 : ℝ) (a + T), Measurable (G τ) := fun τ _ => measurable_of_isHM hG τ
  have hlaw : P'.map Y₀ = P₂.map ξ := by rw [hν₀, hξlaw]
  have hfdd := t25p_fdd hd htr hm hT' hdual hplain hK hKb P' P₂ (gfb4_aug P₂ ℱ₂) ξ hξ G' G hG' hGc hGz
    hG0m hGG hind Zb hZb' hZbm Y₀ hY₀ hlaw Y hY
  have hmY := hY.meas
  have hmXb : ∀ t, Measurable (fun ω' => Vev t 0 (ξ ω') + Zb t ω') := fun t =>
    (((Vev t 0).continuous).measurable.comp hξ).add (hZbm t)
  have hcXb : ∀ᵐ ω' ∂P₂, ContinuousOn (fun t => Vev t 0 (ξ ω') + Zb t ω') (Set.Icc 0 (a + T)) := by
    filter_upwards [hZbc] with ω' hω'
    exact (HRS.Uniform.Comp28.continuousOn_V_zero Vev hplain.2.2 (ξ ω')).add hω'
  have key := Q54c.toPath_law_eq (m := m) (T := T) hT.le P' P₂ (fun t ω => Y (a + t) ω)
    (fun t ω' => Vev (a + t) 0 (ξ ω') + Zb (a + t) ω') (fun t => hmY _) (fun t => hmXb _)
    (by filter_upwards [hY.cont] with ω hω using
      HRS.Uniform.Comp28.contOn_shift (T := T) ha (Y := Y) hω)
    (by filter_upwards [hcXb] with ω hω using
      HRS.Uniform.Comp28.contOn_shift (T := T) ha (Y := fun t ω' => Vev t 0 (ξ ω') + Zb t ω') hω)
    (fun p ts ks hts' => hfdd p (fun i => a + ts i) ks
      (fun i => ⟨by linarith [(hts' i).1], by linarith [(hts' i).2]⟩))
  rw [hΛ]
  refine Eq.trans key ?_
  rw [HRS.Uniform.Comp28.windowPath_shift]
  congr 1
  funext ω'
  exact toPath_eq_windowPath m T _ ω'

end HRS.T25P
