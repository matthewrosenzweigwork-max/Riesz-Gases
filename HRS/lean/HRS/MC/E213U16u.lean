import HRS.MC.E213U16t

/-!
# Packet e213u16, file u: the path `η^{[0,τ]}` is past measurable; the covariance increment is a linear image of it
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10 HRS.MC.E213U11

variable {d : ℕ}

section Jinc

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- On a path continuous on `[0,L]`, the covariance increment over `(u,u'] ⊆ [0,L]` is the one of the clamped path. -/
theorem u16_Jinc_eq (T : ℝ) (a : ℝ) (ha : 0 ≤ a) {L : ℝ} (hL0 : 0 ≤ L) {u u' : ℝ} (hu : 0 ≤ u) (hu' : u' ≤ L)
    (ω : gd.Ω₀) (hc : ContinuousOn (fun t => gd.η t ω) (Set.Icc 0 L)) :
    winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω)) (Set.Ioc u u') =
      winJ (regime S β₀ hE) m T a ha
        (fun v => NegSobolev.embed m (u11_cp hL0 (procWin (rLvl d) L 0 gd.η ω) v)) (Set.Ioc u u') := by
  have hc' : ContinuousOn (fun t => gd.η t ω) (Set.Icc 0 (0 + L)) := by simpa using hc
  unfold winJ
  congr 1
  refine u11_jTensor_congr _ m (a + T) measurableSet_Ioc (fun v hv hv0 => ?_)
  have hv1 : v ∈ Set.Icc (0 : ℝ) L := ⟨hv0, hv.2.trans hu'⟩
  rw [u11_cp_of_mem _ _ hv1, u11_procWin_at gd.η L 0 ω hc' hL0]
  simp

theorem u16_Wtau_past {τ : ℝ} (hτ : 0 < τ) :
    ∃ W' : gd.Ω₀ → PathSpace d (rLvl d) τ, Measurable[pastSig gd τ] W' ∧
      (fun ω => procWin (rLvl d) τ 0 gd.η ω) =ᵐ[gd.P₀] W' := by
  refine u16_path_meas (μ := gd.P₀) (W := fun ω => procWin (rLvl d) τ 0 gd.η ω) (pastSig gd τ) hτ
    fun t ht ψ hψ => ?_
  refine ⟨Xs gd τ (⟨t, ht⟩, ⟨ψ, hψ⟩), pastSig_meas_Xs gd τ _, ?_⟩
  filter_upwards [u11_eta_cont gd τ] with ω hω
  have hc' : ContinuousOn (fun t => gd.η t ω) (Set.Icc 0 (0 + τ)) := by simpa using hω
  have h := HRS.MC.E213U4.u4_pathAt_coe (procWin (rLvl d) τ 0 gd.η ω) ⟨t, ht⟩
  have h2 := u11_procWin_at gd.η τ 0 ω hc' hτ.le ⟨t, ht⟩
  simp only [] at h h2
  rw [h, h2]
  simp [Xs]

theorem u16_Jinc_past (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {u τ : ℝ} (hu : 0 ≤ u) (huτ : u ≤ τ)
    (hτ : τ ≤ a + T) (hτ0 : 0 < τ) :
    ∃ (Λ : PathSpace d (rLvl d) τ →L[ℝ] TensorDual (PathSpace d m T) 2)
      (W' : gd.Ω₀ → PathSpace d (rLvl d) τ), (∃ K : ℝ, 0 ≤ K ∧ ∀ w, ‖Λ w‖ ≤ K * ‖w‖) ∧
      Measurable[pastSig gd τ] W' ∧
      (fun ω => procWin (rLvl d) τ 0 gd.η ω) =ᵐ[gd.P₀] W' ∧
      ∀ᵐ ω ∂gd.P₀, winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω)) (Set.Ioc u τ) =
        Λ (procWin (rLvl d) τ 0 gd.η ω) := by
  obtain ⟨Λ, hΛ, hK⟩ := u16_exists_LambdaI hE T hT a ha hτ0.le hu huτ hτ
  obtain ⟨W', hW', hae⟩ := u16_Wtau_past gd hτ0
  refine ⟨Λ, W', hK, hW', hae, ?_⟩
  filter_upwards [u11_eta_cont gd τ] with ω hω
  rw [hΛ]
  exact u16_Jinc_eq gd T a ha hτ0.le hu le_rfl ω hω

/-- Domination: a.s., all the covariance increments are bounded by `C ‖η^{[0,H]}‖ (u'-u)`, and they are additive. -/
theorem u16_Jinc_ae (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ ω ∂gd.P₀,
      (∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ a + T →
        ‖winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω)) (Set.Ioc u u')‖ ≤
          C * ‖procWin (rLvl d) (a + T) 0 gd.η ω‖ * (u' - u)) ∧
      (∀ u u' u'' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ u'' → u'' ≤ a + T →
        winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω)) (Set.Ioc u u'') =
          winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω)) (Set.Ioc u u') +
          winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω)) (Set.Ioc u' u'')) := by
  obtain ⟨C, hC0, hC⟩ := u16_Jstruct hE T hT a ha
  have hH : 0 < a + T := by linarith
  refine ⟨C, hC0, ?_⟩
  filter_upwards [u11_eta_cont gd (a + T)] with ω hω
  set w := procWin (rLvl d) (a + T) 0 gd.η ω with hw
  obtain ⟨h1, h2⟩ := hC (u11_cp hH.le w) (u11_cp_continuous hH.le w).measurable ‖w‖ (u11_cp_bounds hH.le w _ _)
  refine ⟨fun u u' hu huu hu' => ?_, fun u u' u'' hu huu huu' hu'' => ?_⟩
  · rw [u16_Jinc_eq gd T a ha hH.le hu hu' ω hω]
    exact h1 u u' hu huu hu'
  · rw [u16_Jinc_eq gd T a ha hH.le hu hu'' ω hω, u16_Jinc_eq gd T a ha hH.le hu (huu'.trans hu'') ω hω,
      u16_Jinc_eq gd T a ha hH.le (hu.trans huu) hu'' ω hω]
    exact h2 u u' u'' hu huu huu' hu''

end Jinc

end HRS.MC.E213U16

end
