import HRS.MC.E213U4
import HRS.MC.E213U5b
import HRS.MC.E213U6
import HRS.MC.E213U1a
import HRS.MC.E213O1
import HRS.MC.E213O2
import HRS.MC.S7PIZ
import HRS.MC.S7PIM3
import HRS.MC.S7FCW12B

/-!
# Packet e213u8 (Theorem 2.13, Wave 2): the window identity at finite `N`

`window_identity_proof`: `path_Ito_proof` at horizon `a + T` for `Φ ∘ winRestr a` with the canonical future Gaussians
`canonFut`, transported to the window by the chain rule through the linear contraction `winRestr a`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U8

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

section Aux

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u8_isRS_congr {T : ℝ} {S₁ S₂ : ℝ → ℝ → ℝ → ℝ} {I : ℝ} (h : IsRS T S₁ I)
    (heq : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ u u' : ℝ, S₁ τ u u' = S₂ τ u u') : IsRS T S₂ I := by
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := h ε hε
  refine ⟨δ, hδ, fun n u τ hu hu0 huT htag hmesh => ?_⟩
  have h1 := H n u τ hu hu0 huT htag hmesh
  have : ∑ i : Fin n, S₂ (τ i) (u i.castSucc) (u i.succ) = ∑ i : Fin n, S₁ (τ i) (u i.castSucc) (u i.succ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have h0 : 0 ≤ τ i := by
      have := hu.monotone (Fin.zero_le i.castSucc)
      rw [hu0] at this
      linarith [(htag i).1]
    have hT : τ i ≤ T := by
      have := hu.monotone (Fin.le_last i.succ)
      rw [huT] at this
      linarith [(htag i).2]
    exact (heq (τ i) ⟨h0, hT⟩ _ _).symm
  rw [this]
  exact h1

theorem u8_rsLim_eq {T : ℝ} (hT : 0 < T) {S : ℝ → ℝ → ℝ → ℝ} {I : ℝ} (h : IsRS T S I) : rsLim T S = I := by
  classical
  have hex : ∃ I, IsRS T S I := ⟨I, h⟩
  unfold rsLim
  rw [dif_pos hex]
  exact HRS.MC.E213U1.isRS_unique_proof hT hex.choose_spec h

theorem u8_Iwin_spec (hE : EdgeworthHyp S β₀ m) (T a : ℝ) (ha : 0 ≤ a) (z : NegSobolev d (rLvl d)) :
    Iwin S β₀ hE T a z = initWinFun (regime S β₀ hE).D (regime S β₀ hE).ρ m (rLvl d) T a z := by
  obtain ⟨C, c, -, -, h⟩ := Classical.choose_spec (exists_Iwin S β₀ hE T)
  exact (h a ha).1 z

theorem u8_fderiv (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T))
    (y z : PathSpace d m (a + T)) :
    fderiv ℝ (heatFn (canonFut hE (a + T)) (fun w => Φ (winRestr a ha w)) τ) y z =
      fderiv ℝ (Ucan hE T a ha Φ τ) (winRestr a ha y) (winRestr a ha z) := by
  have hreg := (HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ).1 τ hτ
  have hfun : heatFn (canonFut hE (a + T)) (fun w => Φ (winRestr a ha w)) τ =
      (Ucan hE T a ha Φ τ) ∘ (winRestr a ha) := funext (heatFn_comp_winRestr hE T a ha Φ τ)
  have hd : DifferentiableAt ℝ (Ucan hE T a ha Φ τ) (winRestr a ha y) :=
    hreg.1.differentiable (by norm_num) _
  rw [hfun, fderiv_comp y hd (winRestr a ha).differentiableAt, ContinuousLinearMap.fderiv]
  rfl

theorem u8_jpair (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T))
    (y : PathSpace d m (a + T)) (zq : ℝ → NegSobolev d m) (I : Set ℝ) :
    jPair (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + T) zq I
        (iteratedFDeriv ℝ 2 (heatFn (canonFut hE (a + T)) (fun w => Φ (winRestr a ha w)) τ) y) =
      winJ (regime S β₀ hE) m T a ha zq I (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ) (winRestr a ha y)) := by
  have hreg := (HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ).1 τ hτ
  have hfun : heatFn (canonFut hE (a + T)) (fun w => Φ (winRestr a ha w)) τ =
      (Ucan hE T a ha Φ τ) ∘ (winRestr a ha) := funext (heatFn_comp_winRestr hE T a ha Φ τ)
  rw [jPair_eq_jTensor]
  unfold winJ
  rw [tensorPow'_apply, hfun,
    ContinuousLinearMap.iteratedFDeriv_comp_right (winRestr a ha) hreg.1 y (by norm_num)]

end Aux

section Identity

variable {S : PreparedData d} {β₀ m : ℝ}

theorem window_identity_proof (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (N : ℕ) (hN : 1 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization (regime S β₀ hE).D P
      (modulatedGibbs (periodicRiesz d (regime S β₀ hE).D.s) N (regime S β₀ hE).β₀
        (withDensityReal (regime S β₀ hE).ρ₀)) X₀ W X)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) :
    Integrable (fun ω => rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
        (fun v => quadFieldAt m (regime S β₀ hE).D.s (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω)) P ∧
    Integrable (fun ω => rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
        (fun v => etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v)))) P ∧
    (∀ᵐ ω ∂P, IsRS (a + T)
      (rsSumD (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha (zetaWin m (a + T) 0 P X ω) τ)
        (fun u u' => winDrift (regime S β₀ hE) m T a ha
          (fun v => quadFieldAt m (regime S β₀ hE).D.s (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω) u u'))
      (rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
        (fun v => quadFieldAt m (regime S β₀ hE).D.s (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω))) ∧
    (∀ᵐ ω ∂P, IsRS (a + T)
      (rsSumJ (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha (zetaWin m (a + T) 0 P X ω) τ)
        (fun u u' => winJ (regime S β₀ hE) m T a ha
          (fun v => etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v))) (Set.Ioc u u')))
      (rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
        (fun v => etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v))))) ∧
    ∫ ω, Φ (HRS.Main.windowZeta m T a P X ω) ∂P =
      ∫ ω, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a (zetaAt (rLvl d) P X 0 ω)) ∂P
        - (Real.sqrt N)⁻¹ * ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
            (fun v => quadFieldAt m (regime S β₀ hE).D.s (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω) ∂P
        + (1 / (2 * Real.sqrt N)) * ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ)
            (zetaWin m (a + T) 0 P X ω)
            (fun v => etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v))) ∂P := by
  classical
  have hH : 0 < a + T := by linarith
  have hm : 3 * (d : ℝ) + 8 < m := hE.m_gt
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm2 : (d : ℝ) < 2 * m := by linarith
  have hspec := HRS.MC.E213U5.e213u5_canonFut_spec hE (a + T) hH
  obtain ⟨hΦ5, -⟩ := winRestr_memCb a ha hΦ
  obtain ⟨A, J, hAi, hJi, hAR, hJR, hEq⟩ := HRS.MC.Sec7.S7PIZ.path_Ito_proof (regime S β₀ hE) m hm (a + T) hH
    (canonFut hE (a + T)) (fun u hu => (hspec u hu).1) N hN P X₀ W X hreal (fun w => Φ (winRestr a ha w)) hΦ5
  -- the Riemann--Stieltjes integrals
  have hAmain : ∀ᵐ ω ∂P, IsRS (a + T)
      (rsSumD (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha (zetaWin m (a + T) 0 P X ω) τ)
        (fun u u' => winDrift (regime S β₀ hE) m T a ha
          (fun v => quadFieldAt m (regime S β₀ hE).D.s (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω)
          u u')) (A ω) := by
    filter_upwards [hAR] with ω hω
    refine u8_isRS_congr hω (fun τ hτ u u' => ?_)
    exact u8_fderiv hE T hT a ha Φ hΦ τ hτ _ _
  have hJmain : ∀ᵐ ω ∂P, IsRS (a + T)
      (rsSumJ (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha (zetaWin m (a + T) 0 P X ω) τ)
        (fun u u' => winJ (regime S β₀ hE) m T a ha
          (fun v => etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v))) (Set.Ioc u u'))) (J ω) := by
    filter_upwards [hJR] with ω hω
    refine u8_isRS_congr hω (fun τ hτ u u' => ?_)
    exact u8_jpair hE T hT a ha Φ hΦ τ hτ _ _ _
  have hA_ae : ∀ᵐ ω ∂P, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
        (fun v => quadFieldAt m (regime S β₀ hE).D.s (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω)
        = A ω := by
    filter_upwards [hAmain] with ω hω
    exact u8_rsLim_eq hH hω
  have hJ_ae : ∀ᵐ ω ∂P, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
        (fun v => etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v))) = J ω := by
    filter_upwards [hJmain] with ω hω
    exact u8_rsLim_eq hH hω
  have hS := hreal.solution (a + T)
  have hN0 : 0 < N := hN
  -- the left side
  have hLHS : ∀ᵐ ω ∂P, HRS.Main.windowZeta m T a P X ω =
      winRestr a ha (zetaWin m (a + T) 0 P X ω) := by
    filter_upwards [hS.cont] with ω hω
    have hζ := HRS.MC.Sec7.S7FCW12.s7fcw12_zetaAt_continuousOn m hm2 P X hS.adapted hS.cont hN0 ω
      (fun i => (hω i).comp continuous_real_toNNReal) (Set.Icc 0 (a + T))
    rw [← winRestr_zetaWin m T a ha P X ω hζ]
    rfl
  -- the initial term
  have hinit : ∀ ω, winRestr a ha (initProp (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + T) (zetaAt m P X 0 ω)) =
      Iwin S β₀ hE T a (zetaAt (rLvl d) P X 0 ω) := by
    intro ω
    haveI : IsProbabilityMeasure (P.map (X (Real.toNNReal 0))) :=
      (Measure.isProbabilityMeasure_map_iff (hS.adapted _).aemeasurable).2 inferInstance
    haveI : IsProbabilityMeasure (Measure.dirac (0 : Torus d)) := inferInstance
    have hz : zetaAt m P X 0 ω = NegSobolev.embed m (zetaAt (rLvl d) P X 0 ω) :=
      (HRS.MC.E213U6.etaE_zetaE_embed_proof hE (P.map (X (Real.toNNReal 0))) (X (Real.toNNReal 0) ω)
        (Measure.dirac (0 : Torus d))).2
    rw [hz, u8_Iwin_spec hE T a ha]
    exact (initWinFun_eq_winRestr_initProp (regime S β₀ hE).D (regime S β₀ hE).ρ m (rLvl d) T a ha _
      (vprop_continuousOn_zero S β₀ hE m (a + T) hH.le _)).symm
  have hinit' : ∀ ω, heatFn (canonFut hE (a + T)) (fun w => Φ (winRestr a ha w)) 0
        (initProp (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + T) (zetaAt m P X 0 ω)) =
      Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a (zetaAt (rLvl d) P X 0 ω)) := fun ω => by
    rw [heatFn_comp_winRestr, hinit]
  refine ⟨hAi.congr (hA_ae.mono fun ω h => h.symm), hJi.congr (hJ_ae.mono fun ω h => h.symm), ?_, ?_, ?_⟩
  · filter_upwards [hAmain, hA_ae] with ω h1 h2
    rwa [h2]
  · filter_upwards [hJmain, hJ_ae] with ω h1 h2
    rwa [h2]
  · have e1 : ∫ ω, Φ (HRS.Main.windowZeta m T a P X ω) ∂P =
        ∫ ω, Φ (winRestr a ha (zetaWin m (a + T) 0 P X ω)) ∂P :=
      integral_congr_ae (hLHS.mono fun ω h => congrArg Φ h)
    have e2 : ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
        (fun v => quadFieldAt m (regime S β₀ hE).D.s (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω) ∂P
        = ∫ ω, A ω ∂P := integral_congr_ae hA_ae
    have e3 : ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
        (fun v => etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v))) ∂P
        = ∫ ω, J ω ∂P := integral_congr_ae hJ_ae
    rw [e1, e2, e3, hEq]
    simp only [hinit']

end Identity

end HRS.MC.E213U8

end
