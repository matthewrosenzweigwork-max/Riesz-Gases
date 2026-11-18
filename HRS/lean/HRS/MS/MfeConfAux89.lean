import HRS.MS.MfeConfAux88

/-!
# S.B.1, packet F8 (part 21): the normaliser `K̄_s` and the constant `c̄_s` of the level-`k` reference along the clamped trajectory

`sb1_lv_Kb s = gibbsNormalizer k N β (ρb_s)` is positive, continuous in `s`, bounded above and below on `ℝ`;
`sb1_lv_cb s = sb1c k (ρb_s)` is continuous and bounded.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

def sb1_lv_Kb (k : Euc d → ℝ) (β : ℝ) (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ) : ℝ :=
  Whole.gibbsNormalizer k N β (Whole.withDensityReal (sb1_lv_rb hT ρ s))

def sb1_lv_cb (k : Euc d → ℝ) {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ) : ℝ := sb1c k (sb1_lv_rb hT ρ s)

/-- the clamped time as a real number -/
def sb1_lv_cl' {T : ℝ} (hT : 0 ≤ T) (s : ℝ) : ℝ := ((Set.projIcc (0 : ℝ) T hT s : Set.Icc (0 : ℝ) T) : ℝ)

theorem sb1_lv_cl'_cont {T : ℝ} (hT : 0 ≤ T) : Continuous (sb1_lv_cl' hT) :=
  continuous_subtype_val.comp (continuous_projIcc (h := hT))

theorem sb1_lv_cl'_mem {T : ℝ} (hT : 0 ≤ T) (s : ℝ) : sb1_lv_cl' hT s ∈ Set.Icc (0 : ℝ) T := (Set.projIcc (0 : ℝ) T hT s).2

theorem sb1_lv_rb_eq {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ) : sb1_lv_rb hT ρ s = ρ (sb1_lv_cl' hT s) := rfl

section Traj

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {k : Euc d → ℝ} {β : ℝ}

include H hT

theorem sb1_lv_Kb_eq (s : ℝ) :
    sb1_lv_Kb k β N hT ρ s = ∫ X : Whole.EucConfig d N, sb1Wf k β N ρ (sb1_lv_cl' hT s) X := by
  unfold sb1_lv_Kb
  rw [sb1_lv_rb_eq, sb1_gibbs_eq_Kpi H (sb1_lv_cl'_mem hT s) k β, sb1_Kpi_eq H (sb1_lv_cl'_mem hT s) k β]

theorem sb1_lv_Kb_pos (hk : Sb1KerU d D.s k) (hβ : 0 ≤ β) (hN : 1 ≤ N) (s : ℝ) : 0 < sb1_lv_Kb k β N hT ρ s := by
  have ht := sb1_lv_cl'_mem hT s
  have hd := H.tr.hd
  unfold sb1_lv_Kb
  rw [sb1_lv_rb_eq, sb1_gibbs_eq_Kpi H ht k β]
  haveI : IsProbabilityMeasure (Whole.withDensityReal (ρ (sb1_lv_cl' hT s))) :=
    HRS.MS.Thm.cb_withDensityReal_isProb (H.tr.slice _ ht).dens
  unfold sb1Kpi sb1FF
  refine integral_exp_pos ?_
  exact Integrable.of_bound (C := sb1CwR d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) β N)
    (Real.measurable_exp.comp ((sb1_En_meas hk (H.rho hd ht)).const_mul _)).aestronglyMeasurable
    (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact sb1_E_le hd H.tr.hs0 H.tr.hsd hN hβ hk (H.rho hd ht) X)

theorem sb1_lv_Kb_cont (hk : Sb1KerU d D.s k) (hβ : 0 ≤ β) (hN : 1 ≤ N) :
    Continuous (sb1_lv_Kb k β N hT ρ) := by
  have h1 := sb1_Kk_contOn H hk hβ hN
  have e : sb1_lv_Kb k β N hT ρ = fun s => (fun r => ∫ X : Whole.EucConfig d N, sb1Wf k β N ρ r X) (sb1_lv_cl' hT s) :=
    funext fun s => sb1_lv_Kb_eq H hT s
  rw [e]
  exact h1.comp_continuous (sb1_lv_cl'_cont hT) (sb1_lv_cl'_mem hT)

theorem sb1_lv_Kb_bounds (hk : Sb1KerU d D.s k) (hβ : 0 ≤ β) (hN : 1 ≤ N) :
    ∃ m M : ℝ, 0 < m ∧ ∀ s, m ≤ sb1_lv_Kb k β N hT ρ s ∧ sb1_lv_Kb k β N hT ρ s ≤ M := by
  have hc := sb1_lv_Kb_cont H hT hk hβ hN
  have hpos := sb1_lv_Kb_pos H hT hk hβ hN
  have hcpt : IsCompact (Set.Icc (0 : ℝ) T) := isCompact_Icc
  have hne : (Set.Icc (0 : ℝ) T).Nonempty := ⟨0, le_rfl, hT⟩
  obtain ⟨s0, hs0, hmin⟩ := hcpt.exists_isMinOn hne hc.continuousOn
  obtain ⟨s1, hs1, hmax⟩ := hcpt.exists_isMaxOn hne hc.continuousOn
  refine ⟨sb1_lv_Kb k β N hT ρ s0, sb1_lv_Kb k β N hT ρ s1, hpos s0, fun s => ?_⟩
  have hK : sb1_lv_Kb k β N hT ρ s = sb1_lv_Kb k β N hT ρ (sb1_lv_cl' hT s) := by
    unfold sb1_lv_Kb sb1_lv_rb
    have : (Set.projIcc (0 : ℝ) T hT (sb1_lv_cl' hT s)) = Set.projIcc (0 : ℝ) T hT s := by
      unfold sb1_lv_cl'; simp
    rw [this]
  rw [hK]
  exact ⟨hmin (sb1_lv_cl'_mem hT s), hmax (sb1_lv_cl'_mem hT s)⟩

theorem sb1_lv_cb_cont (hk : Sb1KerU d D.s k) : Continuous (sb1_lv_cb k hT ρ) := by
  have h1 := sb1_c_contOn H hk
  have e : sb1_lv_cb k hT ρ = fun s => (fun r => sb1c k (ρ r)) (sb1_lv_cl' hT s) := rfl
  rw [e]
  exact h1.comp_continuous (sb1_lv_cl'_cont hT) (sb1_lv_cl'_mem hT)

theorem sb1_lv_cb_bound (hk : Sb1KerU d D.s k) (s : ℝ) :
    |sb1_lv_cb k hT ρ s| ≤ (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) +
      sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) :=
  sb1_c_abs_le H.tr.hd H.tr.hs0 H.tr.hsd hk (sb1_lv_rb_rho H hT s)

end Traj

end HRS.MS.MfeConf
