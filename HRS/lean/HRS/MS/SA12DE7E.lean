import HRS.MS.SA12DE7D
import HRS.MS.SA12K6
import HRS.MS.SA12V3U
import HRS.MS.SA12V1

/-!
# S.A.12(c), packet E7.07 (worker S82Z2), part E: `periodic_datum_box_energy`

`sa12de7_boxJet m L F = ∑_{j ≤ m} C(m,j) ∑_{idx} ∫_{[0,L)^d} (∂^idx F)²` (the exact box jet integral, ordered indices).
`sa12de7_box_jet_perL`: for `g ∈ C^∞` supported in `B(0,L/3)`, the box jet of the periodization `perL L g` equals `jetSq m 1 g`.
`sa12de7_periodic_datum_box_energy`: along the actual `periodicDatum ζ η L ε φ` family,
`boxJet ≤ (‖φ‖_{H^m} + δ)²` for `L ≥ L₀`, `0 < ε ≤ ε₀`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12DE7

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.PDE.ToolboxRd.FourierAux
  HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Limit HRS.MH.AdjointRd.Phase2SA12Construction
  HRS.MH.AdjointRd.Phase2SA12V3 HRS.MS.ToriCoefA

variable {d : ℕ}

/-- The exact box jet integral over the period box `[0,L)^d` (ordered indices, binomial weights). -/
def sa12de7_boxJet (m : ℕ) (L : ℝ) (F : Euc d → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
    ∑ idx : Fin j → Fin d, ∫ x in periodBox d L, (partialDeriv idx F x) ^ 2

theorem sa12de7_pd_periodic {L : ℝ} {F : Euc d → ℝ}
    (hper : ∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) {j : ℕ} (idx : Fin j → Fin d)
    (x : Euc d) (k : Fin d → ℤ) :
    partialDeriv idx F (x + L • latticePt k) = partialDeriv idx F x := by
  unfold partialDeriv
  have e : (fun z => F (z + L • latticePt k)) = F := funext fun z => hper z k
  have := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := F) j (L • latticePt k) x
  rw [e] at this
  exact this.symm ▸ rfl

theorem sa12de7_box_jet_perL (m : ℕ) {L : ℝ} (hL : 0 < L) {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : ∀ y : Euc d, L / 3 ≤ ‖y‖ → g y = 0) :
    sa12de7_boxJet m L (perL L g) = jetSq m (fun _ => 1) g := by
  unfold sa12de7_boxJet jetSq
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun idx _ => ?_
  have hper := sa12k_perL_periodic L g
  -- periodicity of the squared jet
  have hΦ : ∀ (x : Euc d) (k : Fin d → ℤ),
      (fun z => (partialDeriv idx (perL L g) z) ^ 2) (x + L • latticePt k) =
        (fun z => (partialDeriv idx (perL L g) z) ^ 2) x := by
    intro x k
    simp only [sa12de7_pd_periodic hper idx x k]
  rw [← sa12v_centered_eq L hL hΦ]
  have h1 : ∫ x in centeredBox d L, (partialDeriv idx (perL L g) x) ^ 2 =
      ∫ x in centeredBox d L, (partialDeriv idx g x) ^ 2 := by
    refine setIntegral_congr_fun (sa12v_centered_meas L) fun x hx => ?_
    have hU : x ∈ tca_U L 0 := by
      intro i
      have := hx i
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, sub_zero]
      rw [abs_lt]
      constructor <;> linarith [this.1, this.2]
    have hev : perL L g =ᶠ[𝓝 x] g := by
      filter_upwards [(tca_U_isOpen L 0).mem_nhds hU] with y hy
      have := tca_perL_eq_on L hL g hgs 0 y hy
      rwa [tca_latticePt_zero, smul_zero, sub_zero] at this
    show (partialDeriv idx (perL L g) x) ^ 2 = (partialDeriv idx g x) ^ 2
    unfold partialDeriv
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds]
  rw [h1]
  have h2 : ∫ x in centeredBox d L, (partialDeriv idx g x) ^ 2 = ∫ x, (partialDeriv idx g x) ^ 2 := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hxn : L / 2 ≤ ‖x‖ := by
      have : ∃ i, ¬ (-(L / 2) ≤ x i ∧ x i < L / 2) := by
        by_contra h
        push Not at h
        exact hx h
      obtain ⟨i, hi⟩ := this
      have h4 : L / 2 ≤ |x i| := by
        by_contra h
        push Not at h
        rw [abs_lt] at h
        exact hi ⟨by linarith [h.1], by linarith [h.2]⟩
      have h5 := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at h5
      linarith
    have hev : g =ᶠ[𝓝 x] fun _ => 0 := by
      have : {y : Euc d | L / 3 < ‖y‖} ∈ 𝓝 x := (isOpen_lt continuous_const continuous_norm).mem_nhds (by show L / 3 < ‖x‖; linarith)
      filter_upwards [this] with y hy
      exact hgs y hy.le
    have h6 : partialDeriv idx g x = 0 := by
      unfold partialDeriv
      rw [(hev.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds, iteratedFDeriv_fun_zero]
      · simp
    simp [h6]
  rw [h2]
  simp

theorem sa12de7_periodic_datum_box_energy (m : ℕ) {ζ η : Euc d → ℝ}
    (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (hη : IsMollifier η) {φ : Euc d → ℝ}
    (hφ : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) φ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ ε : ℝ, 0 < ε → ε ≤ ε0 →
      sa12de7_boxJet m L (periodicDatum ζ η L ε φ) ≤
        (Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) φ) + δ) ^ 2 := by
  obtain ⟨L0, hL0, ε0, hε0, h⟩ := sa12de7_cut_mollify_norm m hζ hη hφ hδ
  refine ⟨L0, hL0, ε0, hε0, fun L hL ε hε hεle => ?_⟩
  have hL1 : 1 ≤ L := hL0.trans hL
  have hLp : 0 < L := lt_of_lt_of_le one_pos hL1
  have hε' : 0 < min ε 1 := lt_min hε one_pos
  have hli : LocallyIntegrable φ volume := hφ.1.locallyIntegrable (by norm_num)
  set g : Euc d → ℝ := fun x => ζ (L⁻¹ • x) * mollify η (min ε 1) φ x with hg
  have hgsm : ContDiff ℝ ∞ g :=
    (hζ.1.comp (contDiff_const_smul _)).mul (sa12v3_mollify_smooth hη hε' hli)
  have hgs : ∀ y : Euc d, L / 3 ≤ ‖y‖ → g y = 0 := sa12v3_g_supp hζ hLp _
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (L / 3)) fun x hx => by
      apply hgs
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
      exact hx.le
  have hbox : sa12de7_boxJet m L (periodicDatum ζ η L ε φ) = jetSq m (fun _ => 1) g :=
    sa12de7_box_jet_perL m hLp hgsm hgs
  have hnorm := h L hL ε hε hεle
  rw [sa12de7_normE_cc m hgsm hgc, sa12de7_sobolevNormSq_jet m hgsm hgc] at hnorm
  unfold sobolevNormE at hnorm
  rw [if_pos hφ, ← ENNReal.ofReal_add (Real.sqrt_nonneg _) hδ.le, ENNReal.ofReal_le_ofReal_iff
    (by positivity)] at hnorm
  rw [hbox]
  have hnn : 0 ≤ jetSq m (fun _ => 1) g := by
    rw [← sa12de7_sobolevNormSq_jet m hgsm hgc]
    exact integral_nonneg fun ξ => by
      have := HRS.PDE.ToolboxRd.FourierAux.wt_pos (d := d) ξ
      positivity
  calc jetSq m (fun _ => 1) g = Real.sqrt (jetSq m (fun _ => 1) g) ^ 2 := (Real.sq_sqrt hnn).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hnorm 2

end HRS.MS.SA12DE7
