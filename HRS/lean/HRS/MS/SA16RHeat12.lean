import HRS.MS.SA16RHeat11

/-!
# S.A.16 (SA16R) Heat12: continuity in the time parameter of the jets of heat convolutions

For `φ ∈ C_c^∞`, every component `∂^τ (g_a ⋆ φ)` (`|τ| ≤ k+1`) is `κ_a ⋆ u_τ` with `κ_a ∈ {g_a, ∂_i g_a}` and `u_τ`
independent of `a` (`sa16r_pd_heat_struct`); `sa16r_comp_diff_tendsto`: each component is `L^p`-continuous in `a`;
`sa16r_jet_diff_tendsto`: the `(k+1)`-jet of `g_a ⋆ φ` is `L^p`-continuous in `a`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Heat12
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16r_pd_heat_struct {φ : Euc d → ℝ} (hφ : IsCcInfty φ) {k j : ℕ} (hj : j ≤ k + 1)
    (r : Fin j → Fin d) :
    (∃ u, IsCcInfty u ∧ ∀ a : ℝ, 0 < a →
        partialDeriv r (sa16r_cv (sa16r_g d a) φ) = sa16r_cv (sa16r_g d a) u) ∨
    (∃ (i : Fin d) (u : Euc d → ℝ), IsCcInfty u ∧ ∀ a : ℝ, 0 < a →
        partialDeriv r (sa16r_cv (sa16r_g d a) φ) = sa16r_cv (sa16r_dg d a i) u) := by
  rcases Nat.lt_or_ge j (k + 1) with hlt | hge
  · left
    exact ⟨partialDeriv r φ, sa16s_cc_partialDeriv hφ r, fun a ha => sa16r_cv_pd ha hφ j r⟩
  · right
    have hjk : j = k + 1 := le_antisymm hj hge
    subst hjk
    obtain ⟨i, idx', rfl⟩ : ∃ (i : Fin d) (idx' : Fin k → Fin d), r = Fin.cons i idx' :=
      ⟨r 0, Fin.tail r, (Fin.cons_self_tail r).symm⟩
    refine ⟨i, partialDeriv idx' φ, sa16s_cc_partialDeriv hφ idx', fun a ha => ?_⟩
    funext x
    exact sa16r_cv_pd_gain ha hφ i idx' x

lemma sa16r_cv_sub_kernel {κ κ' : Euc d → ℝ} (hκ : Integrable κ) (hκ' : Integrable κ') {u : Euc d → ℝ}
    (hu : IsCcInfty u) (x : Euc d) :
    sa16r_cv κ u x - sa16r_cv κ' u x = sa16r_cv (fun z => κ z - κ' z) u x := by
  unfold sa16r_cv
  rw [← integral_sub (sa16r_cv_integrand hκ hu x) (sa16r_cv_integrand hκ' hu x)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [sub_mul]

/-- Young for a difference of kernels -/
lemma sa16r_young_diff {κ κ' : Euc d → ℝ} (hκm : Measurable κ) (hκm' : Measurable κ')
    (hκ : Integrable κ) (hκ' : Integrable κ') {u : Euc d → ℝ} (hu : IsCcInfty u) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun x => sa16r_cv κ u x - sa16r_cv κ' u x) (ENNReal.ofReal p) volume ≤
      (∫⁻ z, ‖κ z - κ' z‖ₑ) * eLpNorm u (ENNReal.ofReal p) volume := by
  have h : (fun x => sa16r_cv κ u x - sa16r_cv κ' u x) = sa16r_cv (fun z => κ z - κ' z) u :=
    funext fun x => sa16r_cv_sub_kernel hκ hκ' hu x
  rw [h]
  exact sa16r_young (hκm.sub hκm') hu.1.continuous hp

/-- each component of the jet of `g_a ⋆ φ` is `L^p`-continuous in `a` -/
lemma sa16r_comp_diff_tendsto {φ : Euc d → ℝ} (hφ : IsCcInfty φ) {k j : ℕ} (hj : j ≤ k + 1)
    (r : Fin j → Fin d) {a0 : ℝ} (ha0 : 0 < a0) :
    Tendsto (fun a : ℝ => eLpNorm (fun x => partialDeriv r (sa16r_cv (sa16r_g d a) φ) x -
      partialDeriv r (sa16r_cv (sa16r_g d a0) φ) x) (ENNReal.ofReal p) volume) (𝓝 a0) (𝓝 0) := by
  have hp : (1 : ℝ) ≤ p := by have := (Fact.out : 2 ≤ p); linarith
  have hnear : ∀ᶠ a in 𝓝 a0, 0 < a := lt_mem_nhds ha0
  rcases sa16r_pd_heat_struct hφ hj r with ⟨u, hu, h⟩ | ⟨i, u, hu, h⟩
  · have hfin : eLpNorm u (ENNReal.ofReal p) volume ≠ ⊤ := (sa16r_cc_memLp (p := p) hu).eLpNorm_lt_top.ne
    have hT := ENNReal.Tendsto.mul_const (sa16r_g_L1_cont (d := d) ha0) (Or.inr hfin)
    rw [zero_mul] at hT
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hnear] with a ha
    simp only [h a ha, h a0 ha0]
    exact sa16r_young_diff sa16r_g_meas sa16r_g_meas (sa16r_g_int ha) (sa16r_g_int ha0) hu hp
  · have hfin : eLpNorm u (ENNReal.ofReal p) volume ≠ ⊤ := (sa16r_cc_memLp (p := p) hu).eLpNorm_lt_top.ne
    have hT := ENNReal.Tendsto.mul_const (sa16r_dg_L1_cont (d := d) ha0 i) (Or.inr hfin)
    rw [zero_mul] at hT
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hnear] with a ha
    simp only [h a ha, h a0 ha0]
    exact sa16r_young_diff (sa16r_dg_cont a i).measurable (sa16r_dg_cont a0 i).measurable
      (sa16r_dg_int ha i) (sa16r_dg_int ha0 i) hu hp

/-- the `(k+1)`-jet of `g_a ⋆ φ` is `L^p`-continuous in `a` -/
lemma sa16r_jet_diff_tendsto {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (k : ℕ) {a0 : ℝ} (ha0 : 0 < a0) :
    Tendsto (fun a : ℝ => eLpNorm (fun x => wJet (k + 1) (sa16r_cv (sa16r_g d a) φ) x -
      wJet (k + 1) (sa16r_cv (sa16r_g d a0) φ) x) (ENNReal.ofReal p) volume) (𝓝 a0) (𝓝 0) := by
  have hp : (1 : ℝ) ≤ p := by have := (Fact.out : 2 ≤ p); linarith
  have hnear : ∀ᶠ a in 𝓝 a0, 0 < a := lt_mem_nhds ha0
  have hsum : Tendsto (fun a : ℝ => ∑ τ : WIndex d (k + 1), eLpNorm (fun x =>
      partialDeriv τ.2 (sa16r_cv (sa16r_g d a) φ) x - partialDeriv τ.2 (sa16r_cv (sa16r_g d a0) φ) x)
      (ENNReal.ofReal p) volume) (𝓝 a0) (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (WIndex d (k + 1))) (fun τ _ =>
      sa16r_comp_diff_tendsto (p := p) hφ (k := k) (by have := τ.1.2; omega) τ.2 ha0)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hnear] with a ha
  have hcomp : ∀ τ : WIndex d (k + 1), AEStronglyMeasurable (fun x =>
      partialDeriv τ.2 (sa16r_cv (sa16r_g d a) φ) x - partialDeriv τ.2 (sa16r_cv (sa16r_g d a0) φ) x) volume := by
    intro τ
    exact ((sa16j_pd_smooth (sa16r_cv_contDiff ha hφ) τ.2).continuous.sub
      (sa16j_pd_smooth (sa16r_cv_contDiff ha0 hφ) τ.2).continuous).aestronglyMeasurable
  set comp : WIndex d (k + 1) → Euc d → ℝ := fun τ x =>
    partialDeriv τ.2 (sa16r_cv (sa16r_g d a) φ) x - partialDeriv τ.2 (sa16r_cv (sa16r_g d a0) φ) x with hcomp_def
  have hjet_aesm : AEStronglyMeasurable (fun x => wJet (k + 1) (sa16r_cv (sa16r_g d a) φ) x -
      wJet (k + 1) (sa16r_cv (sa16r_g d a0) φ) x) volume :=
    ((sa16j_jet_cont (sa16r_cv_contDiff ha hφ) (k + 1)).sub
      (sa16j_jet_cont (sa16r_cv_contDiff ha0 hφ) (k + 1))).aestronglyMeasurable
  have h1 : eLpNorm (fun x => wJet (k + 1) (sa16r_cv (sa16r_g d a) φ) x -
      wJet (k + 1) (sa16r_cv (sa16r_g d a0) φ) x) (ENNReal.ofReal p) volume ≤
      eLpNorm (∑ τ : WIndex d (k + 1), fun x => ‖comp τ x‖) (ENNReal.ofReal p) volume := by
    refine eLpNorm_mono hjet_aesm fun x => ?_
    have hnn : 0 ≤ (∑ τ : WIndex d (k + 1), fun x => ‖comp τ x‖) x := by
      simp only [Finset.sum_apply]
      exact Finset.sum_nonneg fun τ _ => norm_nonneg _
    rw [Real.norm_of_nonneg hnn]
    refine (pi_norm_le_iff_of_nonneg hnn).2 fun τ => ?_
    simp only [Finset.sum_apply]
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ‖comp τ x‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ τ))
    exact le_of_eq rfl
  refine h1.trans ?_
  refine (eLpNorm_sum_le (by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]; exact ENNReal.ofReal_le_ofReal hp)).trans ?_
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [eLpNorm_norm _ (hcomp τ)]

end Heat12

end HRS.Whole.AppendixA.Phase2SA16R
