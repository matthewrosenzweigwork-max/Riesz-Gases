import HRS.MS.SA16RHeat14

/-!
# S.A.16 (SA16R) Heat15: the heat operator on `WmpSpace d (k+1) p` is a contraction, strongly continuous at `0+`

`sa16r_H_norm`: `‖H_a G‖ ≤ ‖G‖`; `sa16r_H_tendsto`: `H_a G → G` as `a → 0+`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Heat15
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16r_cc_S_memLp {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (l : ℕ) :
    MemLp (sa16j_S d l φ) (ENNReal.ofReal p) volume := by
  have hg : MemLp (fun x => ∑ j ∈ Finset.range (l + 1), ∑ r : Fin j → Fin d, |partialDeriv r φ x|)
      (ENNReal.ofReal p) volume := by
    refine memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun r _ => ?_
    exact (sa16r_cc_memLp (p := p) (sa16s_cc_partialDeriv hφ r)).norm
  refine hg.mono' (sa16j_S_cont hφ.1 l).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sa16j_S_nonneg d l φ x)]
  exact sa16j_S_le l φ x

lemma sa16r_J_sub_norm (l : ℕ) {f f' : sa16r_S d l p} (hS : MemLp (sa16j_S d l f.1) (ENNReal.ofReal p) volume)
    (hS' : MemLp (sa16j_S d l f'.1) (ENNReal.ofReal p) volume) :
    ‖sa16r_J d l p f - sa16r_J d l p f'‖ =
      (eLpNorm (fun x => wJet l f.1 x - wJet l f'.1 x) (ENNReal.ofReal p) volume).toReal := by
  have hc1 := sa16r_J_coe (p := p) l hS
  have hc0 := sa16r_J_coe (p := p) l hS'
  show ‖(((sa16r_J d l p f : WmpSpace d l p) : WLp d l p) - ((sa16r_J d l p f' : WmpSpace d l p) : WLp d l p))‖ = _
  rw [Lp.norm_def]
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (((sa16r_J d l p f : WmpSpace d l p) : WLp d l p))
    (((sa16r_J d l p f' : WmpSpace d l p) : WLp d l p)), hc1, hc0] with x h1 h2 h3
  rw [h1]
  simp only [Pi.sub_apply, h2, h3]

lemma sa16r_H_Jcc {a : ℝ} (ha : 0 < a) (k : ℕ) (φ : ccSub d) :
    sa16r_H d k p a (sa16r_Jcc d (k + 1) p φ) = sa16r_J d (k + 1) p (sa16r_heatL d p ha k φ) := by
  unfold sa16r_H
  rw [ContinuousLinearMap.comp_apply, sa16r_iota_Jcc, sa16r_Gam_jet ha]

lemma sa16r_H_norm_cc {a : ℝ} (ha : 0 < a) (k : ℕ) (φ : ccSub d) :
    ‖sa16r_H d k p a (sa16r_Jcc d (k + 1) p φ)‖ ≤ ‖sa16r_Jcc d (k + 1) p φ‖ := by
  rw [sa16r_H_Jcc ha k φ]
  have hS : MemLp (sa16j_S d (k + 1) (sa16r_heatL d p ha k φ).1) (ENNReal.ofReal p) volume :=
    sa16r_heat_S_memLp ha φ.2 k
  rw [sa16r_J_norm (f := sa16r_heatL d p ha k φ) (k + 1) hS, sa16r_Jcc_norm]
  have hfin : eLpNorm (wJet (k + 1) φ.1) (ENNReal.ofReal p) volume ≠ ⊤ :=
    (sa16r_jet_memLp_cc φ.2 (k + 1)).eLpNorm_lt_top.ne
  exact ENNReal.toReal_mono hfin (sa16r_heat_contract (p := p) ha φ.2 (k + 1))

lemma sa16r_H_norm {a : ℝ} (ha : 0 < a) (k : ℕ) (G : WmpSpace d (k + 1) p) :
    ‖sa16r_H d k p a G‖ ≤ ‖G‖ := by
  refine (sa16r_Jcc_dense d (k + 1) p).induction_on G (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro φ
  exact sa16r_H_norm_cc ha k φ

lemma sa16r_H_opNorm {a : ℝ} (ha : 0 < a) (k : ℕ) : ‖sa16r_H d k p a‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun G => by
    rw [one_mul]; exact sa16r_H_norm ha k G

lemma sa16r_approx_id_eLp {u : Euc d → ℝ} (hu : IsCcInfty u) {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun a : ℝ => eLpNorm (fun x => sa16r_cv (sa16r_g d a) u x - u x) (ENNReal.ofReal p) volume)
      (𝓝[>] 0) (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hpe0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  have hpet : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hl := sa16r_approx_lint_tendsto hu hp
  have h2 := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0).comp hl
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha' : 0 < a := ha
  have hm : AEStronglyMeasurable (fun x => sa16r_cv (sa16r_g d a) u x - u x) volume :=
    ((sa16r_cv_contDiff ha' hu).continuous.sub hu.1.continuous).aestronglyMeasurable
  simp only [Function.comp]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpet hm, hpr]

end Heat15

end HRS.Whole.AppendixA.Phase2SA16R
