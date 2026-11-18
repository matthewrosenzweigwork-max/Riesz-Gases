import HRS.MS.SA16RHeat13

/-!
# S.A.16 (SA16R) Heat14: the heat semigroup on `WmpSpace d (k+1) p`

`sa16r_iota`: the jet truncation `WmpSpace d (k+1) p →L WmpSpace d k p`; `sa16r_H a = Γ_a ∘ ι` is the heat operator
on `WmpSpace d (k+1) p`, a contraction (`sa16r_H_norm`) and strongly continuous at `a = 0+` (`sa16r_H_tendsto`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Heat14
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- jet truncation -/
def sa16r_iota (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] : WmpSpace d (k + 1) p →L[ℝ] WmpSpace d k p :=
  Classical.choose (jet_restriction_and_finite_lift d k (k + 1) (Nat.le_succ k) p).1

lemma sa16r_iota_wrep (k : ℕ) (G : WmpSpace d (k + 1) p) :
    wrep d k p (sa16r_iota d k p G) =ᵐ[volume] wrep d (k + 1) p G :=
  (Classical.choose_spec (jet_restriction_and_finite_lift d k (k + 1) (Nat.le_succ k) p).1).2 G

lemma sa16r_iota_Jcc (k : ℕ) (φ : ccSub d) :
    sa16r_iota d k p (sa16r_Jcc d (k + 1) p φ) = sa16r_Jcc d k p φ := by
  refine sa16r_wrep_inj d k p _ _ ?_
  rw [sa16r_Jcc_eq, sa16r_Jcc_eq]
  filter_upwards [sa16r_iota_wrep (p := p) k (sa16r_cc_elt (p := p) φ.2 (k + 1)), sa16r_cc_elt_wrep (p := p) φ.2 (k + 1),
    sa16r_cc_elt_wrep (p := p) φ.2 k] with x h1 h2 h3
  rw [h1, h2, h3]

/-- the heat operator on `WmpSpace d (k+1) p` -/
def sa16r_H (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] (a : ℝ) : WmpSpace d (k + 1) p →L[ℝ] WmpSpace d (k + 1) p :=
  (sa16r_Gam d k p a).comp (sa16r_iota d k p)

/-- sup-norm of the jet is at most the sum of the absolute components -/
lemma sa16r_jet_le_sum {F G : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (m : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun x => wJet m F x - wJet m G x) (ENNReal.ofReal p) volume ≤
      ∑ τ : WIndex d m, eLpNorm (fun x => partialDeriv τ.2 F x - partialDeriv τ.2 G x)
        (ENNReal.ofReal p) volume := by
  set comp : WIndex d m → Euc d → ℝ := fun τ x => partialDeriv τ.2 F x - partialDeriv τ.2 G x with hc
  have hcomp : ∀ τ : WIndex d m, AEStronglyMeasurable (comp τ) volume := fun τ =>
    ((sa16j_pd_smooth hF τ.2).continuous.sub (sa16j_pd_smooth hG τ.2).continuous).aestronglyMeasurable
  have hjet_aesm : AEStronglyMeasurable (fun x => wJet m F x - wJet m G x) volume :=
    ((sa16j_jet_cont hF m).sub (sa16j_jet_cont hG m)).aestronglyMeasurable
  have h1 : eLpNorm (fun x => wJet m F x - wJet m G x) (ENNReal.ofReal p) volume ≤
      eLpNorm (∑ τ : WIndex d m, fun x => ‖comp τ x‖) (ENNReal.ofReal p) volume := by
    refine eLpNorm_mono hjet_aesm fun x => ?_
    have hnn : 0 ≤ (∑ τ : WIndex d m, fun x => ‖comp τ x‖) x := by
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

/-- contraction on jets of `C_c^∞` -/
lemma sa16r_heat_contract {a : ℝ} (ha : 0 < a) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (M : ℕ) :
    eLpNorm (wJet M (sa16r_cv (sa16r_g d a) φ)) (ENNReal.ofReal p) volume ≤
      eLpNorm (wJet M φ) (ENNReal.ofReal p) volume := by
  have hp : (1 : ℝ) ≤ p := by have := (Fact.out : 2 ≤ p); linarith
  have hm0 : ∀ y, 0 ≤ ‖wJet M φ y‖ := fun y => norm_nonneg _
  have hmc : Continuous (fun y => ‖wJet M φ y‖) := (sa16j_jet_cont hφ.1 M).norm
  have hmb : ∃ B, ∀ y, ‖wJet M φ y‖ ≤ B := by
    obtain ⟨B, hB⟩ := (sa16j_jet_cont hφ.1 M).norm.bounded_above_of_compact_support
      (sa16j_jet_support hφ.2 M).norm
    exact ⟨B, fun y => by simpa using hB y⟩
  have hpt : ∀ x, ‖wJet M (sa16r_cv (sa16r_g d a) φ) x‖ ≤ sa16r_cv (sa16r_g d a) (fun y => ‖wJet M φ y‖) x := by
    intro x
    have hnn : 0 ≤ sa16r_cv (sa16r_g d a) (fun y => ‖wJet M φ y‖) x := by
      unfold sa16r_cv
      exact integral_nonneg fun z => mul_nonneg (sa16r_g_pos ha z).le (hm0 _)
    refine (pi_norm_le_iff_of_nonneg hnn).2 fun τ => ?_
    rw [Real.norm_eq_abs]
    show |partialDeriv τ.2 (sa16r_cv (sa16r_g d a) φ) x| ≤ _
    rw [sa16r_cv_pd ha hφ]
    exact sa16r_cv_abs_le (sa16r_g_int ha) (sa16s_cc_partialDeriv hφ τ.2) hm0 hmb hmc
      (fun z => le_of_eq (abs_of_pos (sa16r_g_pos ha z))) (fun y => sa16j_pd_le_jet M φ y
        (by have := τ.1.2; omega) τ.2) x
  have h1 : eLpNorm (wJet M (sa16r_cv (sa16r_g d a) φ)) (ENNReal.ofReal p) volume ≤
      eLpNorm (sa16r_cv (sa16r_g d a) (fun y => ‖wJet M φ y‖)) (ENNReal.ofReal p) volume := by
    refine eLpNorm_mono (sa16j_jet_cont (sa16r_cv_contDiff ha hφ) M).aestronglyMeasurable fun x => ?_
    refine (hpt x).trans ?_
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  refine h1.trans ((sa16r_young sa16r_g_meas hmc hp).trans ?_)
  rw [eLpNorm_norm _ (sa16j_jet_cont hφ.1 M).aestronglyMeasurable, sa16r_lint_g_one ha, one_mul]

end Heat14

end HRS.Whole.AppendixA.Phase2SA16R
