import HRS.MS.R2GenInitAux15
import HRS.MS.SuppU9Aux1

/-!
# S10.5 window comparison, packet B2: the deterministic covariation density of the window features

For a window feature family `Γ` (`S105Feat`) and the stationary probability density `ρ`, `s105Db` is the bounded bilinear form
`C̄_r = featureForm m T q (Γ(r)) (ρ dx)` (`0` off `[0,τ₀]`), a nonnegative trace-class form with `‖C̄_r‖₁ ≤ 2 d B² q`
(`u9_exists_form`), measurable in `r`; `s105Db_isDet : IsDetCovDensity τ₀ (s105Db ...)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.MP.RdRem HRS.MS.GenPath

variable {d : ℕ}

theorem s105_featureForm_meas {m T τ₀ : ℝ} (hτ : 0 ≤ τ₀) {Γ : Fin d → ℝ → Euc d → KSpace d m T}
    (h : S105Feat d m T τ₀ Γ) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (q : ℝ)
    (u v : KSpace d m T) :
    Measurable fun r : ℝ => featureForm m T q (fun a => Γ a (mrrClamp τ₀ r)) (HRS.Whole.withDensityReal ρ) u v := by
  unfold featureForm
  refine (Finset.measurable_sum _ fun a _ => ?_).const_mul _
  have : (fun r : ℝ => ∫ x, inner ℝ (Γ a (mrrClamp τ₀ r) x) u * inner ℝ (Γ a (mrrClamp τ₀ r) x) v
        ∂(HRS.Whole.withDensityReal ρ)) =
      fun r : ℝ => ∫ x, ρ x * (inner ℝ (Γ a (mrrClamp τ₀ r) x) u * inner ℝ (Γ a (mrrClamp τ₀ r) x) v) := by
    funext r
    exact mrr_integral_withDensityReal _ hρ.measurable hρ.nonneg _
  rw [this]
  have hG : Measurable fun p : ℝ × Euc d => ρ p.2 *
      (inner ℝ (Γ a (mrrClamp τ₀ p.1) p.2) u * inner ℝ (Γ a (mrrClamp τ₀ p.1) p.2) v) :=
    (hρ.measurable.comp measurable_snd).mul (((s105_feat_meas hτ h a).inner measurable_const).mul
      ((s105_feat_meas hτ h a).inner measurable_const))
  exact (hG.stronglyMeasurable.integral_prod_right').measurable

open Classical in
/-- The bounded bilinear form `C̄_r = featureForm(Γ(r), ρ dx)`, `0` off `[0,τ₀]`. -/
def s105Db {m T τ₀ : ℝ} (Γ : Fin d → ℝ → Euc d → KSpace d m T) (h : S105Feat d m T τ₀ Γ) (ν : Measure (Euc d))
    [IsFiniteMeasure ν] (q : ℝ) (hq : 0 ≤ q) (r : ℝ) : KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ :=
  if hr : r ∈ Set.Icc (0 : ℝ) τ₀ then
    Classical.choose (HRS.MS.U9.u9_exists_form (ν := ν) (Γ := fun a => Γ a r) hq
      (fun a => (h.cont_x a r hr).measurable) (B := Classical.choose h.bound)
      (fun a x => (Classical.choose_spec h.bound).2 a r hr x))
  else 0

theorem s105Db_spec {m T τ₀ : ℝ} (Γ : Fin d → ℝ → Euc d → KSpace d m T) (h : S105Feat d m T τ₀ Γ)
    (ν : Measure (Euc d)) [IsFiniteMeasure ν] (q : ℝ) (hq : 0 ≤ q) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) τ₀) :
    (∀ u v, s105Db Γ h ν q hq r u v = featureForm m T q (fun a => Γ a r) ν u v) ∧
      IsTraceClassCov (s105Db Γ h ν q hq r) ∧
      traceNormForm (s105Db Γ h ν q hq r) ≤ 2 * d * (Classical.choose h.bound) ^ 2 * q * (ν Set.univ).toReal := by
  unfold s105Db
  rw [dif_pos hr]
  exact Classical.choose_spec (HRS.MS.U9.u9_exists_form (ν := ν) (Γ := fun a => Γ a r) hq
      (fun a => (h.cont_x a r hr).measurable) (B := Classical.choose h.bound)
      (fun a x => (Classical.choose_spec h.bound).2 a r hr x))

theorem s105Db_zero {m T τ₀ : ℝ} (Γ : Fin d → ℝ → Euc d → KSpace d m T) (h : S105Feat d m T τ₀ Γ)
    (ν : Measure (Euc d)) [IsFiniteMeasure ν] (q : ℝ) (hq : 0 ≤ q) {r : ℝ} (hr : r ∉ Set.Icc (0 : ℝ) τ₀) :
    s105Db Γ h ν q hq r = 0 := by
  unfold s105Db
  rw [dif_neg hr]

theorem s105Db_isDet {m T τ₀ : ℝ} (hτ : 0 ≤ τ₀) (Γ : Fin d → ℝ → Euc d → KSpace d m T) (h : S105Feat d m T τ₀ Γ)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (q : ℝ) (hq : 0 ≤ q) :
    haveI := HRS.MS.Thm.cb_withDensityReal_isProb hρ
    IsDetCovDensity τ₀ (s105Db Γ h (HRS.Whole.withDensityReal ρ) q hq) := by
  haveI hpr := HRS.MS.Thm.cb_withDensityReal_isProb hρ
  have hm : ∀ u v : KSpace d m T, Measurable fun r => s105Db Γ h (HRS.Whole.withDensityReal ρ) q hq r u v := by
    intro u v
    have h1 := s105_featureForm_meas hτ h hρ q u v
    have : (fun r => s105Db Γ h (HRS.Whole.withDensityReal ρ) q hq r u v) = fun r =>
        if r ∈ Set.Icc (0 : ℝ) τ₀ then featureForm m T q (fun a => Γ a (mrrClamp τ₀ r))
          (HRS.Whole.withDensityReal ρ) u v else 0 := by
      funext r
      by_cases hr : r ∈ Set.Icc (0 : ℝ) τ₀
      · rw [if_pos hr, (s105Db_spec Γ h (HRS.Whole.withDensityReal ρ) q hq hr).1, mrrClamp_of_mem hr]
      · rw [if_neg hr, s105Db_zero Γ h (HRS.Whole.withDensityReal ρ) q hq hr]; rfl
    rw [this]
    exact Measurable.ite measurableSet_Icc h1 measurable_const
  refine ⟨hm, fun r hr => (s105Db_spec Γ h (HRS.Whole.withDensityReal ρ) q hq hr).2.1, ?_⟩
  have hmeas : Measurable fun r => traceNormForm (s105Db Γ h (HRS.Whole.withDensityReal ρ) q hq r) :=
    HRS.measurable_traceNormForm _ hm
  refine Measure.integrableOn_of_bounded (M := |2 * d * (Classical.choose h.bound) ^ 2 * q|) (by simp)
    hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => ?_)
  rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
  have hspec := (s105Db_spec Γ h (HRS.Whole.withDensityReal ρ) q hq hr).2.2
  rw [measure_univ] at hspec
  simp only [ENNReal.toReal_one, mul_one] at hspec
  exact hspec.trans (le_abs_self _)

end HRS.MS.R2GenInit
