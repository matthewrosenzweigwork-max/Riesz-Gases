import HRS.MS.S111K3C2
import HRS.MS.S111K3D1

/-!
# S11.1 continuation (S11K3), B03 part D2: the transformed trace density on `[0,2T]`

`k3Hat T u Dm s = (u/T) Dm((u/T)s)` (`s ≤ T`), `Dm(u + (s - T))` (`s > T`).  If `Dm` is a trace density on `[0,u+T]` (`K3TD`)
then `k3Hat` is a trace density on `[0,2T]` (`k3_hat_td`), with the entries and the trace norms related by the change of
variables `k3_cv`.
-/

set_option autoImplicit false
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111K3

open HRS HRS.Whole HRS.Uniform HRS.MS.CovMeas
open Classical

variable {d : ℕ} {m T u : ℝ}

lemma k3_tn_smul (c : ℝ) {A : K3Bil d m T}
    (hA : BddAbove (Set.range fun p : HRS.OrthonormalPairs (KSpace d m T) => ∑ i, |A (p.1.2.1 i) (p.1.2.2 i)|)) :
    HRS.traceNormForm (c • A) = |c| * HRS.traceNormForm A := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_smul, abs_zero, zero_mul]
    exact traceNormForm_zero_eq
  · refine le_antisymm (s101_tn_smul_le c hA) ?_
    have h1 := s101_tn_smul_le (d := d) (m := m) (T := T) c⁻¹ (A := c • A) (s101_bdd_smul c hA)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, abs_inv] at h1
    have hpos : 0 < |c| := abs_pos.2 hc
    calc |c| * HRS.traceNormForm A ≤ |c| * (|c|⁻¹ * HRS.traceNormForm (c • A)) :=
          mul_le_mul_of_nonneg_left h1 hpos.le
      _ = HRS.traceNormForm (c • A) := by field_simp

/-- A family of forms with the trace-density properties on `[0,u+T]`. -/
structure K3TD (T u : ℝ) (Dm : ℝ → K3Bil d m T) : Prop where
  symm : ∀ v x y, Dm v x y = Dm v y x
  meas : ∀ x y, Measurable fun v => Dm v x y
  bdd : ∀ v ∈ Icc (0 : ℝ) (u + T), BddAbove (Set.range fun p : HRS.OrthonormalPairs (KSpace d m T) =>
    ∑ i, |Dm v (p.1.2.1 i) (p.1.2.2 i)|)
  int : IntegrableOn (fun v => HRS.traceNormForm (Dm v)) (Icc 0 (u + T))

/-- The transformed density. -/
def k3Hat (T u : ℝ) (Dm : ℝ → K3Bil d m T) : ℝ → K3Bil d m T := fun s =>
  if s ≤ T then (u / T) • Dm ((u / T) * s) else Dm (u + (s - T))

lemma k3Hat_apply (Dm : ℝ → K3Bil d m T) (s : ℝ) (x y : KSpace d m T) :
    k3Hat T u Dm s x y = k3g T u (fun v => Dm v x y) s := by
  unfold k3Hat k3g
  split_ifs <;> simp

lemma k3_entry_integrable {Dm : ℝ → K3Bil d m T} (h : K3TD T u Dm) (x y : KSpace d m T) :
    IntegrableOn (fun v => Dm v x y) (Icc 0 (u + T)) := by
  refine Integrable.mono' (h.int.mul_const (‖x‖ * ‖y‖)) (h.meas x y).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  rw [Real.norm_eq_abs]
  exact s101_abs_le_tn (h.bdd v hv) x y

lemma k3_pre {T u : ℝ} (hT : 0 < T) (hu : 0 ≤ u) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ T) :
    (u / T) * s ∈ Icc (0 : ℝ) (u + T) := by
  have hc : 0 ≤ u / T := div_nonneg hu hT.le
  refine ⟨mul_nonneg hc hs0, ?_⟩
  have : (u / T) * s ≤ (u / T) * T := mul_le_mul_of_nonneg_left hsT hc
  have e : (u / T) * T = u := by field_simp
  linarith

theorem k3_hat_td (hT : 0 < T) (hu : 0 ≤ u) {Dm : ℝ → K3Bil d m T} (h : K3TD T u Dm) :
    IsTraceDensityL1 (2 * T) (k3Hat T u Dm) := by
  have hmeas : ∀ x y : KSpace d m T, Measurable fun s => k3Hat T u Dm s x y := by
    intro x y
    have : (fun s => k3Hat T u Dm s x y) = k3g T u (fun v => Dm v x y) := funext fun s => k3Hat_apply Dm s x y
    rw [this]
    unfold k3g
    refine Measurable.ite measurableSet_Iic ?_ ?_
    · exact measurable_const.mul ((h.meas x y).comp (measurable_const.mul measurable_id))
    · exact (h.meas x y).comp (measurable_const.add (measurable_id.sub_const T))
  refine ⟨fun s x y => ?_, fun s hs => ?_, hmeas, ?_⟩
  · rw [k3Hat_apply, k3Hat_apply]
    unfold k3g
    beta_reduce
    split_ifs
    · rw [h.symm]
    · rw [h.symm]
  · by_cases hsT : s ≤ T
    · have hv := k3_pre hT hu hs.1 hsT
      have e : k3Hat T u Dm s = (u / T) • Dm ((u / T) * s) := by simp [k3Hat, hsT]
      rw [e]
      exact s101_bdd_smul _ (h.bdd _ hv)
    · have hs' : T < s := not_le.1 hsT
      have e : k3Hat T u Dm s = Dm (u + (s - T)) := by simp [k3Hat, hsT]
      rw [e]
      exact h.bdd _ ⟨by linarith, by linarith [hs.2]⟩
  · have hint := k3_integrable hT hu h.int
    refine hint.congr_fun (fun s hs => ?_) measurableSet_Icc
    by_cases hsT : s ≤ T
    · have hv := k3_pre hT hu hs.1 hsT
      have e : k3Hat T u Dm s = (u / T) • Dm ((u / T) * s) := by simp [k3Hat, hsT]
      show k3g T u (fun v => HRS.traceNormForm (Dm v)) s = HRS.traceNormForm (k3Hat T u Dm s)
      rw [e, k3_tn_smul _ (h.bdd _ hv), abs_of_nonneg (div_nonneg hu hT.le), k3g_past hsT]
    · have hs' : T < s := not_le.1 hsT
      have e : k3Hat T u Dm s = Dm (u + (s - T)) := by simp [k3Hat, hsT]
      show k3g T u (fun v => HRS.traceNormForm (Dm v)) s = HRS.traceNormForm (k3Hat T u Dm s)
      rw [e]
      simp only [k3g, hsT, if_false]

/-- The entries of the transformed density integrate to those of `Dm` over the transformed intervals. -/
theorem k3_hat_int (hT : 0 < T) (hu : 0 ≤ u) {Dm : ℝ → K3Bil d m T} (h : K3TD T u Dm) {a b M : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbH : b ≤ u + T) (hM : T ≤ M) (hMT : M ≤ 2 * T) (x y : KSpace d m T) :
    ∫ s in Ioc (k3φ T u a) (k3φ T u b) ∩ Icc 0 M, k3Hat T u Dm s x y =
      ∫ v in Ioc a b ∩ Icc 0 (u + (M - T)), Dm v x y := by
  have := (k3_cv hT hu ha hab hbH hM hMT (k3_entry_integrable h x y)).2
  simp_rw [k3Hat_apply]
  exact this

/-- The trace norms: `‖D̂_s‖₁ = k3g (‖D_·‖₁)(s)` on `[0,2T]`. -/
lemma k3_hat_tn (hT : 0 < T) (hu : 0 ≤ u) {Dm : ℝ → K3Bil d m T} (h : K3TD T u Dm) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (2 * T)) :
    HRS.traceNormForm (k3Hat T u Dm s) = k3g T u (fun v => HRS.traceNormForm (Dm v)) s := by
  by_cases hsT : s ≤ T
  · have hv := k3_pre hT hu hs.1 hsT
    have e : k3Hat T u Dm s = (u / T) • Dm ((u / T) * s) := by simp [k3Hat, hsT]
    rw [e, k3_tn_smul _ (h.bdd _ hv), abs_of_nonneg (div_nonneg hu hT.le), k3g_past hsT]
  · have e : k3Hat T u Dm s = Dm (u + (s - T)) := by simp [k3Hat, hsT]
    rw [e]
    simp only [k3g, hsT, if_false]

/-- The `lintegral` of the trace norm over the transformed interval. -/
theorem k3_hat_lint (hT : 0 < T) (hu : 0 ≤ u) {Dm : ℝ → K3Bil d m T} (h : K3TD T u Dm) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbH : b ≤ u + T) :
    ∫⁻ s in Ioc (k3φ T u a) (k3φ T u b) ∩ Icc 0 (2 * T), ENNReal.ofReal (HRS.traceNormForm (k3Hat T u Dm s)) =
      ∫⁻ v in Ioc a b ∩ Icc 0 (u + T), ENNReal.ofReal (HRS.traceNormForm (Dm v)) := by
  have hcv := k3_cv hT hu ha hab hbH (M := 2 * T) (by linarith) le_rfl h.int
  have e : u + (2 * T - T) = u + T := by ring
  rw [e] at hcv
  obtain ⟨hint, hval⟩ := hcv
  have hset : Ioc (k3φ T u a) (k3φ T u b) ∩ Icc 0 (2 * T) ⊆ Icc 0 (2 * T) := inter_subset_right
  have hmeasS : MeasurableSet (Ioc (k3φ T u a) (k3φ T u b) ∩ Icc 0 (2 * T)) :=
    measurableSet_Ioc.inter measurableSet_Icc
  have hLeq : ∀ s ∈ Ioc (k3φ T u a) (k3φ T u b) ∩ Icc 0 (2 * T),
      HRS.traceNormForm (k3Hat T u Dm s) = k3g T u (fun v => HRS.traceNormForm (Dm v)) s :=
    fun s hs => k3_hat_tn hT hu h (hset hs)
  have hnn1 : 0 ≤ᵐ[volume.restrict (Ioc (k3φ T u a) (k3φ T u b) ∩ Icc 0 (2 * T))]
      fun s => HRS.traceNormForm (k3Hat T u Dm s) := Eventually.of_forall fun s => traceNormForm_nonneg _
  have hnn2 : 0 ≤ᵐ[volume.restrict (Ioc a b ∩ Icc 0 (u + T))] fun v => HRS.traceNormForm (Dm v) :=
    Eventually.of_forall fun v => traceNormForm_nonneg _
  have hI1 : IntegrableOn (fun s => HRS.traceNormForm (k3Hat T u Dm s))
      (Ioc (k3φ T u a) (k3φ T u b) ∩ Icc 0 (2 * T)) :=
    hint.congr_fun (fun s hs => (hLeq s hs).symm) hmeasS
  have hI2 : IntegrableOn (fun v => HRS.traceNormForm (Dm v)) (Ioc a b ∩ Icc 0 (u + T)) :=
    h.int.mono_set inter_subset_right
  rw [← ofReal_integral_eq_lintegral_ofReal hI1 hnn1, ← ofReal_integral_eq_lintegral_ofReal hI2 hnn2]
  congr 1
  rw [setIntegral_congr_fun hmeasS hLeq]
  exact hval

theorem k3_hat_lint_total (hT : 0 < T) (hu : 0 ≤ u) {Dm : ℝ → K3Bil d m T} (h : K3TD T u Dm) :
    ∫⁻ s in Icc 0 (2 * T), ENNReal.ofReal (HRS.traceNormForm (k3Hat T u Dm s)) =
      ∫⁻ v in Icc 0 (u + T), ENNReal.ofReal (HRS.traceNormForm (Dm v)) := by
  have hnn1 : 0 ≤ᵐ[volume.restrict (Icc 0 (2 * T))] fun s => HRS.traceNormForm (k3Hat T u Dm s) :=
    Eventually.of_forall fun s => traceNormForm_nonneg _
  have hnn2 : 0 ≤ᵐ[volume.restrict (Icc 0 (u + T))] fun v => HRS.traceNormForm (Dm v) :=
    Eventually.of_forall fun v => traceNormForm_nonneg _
  have hI1 : IntegrableOn (fun s => HRS.traceNormForm (k3Hat T u Dm s)) (Icc 0 (2 * T)) :=
    (k3_integrable hT hu h.int).congr_fun (fun s hs => (k3_hat_tn hT hu h hs).symm) measurableSet_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hI1 hnn1, ← ofReal_integral_eq_lintegral_ofReal h.int hnn2]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Icc (fun s hs => k3_hat_tn hT hu h hs)]
  exact k3_cv_total hT hu h.int

end HRS.MS.S111K3
