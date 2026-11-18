import HRS.MS.SA12DE8A

/-!
# S.A.12(c), packet E7.08 (worker S82Z2), part B: the `H^m` bound for limits of periodic functions with bounded box energy

`sa12de8_Hm_of_box_energy`: smooth `L_n`-periodic `F n` (`L_n → ∞`, `boxEnergy m (L n) (F n) ≤ B²`, `∫ F n ψ → ∫ u ψ`
against all real `C_c^∞` tests, `u` locally integrable) gives `u ∈ H^m` and `sobolevNormE m u ≤ B`.
`sa12de8_Hm_of_box_energy_lim`: the version with `boxEnergy ≤ (B+δ)²` eventually, for every `δ > 0` (the datum approximation).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12DE8

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12C HRS.MS.SA12DE7

variable {d : ℕ}

theorem sa12de8_Hm_of_box_energy {m : ℕ} (F : ℕ → Euc d → ℝ) (L : ℕ → ℝ) (u : Euc d → ℝ) {B : ℝ}
    (hB0 : 0 ≤ B) (hL : ∀ n, 0 < L n) (hLt : Tendsto L atTop atTop)
    (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hper : ∀ n (x : Euc d) (k : Fin d → ℤ), F n (x + L n • latticePt k) = F n x)
    (hE : ∀ n, boxEnergy m (L n) (F n) ≤ B ^ 2)
    (hu : LocallyIntegrable u volume)
    (hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      Tendsto (fun n => ∫ x, F n x * ψ x) atTop (𝓝 (∫ x, u x * ψ x))) :
    HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) u ∧ sobolevNormE (m : ℝ) u ≤ ENNReal.ofReal B := by
  refine sa12de7_Hm_bound_of_weak_limit (m := m) F u (fun n => centeredBox d (L n)) hB0 hF ?_ ?_ ?_ hu hconv
  · intro R
    filter_upwards [hLt.eventually_gt_atTop (2 * R + 1)] with n hn x hx i
    have h1 : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 hx
    have h2 : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
    rw [Real.norm_eq_abs] at h2
    have h3 := abs_le.1 (h2.trans h1)
    constructor <;> linarith [h3.1, h3.2]
  · intro n j hj idx
    set f : Euc d → ℝ := partialDeriv idx (F n) with hf
    have hfc : Continuous f := (sa12de7_partialDeriv_contDiff (hF n) idx).continuous
    have hmeas := sa12de8_centeredBox_measurable (d := d) (L n)
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euc d) (Real.sqrt ((d : ℝ) * (L n / 2) ^ 2))).exists_bound_of_continuousOn
      hfc.continuousOn
    have hsub : centeredBox d (L n) ⊆ Metric.closedBall (0 : Euc d) (Real.sqrt ((d : ℝ) * (L n / 2) ^ 2)) :=
      fun x hx => mem_closedBall_zero_iff.2 (sa12de8_centeredBox_bounded (L n) x hx)
    have hfin : IsFiniteMeasure (volume.restrict (centeredBox d (L n))) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact (measure_mono hsub).trans_lt measure_closedBall_lt_top
    refine (memLp_indicator_iff_restrict hmeas).2 ?_
    exact MemLp.of_bound hfc.aestronglyMeasurable C
      ((ae_restrict_iff' hmeas).2 (Eventually.of_forall fun x hx => hC x (hsub hx)))
  · intro n
    calc ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
          ∑ idx : Fin j → Fin d, ∫ x, ((centeredBox d (L n)).indicator (partialDeriv idx (F n)) x) ^ 2
        = boxEnergy m (L n) (F n) := (sa12de8_boxEnergy_eq (hL n) m (hper n)).symm
      _ ≤ B ^ 2 := hE n

/-- The `H^m` bound from a box energy bound holding only eventually. -/
theorem sa12de8_Hm_of_box_energy_ev {m : ℕ} (F : ℕ → Euc d → ℝ) (L : ℕ → ℝ) (u : Euc d → ℝ) {B : ℝ}
    (hB0 : 0 ≤ B) (hL : ∀ n, 0 < L n) (hLt : Tendsto L atTop atTop)
    (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hper : ∀ n (x : Euc d) (k : Fin d → ℤ), F n (x + L n • latticePt k) = F n x)
    (hE : ∀ᶠ n in atTop, boxEnergy m (L n) (F n) ≤ B ^ 2)
    (hu : LocallyIntegrable u volume)
    (hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      Tendsto (fun n => ∫ x, F n x * ψ x) atTop (𝓝 (∫ x, u x * ψ x))) :
    HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) u ∧ sobolevNormE (m : ℝ) u ≤ ENNReal.ofReal B := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hE
  exact sa12de8_Hm_of_box_energy (fun k => F (k + N)) (fun k => L (k + N)) u hB0 (fun k => hL _)
    (hLt.comp (tendsto_add_atTop_nat N)) (fun k => hF _) (fun k => hper _) (fun k => hN _ (Nat.le_add_left N k))
    hu (fun ψ hψ => (hconv ψ hψ).comp (tendsto_add_atTop_nat N))

/-- The version with `boxEnergy ≤ (B + δ)²` eventually for every `δ > 0`. -/
theorem sa12de8_Hm_of_box_energy_lim {m : ℕ} (F : ℕ → Euc d → ℝ) (L : ℕ → ℝ) (u : Euc d → ℝ) {B : ℝ}
    (hB0 : 0 ≤ B) (hL : ∀ n, 0 < L n) (hLt : Tendsto L atTop atTop)
    (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hper : ∀ n (x : Euc d) (k : Fin d → ℤ), F n (x + L n • latticePt k) = F n x)
    (hE : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, boxEnergy m (L n) (F n) ≤ (B + δ) ^ 2)
    (hu : LocallyIntegrable u volume)
    (hconv : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      Tendsto (fun n => ∫ x, F n x * ψ x) atTop (𝓝 (∫ x, u x * ψ x))) :
    HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) u ∧ sobolevNormE (m : ℝ) u ≤ ENNReal.ofReal B := by
  have hδ : ∀ δ : ℝ, 0 < δ → HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) u ∧
      sobolevNormE (m : ℝ) u ≤ ENNReal.ofReal (B + δ) := fun δ hδ =>
    sa12de8_Hm_of_box_energy_ev F L u (by linarith) hL hLt hF hper (hE δ hδ) hu hconv
  refine ⟨(hδ 1 one_pos).1, ?_⟩
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have h := (hδ (ε : ℝ) (by exact_mod_cast hε)).2
  refine h.trans ?_
  rw [ENNReal.ofReal_add hB0 (by positivity), ENNReal.ofReal_coe_nnreal]

end HRS.MS.SA12DE8
