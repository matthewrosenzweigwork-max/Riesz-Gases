import HRS.MS.Fp81S21WickFam12
import Mathlib.MeasureTheory.Function.Holder

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21

local instance fp81s21_wickFam13_fact_one_le_four : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Products of continuous L⁴ families yield a continuous centered L² family. -/
theorem fp81s21_wickFam_centered_product_continuous
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Set ℝ) (F G : ℝ → Lp ℝ 4 P)
    (hF : ContinuousOn F S) (hG : ContinuousOn G S) :
    ∃ Q : ℝ → Lp ℝ 2 P, ContinuousOn Q S ∧
      ∀ u ∈ S, (Q u : Ω → ℝ) =ᵐ[P] fun ω => F u ω * G u ω -
        ∫ ω', F u ω' * G u ω' ∂P := by
  let H := (ContinuousLinearMap.mul ℝ ℝ).holderL P 4 4 2
  let V : ℝ → Lp ℝ 2 P := fun u => H (F u) (G u)
  let A : Lp ℝ 2 P := Lp.const 2 P 1
  let m : Lp ℝ 2 P → ℝ := fun v => inner ℝ A v
  let Q : ℝ → Lp ℝ 2 P := fun u => V u - Lp.const 2 P (m (V u))
  have hV : ContinuousOn V S := (H.continuous.comp_continuousOn hF).clm_apply hG
  have hm : Continuous m := (continuous_const.inner continuous_id)
  have hQ : ContinuousOn Q S := hV.sub ((Lp.constL 2 P ℝ).continuous.comp_continuousOn
    (hm.comp_continuousOn hV))
  refine ⟨Q, hQ, ?_⟩
  intro u hu
  have hVae : (V u : Ω → ℝ) =ᵐ[P] fun ω => F u ω * G u ω := by
    simpa [V, H] using (ContinuousLinearMap.coeFn_holder
      (ContinuousLinearMap.mul ℝ ℝ) (F u) (G u) (r := (2 : ℝ≥0∞)))
  have hmean : m (V u) = ∫ ω, F u ω * G u ω ∂P := by
    dsimp [m]
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := P) (c := (1 : ℝ)), hVae] with ω ha hv
    simp [A, ha, hv, RCLike.inner_apply]
  filter_upwards [Lp.coeFn_sub (V u) (Lp.const 2 P (m (V u))),
    Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := P) (c := m (V u)), hVae] with ω hs hc hv
  change (V u - Lp.const 2 P (m (V u)) : Lp ℝ 2 P) ω = _
  rw [hs]
  change (V u) ω - (Lp.const 2 P (m (V u)) : Lp ℝ 2 P) ω = _
  rw [hc, hv, hmean]
  all_goals rfl

#print axioms fp81s21_wickFam_centered_product_continuous
end HRS.Fp81.S21
end
