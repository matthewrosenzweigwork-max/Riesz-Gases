import HRS.MS.Fp81S21WickFam9
import HRS.MS.Fp81S21WickFam10

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.Fp81.S21

local instance fp81s21_wickFam11_fact_one_le_four : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- An increment estimate transfers L² continuity to L⁴ continuity for
representatives of the same random variables. -/
theorem fp81s21_wickFam_L4_continuous_of_increment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Set ℝ) (X : ℝ → Ω → ℝ) (h4 : ∀ u, MemLp (X u) 4 P)
    (F : ℝ → Lp ℝ 2 P)
    (hag : ∀ u ∈ S, (F u : Ω → ℝ) =ᵐ[P] X u)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hb : ∀ s ∈ S, ∀ t ∈ S,
      eLpNorm (X t - X s) 4 P ≤ C * eLpNorm (X t - X s) 2 P)
    (hcont : ContinuousOn F S) :
    ContinuousOn (fun u => (h4 u).toLp (X u)) S := by
  have hnorm : ∀ s ∈ S, ∀ t ∈ S,
      ‖(h4 t).toLp (X t) - (h4 s).toLp (X s)‖ ≤
        C.toReal * ‖F t - F s‖ := by
    intro s hs t ht
    have heq : (fun ω => (F t - F s) ω) =ᵐ[P] X t - X s := by
      filter_upwards [Lp.coeFn_sub (F t) (F s), hag t ht, hag s hs] with ω hsub ht' hs'
      simp only [hsub, Pi.sub_apply, ht', hs']
    have hfin : eLpNorm (X t - X s) 2 P ≠ ∞ := by
      rw [← eLpNorm_congr_ae heq]
      exact (Lp.memLp (F t - F s)).eLpNorm_ne_top
    have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hC hfin) (hb s hs t ht)
    rw [ENNReal.toReal_mul] at hreal
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
    rw [← eLpNorm_congr_ae (p := 2) heq, ← Lp.norm_def] at hreal
    exact hreal
  apply Metric.continuousOn_iff.mpr
  intro s hs ε hε
  have hc : 0 < C.toReal + 1 := by positivity
  obtain ⟨δ, hδ, hδprop⟩ := Metric.continuousOn_iff.mp hcont s hs
    (ε / (C.toReal + 1)) (div_pos hε hc)
  refine ⟨δ, hδ, ?_⟩
  intro t ht hdist
  have hF := hδprop t ht hdist
  rw [dist_eq_norm] at hF ⊢
  have hn := hnorm s hs t ht
  have hnon : 0 ≤ ‖F t - F s‖ := norm_nonneg _
  have hε' := (lt_div_iff₀ hc).mp hF
  nlinarith

#print axioms fp81s21_wickFam_L4_continuous_of_increment
end HRS.Fp81.S21
end
