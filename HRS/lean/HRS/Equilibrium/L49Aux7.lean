/-
# HRS.Equilibrium.L49Aux7 — Proposition 4.9, part 7: the variance identity (`R:eq:variance-identity`)

Abstract form: for `L²` functions `f_i` such that `f_j` (`j ≠ i`) is measurable with respect to a
sub-σ-algebra `m_i`, and `T_i = E[f_i | m_i]`,
`Var(∑ f_i) = ∑_i (E f_i² - E T_i²) + ∑_i E[(F - E F)(T_i - E f_i)]`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L49

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem l49_integrable_mul {a b : Ω → ℝ} (ha : MemLp a 2 P) (hb : MemLp b 2 P) :
    Integrable (fun ω => a ω * b ω) P :=
  ha.integrable_mul hb

/-- Orthogonality of `f - E[f|m]` to `L²(m)`. -/
theorem l49_orth [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f G : Ω → ℝ}
    (hf : MemLp f 2 P) (hG : MemLp G 2 P) (hGm : StronglyMeasurable[m] G) :
    ∫ ω, G ω * (f ω - (P[f | m]) ω) ∂P = 0 := by
  have hT : MemLp (P[f | m]) 2 P := hf.condExp (by norm_num)
  have h1 : Integrable (G * f) P := hG.integrable_mul hf
  have h2 : P[G * f | m] =ᵐ[P] G * P[f | m] :=
    condExp_mul_of_stronglyMeasurable_left hGm h1 (hf.integrable (by norm_num))
  have h3 : ∫ ω, G ω * f ω ∂P = ∫ ω, G ω * (P[f | m]) ω ∂P := by
    have e1 : ∫ ω, (P[G * f | m]) ω ∂P = ∫ ω, (G * f) ω ∂P := integral_condExp hm
    have e2 : ∫ ω, (P[G * f | m]) ω ∂P = ∫ ω, (G * P[f | m]) ω ∂P := integral_congr_ae h2
    simp only [Pi.mul_apply] at e1 e2
    rw [← e1, e2]
  have hi1 : Integrable (fun ω => G ω * f ω) P := hG.integrable_mul hf
  have hi2 : Integrable (fun ω => G ω * (P[f | m]) ω) P := hG.integrable_mul hT
  have : (fun ω => G ω * (f ω - (P[f | m]) ω)) = fun ω => G ω * f ω - G ω * (P[f | m]) ω := by
    funext ω; ring
  rw [this, integral_sub hi1 hi2, h3, sub_self]

theorem l49_variance_identity [IsProbabilityMeasure P] {n : ℕ} (m : Fin n → MeasurableSpace Ω)
    (hm : ∀ i, m i ≤ mΩ) (f : Fin n → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 P)
    (hfm : ∀ i j, j ≠ i → StronglyMeasurable[m i] (f j)) :
    ∫ ω, (∑ i, f i ω - ∑ i, ∫ ω', f i ω' ∂P) ^ 2 ∂P =
      ∑ i, (∫ ω, f i ω ^ 2 ∂P - ∫ ω, ((P[f i | m i]) ω) ^ 2 ∂P) +
      ∑ i, ∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((P[f i | m i]) ω - ∫ ω', f i ω' ∂P) ∂P := by
  set M : ℝ := ∑ i, ∫ ω', f i ω' ∂P with hM
  set F : Ω → ℝ := fun ω => ∑ i, f i ω with hF
  have hFm : MemLp F 2 P := memLp_finsetSum _ fun i _ => hf i
  have hFM : MemLp (fun ω => F ω - M) 2 P := hFm.sub (memLp_const M)
  have hT : ∀ i, MemLp (P[f i | m i]) 2 P := fun i => (hf i).condExp (by norm_num)
  -- the per-index identity
  have key : ∀ i, ∫ ω, (F ω - M) * (f i ω - ∫ ω', f i ω' ∂P) ∂P =
      (∫ ω, f i ω ^ 2 ∂P - ∫ ω, ((P[f i | m i]) ω) ^ 2 ∂P) +
        ∫ ω, (F ω - M) * ((P[f i | m i]) ω - ∫ ω', f i ω' ∂P) ∂P := by
    intro i
    set T : Ω → ℝ := P[f i | m i] with hTdef
    set μi : ℝ := ∫ ω', f i ω' ∂P with hμi
    have hTi := hT i
    have hfi := hf i
    -- `F - M = (f_i - T) + G` with `G` measurable for `m_i`
    set G : Ω → ℝ := fun ω => T ω + (∑ j ∈ Finset.univ.erase i, f j ω) - M with hG
    have hGm : StronglyMeasurable[m i] G := by
      have h1 : StronglyMeasurable[m i] T := stronglyMeasurable_condExp
      have h2 : StronglyMeasurable[m i] (fun ω => ∑ j ∈ Finset.univ.erase i, f j ω) := by
        exact Finset.stronglyMeasurable_fun_sum _ fun j hj => hfm i j (Finset.ne_of_mem_erase hj)
      exact (h1.add h2).sub stronglyMeasurable_const
    have hGL : MemLp G 2 P := by
      have h2 : MemLp (fun ω => ∑ j ∈ Finset.univ.erase i, f j ω) 2 P :=
        memLp_finsetSum _ fun j _ => hf j
      exact ((hTi.add h2).sub (memLp_const M))
    have hdecomp : ∀ ω, F ω - M = (f i ω - T ω) + G ω := by
      intro ω
      have := Finset.add_sum_erase (Finset.univ : Finset (Fin n)) (fun j => f j ω) (Finset.mem_univ i)
      simp only [hF, hG]
      linarith
    have hfT : MemLp (fun ω => f i ω - T ω) 2 P := hfi.sub hTi
    have o1 := l49_orth (hm i) hfi hGL hGm
    have o2 := l49_orth (hm i) hfi hTi (stronglyMeasurable_condExp)
    -- ∫ (F-M)(f_i - T) = ∫ f_i² - ∫ T²
    have e1 : ∫ ω, (F ω - M) * (f i ω - T ω) ∂P = ∫ ω, f i ω ^ 2 ∂P - ∫ ω, (T ω) ^ 2 ∂P := by
      have h1 : ∀ ω, (F ω - M) * (f i ω - T ω) =
          (f i ω - T ω) * (f i ω - T ω) + G ω * (f i ω - T ω) := by
        intro ω; rw [hdecomp ω]; ring
      simp_rw [h1]
      rw [integral_add (l49_integrable_mul hfT hfT) (l49_integrable_mul hGL hfT), o1, add_zero]
      -- ∫ (f - T)² = ∫ f² - 2 ∫ f T + ∫ T²,  ∫ T f = ∫ T²
      have h2 : ∫ ω, T ω * f i ω ∂P = ∫ ω, (T ω) ^ 2 ∂P := by
        have hi1 : Integrable (fun ω => T ω * f i ω) P := l49_integrable_mul hTi hfi
        have hi2 : Integrable (fun ω => T ω * T ω) P := l49_integrable_mul hTi hTi
        have : (fun ω => T ω * (f i ω - T ω)) = fun ω => T ω * f i ω - T ω * T ω := by
          funext ω; ring
        rw [this, integral_sub hi1 hi2, sub_eq_zero] at o2
        rw [show (fun ω => (T ω) ^ 2) = fun ω => T ω * T ω from by funext ω; ring]
        exact o2
      have hi1 : Integrable (fun ω => f i ω * f i ω) P := l49_integrable_mul hfi hfi
      have hi2 : Integrable (fun ω => T ω * f i ω) P := l49_integrable_mul hTi hfi
      have hi3 : Integrable (fun ω => T ω * T ω) P := l49_integrable_mul hTi hTi
      have h3 : ∀ ω, (f i ω - T ω) * (f i ω - T ω) =
          f i ω * f i ω - 2 * (T ω * f i ω) + T ω * T ω := by intro ω; ring
      simp_rw [h3]
      have h4 : ∫ ω, (f i ω * f i ω - 2 * (T ω * f i ω) + T ω * T ω) ∂P =
          (∫ ω, (f i ω * f i ω - 2 * (T ω * f i ω)) ∂P) + ∫ ω, T ω * T ω ∂P :=
        integral_add (hi1.sub (hi2.const_mul 2)) hi3
      have h5 : ∫ ω, (f i ω * f i ω - 2 * (T ω * f i ω)) ∂P =
          (∫ ω, f i ω * f i ω ∂P) - ∫ ω, 2 * (T ω * f i ω) ∂P := integral_sub hi1 (hi2.const_mul 2)
      rw [h4, h5, integral_const_mul, h2]
      have e4 : ∀ ω, f i ω * f i ω = f i ω ^ 2 := fun ω => by ring
      have e5 : ∀ ω, T ω * T ω = T ω ^ 2 := fun ω => by ring
      simp_rw [e4, e5]
      ring
    have e2 : ∫ ω, (F ω - M) * (f i ω - μi) ∂P =
        ∫ ω, (F ω - M) * (f i ω - T ω) ∂P + ∫ ω, (F ω - M) * (T ω - μi) ∂P := by
      have hT' : MemLp (fun ω => T ω - μi) 2 P := hTi.sub (memLp_const μi)
      rw [← integral_add (l49_integrable_mul hFM hfT) (l49_integrable_mul hFM hT')]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only
      ring
    rw [e2, e1]
  -- sum over `i`
  have hsum : ∫ ω, (F ω - M) ^ 2 ∂P = ∑ i, ∫ ω, (F ω - M) * (f i ω - ∫ ω', f i ω' ∂P) ∂P := by
    have h1 : ∀ ω, (F ω - M) ^ 2 = ∑ i, (F ω - M) * (f i ω - ∫ ω', f i ω' ∂P) := by
      intro ω
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, sq]
    simp_rw [h1]
    rw [integral_finsetSum]
    intro i _
    exact l49_integrable_mul hFM ((hf i).sub (memLp_const _))
  have h0 : ∫ ω, (∑ i, f i ω - ∑ i, ∫ ω', f i ω' ∂P) ^ 2 ∂P = ∫ ω, (F ω - M) ^ 2 ∂P := rfl
  rw [h0, hsum]
  simp_rw [key]
  rw [Finset.sum_add_distrib]

end L49

end HRS

end
