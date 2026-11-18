import Mathlib
import HRS.Analysis.Category

/-!
# Packet COV211, abstract averaging/category scheme

Given continuous nonnegative minorants `g N` of the (possibly non-measurable) scaled distances
`ofReal (w N) * T N θ`, with interval averages bounded below eventually, we get
(1) the interval-averaged `liminf` lower bound and (2) a dense `G_δ` set of parameters where
`g N θ > q / 2` for arbitrarily large `N`.  Every bound is a lower bound through the continuous
minorant, so no measurability of `θ ↦ T N θ` is used.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MD.Cov211

/-- A countable intersection of dense `G_δ` subsets of an open interval is again one. -/
theorem inter_dense (ε : ℝ) (R : ℕ → Set ℝ)
    (h : ∀ i, R i ⊆ Ioo 0 ε ∧ IsGδ (R i) ∧ Ioo 0 ε ⊆ closure (R i)) :
    (⋂ i, R i) ⊆ Ioo 0 ε ∧ IsGδ (⋂ i, R i) ∧ Ioo 0 ε ⊆ closure (⋂ i, R i) := by
  refine ⟨fun x hx => (h 0).1 (Set.mem_iInter.1 hx 0), IsGδ.iInter fun i => (h i).2.1, ?_⟩
  set W : Set ℝ := (Icc 0 ε)ᶜ with hW
  have hWo : IsOpen W := isClosed_Icc.isOpen_compl
  have hdense : ∀ i, Dense (R i ∪ W) := by
    intro i y
    have h1 : closure W = (Ioo 0 ε)ᶜ := by
      rw [hW, closure_compl, interior_Icc]
    by_cases hy : y ∈ Ioo 0 ε
    · exact closure_mono Set.subset_union_left ((h i).2.2 hy)
    · exact closure_mono Set.subset_union_right (by rw [h1]; exact hy)
  have hG : Dense (⋂ i, (R i ∪ W)) :=
    dense_iInter_of_Gδ (fun i => (h i).2.1.union hWo.isGδ) hdense
  have hsub : Ioo 0 ε ∩ ⋂ i, (R i ∪ W) ⊆ ⋂ i, R i := by
    intro x ⟨hx1, hx2⟩
    refine Set.mem_iInter.2 fun i => ?_
    rcases Set.mem_iInter.1 hx2 i with hxi | hxi
    · exact hxi
    · exact absurd (Ioo_subset_Icc_self hx1) hxi
  exact (hG.open_subset_closure_inter isOpen_Ioo).trans (closure_mono hsub)

/-- The scheme. -/
theorem scheme (ε : ℝ) (hε : 0 < ε) (g : ℕ → ℝ → ℝ) (T : ℕ → ℝ → ℝ≥0∞) (w : ℕ → ℝ)
    (hcont : ∀ N, Continuous (g N)) (hnn : ∀ N θ, 0 ≤ g N θ)
    (hmin : ∀ N, 2 ≤ N → ∀ θ ∈ Ioo 0 ε,
      ENNReal.ofReal (g N θ) ≤ ENNReal.ofReal (w N) * T N θ)
    (q : ℝ) (hq : 0 < q)
    (havg : ∀ c d : ℝ, 0 < c → c < d → d < ε → ∀ᶠ N : ℕ in atTop, q * (d - c) ≤ ∫ θ in c..d, g N θ) :
    (∀ a b : ℝ, 0 < a → a < b → b < ε →
      ENNReal.ofReal (q * (b - a)) ≤
        liminf (fun N : ℕ => ENNReal.ofReal (w N) * ∫⁻ θ in Icc a b, T N θ) atTop) ∧
    ∃ R : Set ℝ, R ⊆ Ioo 0 ε ∧ IsGδ R ∧ Ioo 0 ε ⊆ closure R ∧
      ∀ θ ∈ R, ∀ L : ℕ, ∃ N : ℕ, L ≤ N ∧ 2 ≤ N ∧ q / 2 < g N θ := by
  constructor
  · intro a b ha hab hb
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [havg a b ha hab hb, eventually_ge_atTop 2] with N hN hN2
    have hsub : Icc a b ⊆ Ioo 0 ε := fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    calc ENNReal.ofReal (q * (b - a)) ≤ ENNReal.ofReal (∫ θ in a..b, g N θ) :=
          ENNReal.ofReal_le_ofReal hN
      _ = ENNReal.ofReal (∫ θ in Icc a b, g N θ) := by
          rw [intervalIntegral.integral_of_le hab.le, integral_Icc_eq_integral_Ioc]
      _ = ∫⁻ θ in Icc a b, ENNReal.ofReal (g N θ) := by
          rw [ofReal_integral_eq_lintegral_ofReal
            ((hcont N).continuousOn.integrableOn_Icc)
            (Filter.Eventually.of_forall fun θ => hnn N θ)]
      _ ≤ ∫⁻ θ in Icc a b, ENNReal.ofReal (w N) * T N θ := by
          refine setLIntegral_mono' measurableSet_Icc fun θ hθ => hmin N hN2 θ (hsub hθ)
      _ = ENNReal.ofReal (w N) * ∫⁻ θ in Icc a b, T N θ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · obtain ⟨R, h1, h2, h3, h4⟩ := response_category_freq 0 ε
      hε g (fun N => (hcont N).continuousOn)
      (fun N θ _ => hnn N θ) q hq (fun c d hc hcd hd => by
        refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
        filter_upwards [havg c d hc hcd hd] with N hN
        have hcd' : 0 < d - c := by linarith
        refine EReal.coe_le_coe_iff.2 ?_
        rw [le_inv_mul_iff₀ hcd']
        linarith)
    refine ⟨R, h1, h2, h3, fun θ hθ L => ?_⟩
    obtain ⟨N, hN, hlt⟩ := h4 θ hθ (max L 2)
    exact ⟨N, (le_max_left _ _).trans hN, (le_max_right _ _).trans hN, hlt⟩

end HRS.MD.Cov211
