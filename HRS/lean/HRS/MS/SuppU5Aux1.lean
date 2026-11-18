import Mathlib
import HRS.Prob.Metrics

/-!
# Packet U5 (aux 1): finite-dimensional `W_1` machinery for `iid_init_field_rd`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.U5


/-- Per-test-function `W₁` estimate from a Lindeberg-type bound. -/
lemma u5_w1_test_bound {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → EuclideanSpace ℝ (Fin n)) (hX : Measurable X)
    (hY : Measurable Y) (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P) {Lm : ℝ}
    (hlind : ∀ {K : ℝ} {g : EuclideanSpace ℝ (Fin n) → ℝ}, Yurinskii.TestFn K g →
      |∫ ω, g (X ω) ∂P - ∫ ω, g (Y ω) ∂P| ≤ K * Lm)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh : LipschitzWith 1 h) {ε R : ℝ} (hε : 0 < ε)
    (hR : 0 < R) :
    ∫ ω, h (X ω) ∂P - ∫ ω, h (Y ω) ∂P ≤
      (∫ ω, ‖X ω‖ ^ 2 ∂P + ∫ ω, ‖Y ω‖ ^ 2 ∂P) / (4 * R) + 2 * ε * Real.sqrt n +
        2 / ε ^ 2 * Lm := by
  set u : EuclideanSpace ℝ (Fin n) → ℝ := fun x => h x - h 0
  have hu : LipschitzWith 1 u := LipschitzWith.of_dist_le_mul fun x y => by
    simpa [u, Real.dist_eq] using hh.dist_le_mul x y
  set f : EuclideanSpace ℝ (Fin n) → ℝ := fun x => max (-R) (min R (u x))
  have hfL : LipschitzWith 1 f := (hu.const_min R).const_max (-R)
  have hfc : Continuous f := hfL.continuous
  have hfR : ∀ y, |f y| ≤ R := fun y => by
    rw [abs_le]; simp only [f]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have huf : ∀ x, |u x - f x| ≤ ‖x‖ ^ 2 / (4 * R) := fun x => by
    refine clamp_err hR ?_
    have := hu.dist_le_mul x 0
    simpa [u, Real.dist_eq] using this
  set g := gsmooth ε f
  have hgc : ContDiff ℝ 2 g := contDiff_gsmooth hε hfc hfR
  have hfg : ∀ x, |f x - g x| ≤ ε * Real.sqrt n := fun x => by
    rw [abs_sub_comm]; exact gsmooth_sub_le hε hfc hfR hfL x
  have hTF : Yurinskii.TestFn (1 * (2 / ε ^ 2)) g := by
    refine ⟨hgc, by positivity, ⟨R, abs_gsmooth_le hε hfc hfR⟩,
      ⟨1, norm_fderiv_gsmooth_le hε hfc hfR hfL⟩,
      ⟨Real.sqrt n / ε, norm_fderiv_fderiv_gsmooth_le hε hfc hfR hfL⟩, ?_⟩
    intro x y v
    exact hess_gsmooth_lip hε hfc hfR (c := 1) zero_le_one
      (fun x y => by simpa [Real.dist_eq, dist_eq_norm] using hfL.dist_le_mul x y) x y v
  have hXi : Integrable (fun ω => ‖X ω‖) P := (hX2.integrable one_le_two).norm
  have hYi : Integrable (fun ω => ‖Y ω‖) P := (hY2.integrable one_le_two).norm
  have hX2i : Integrable (fun ω => ‖X ω‖ ^ 2) P := hX2.integrable_norm_pow two_ne_zero
  have hY2i : Integrable (fun ω => ‖Y ω‖ ^ 2) P := hY2.integrable_norm_pow two_ne_zero
  have hhX := integrable_lip_comp P hh hX hXi
  have hhY := integrable_lip_comp P hh hY hYi
  have hgb : ∀ z, |g z| ≤ R := abs_gsmooth_le hε hfc hfR
  have hgX : Integrable (fun ω => g (X ω)) P :=
    integrable_comp_of_continuous P hgc.continuous hgb hX.aemeasurable
  have hgY : Integrable (fun ω => g (Y ω)) P :=
    integrable_comp_of_continuous P hgc.continuous hgb hY.aemeasurable
  have hpt : ∀ ω, h (X ω) - h (Y ω) ≤
      (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2) / (4 * R) + 2 * ε * Real.sqrt n + (g (X ω) - g (Y ω)) := by
    intro ω
    have a1 := abs_le.1 (huf (X ω))
    have a2 := abs_le.1 (huf (Y ω))
    have a3 := abs_le.1 (hfg (X ω))
    have a4 := abs_le.1 (hfg (Y ω))
    have e : h (X ω) - h (Y ω) = u (X ω) - u (Y ω) := by simp [u]
    rw [e, add_div]
    linarith [a1.2, a2.1, a3.2, a4.1]
  have hint : ∫ ω, h (X ω) ∂P - ∫ ω, h (Y ω) ∂P ≤
      (∫ ω, ‖X ω‖ ^ 2 ∂P + ∫ ω, ‖Y ω‖ ^ 2 ∂P) / (4 * R) + 2 * ε * Real.sqrt n +
        (∫ ω, g (X ω) ∂P - ∫ ω, g (Y ω) ∂P) := by
    have hc : ∫ _ω, (2 * ε * Real.sqrt n) ∂P = 2 * ε * Real.sqrt n := by simp
    rw [← integral_sub hhX hhY, ← integral_sub hgX hgY, ← integral_add hX2i hY2i,
      ← integral_div, ← hc,
      ← integral_add (f := fun ω => (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2) / (4 * R))
        (g := fun _ => 2 * ε * Real.sqrt n) ((hX2i.add hY2i).div_const _) (integrable_const _),
      ← integral_add (f := fun ω => (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2) / (4 * R) + 2 * ε * Real.sqrt n)
        (g := fun ω => g (X ω) - g (Y ω))
        (((hX2i.add hY2i).div_const _).add (integrable_const _)) (hgX.sub hgY)]
    exact integral_mono (hhX.sub hhY)
      ((((hX2i.add hY2i).div_const _).add (integrable_const _)).add (hgX.sub hgY)) hpt
  have hl := (le_abs_self _).trans (hlind hTF)
  have : 1 * (2 / ε ^ 2) * Lm = 2 / ε ^ 2 * Lm := by ring
  linarith


open Yurinskii in
/-- `W₁` distance between a sum of i.i.d. centered vectors and its Gaussian analogue. -/
theorem u5_w1_iid_gauss {n N : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ρ]
    (h0 : ∀ c, ∫ x, x c ∂ρ = 0) (h3 : Integrable (fun x => ‖x‖ ^ 3) ρ) {ε : ℝ} (hε : 0 < ε) :
    wassersteinE 1 ((Measure.pi fun _ : Fin N => ρ).map (fun p => ∑ i, p i))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) (∑ _i : Fin N, momentMatrix ρ)) ≤
    ENNReal.ofReal (2 * ε * Real.sqrt n +
      2 / ε ^ 2 * ((2 + c4 / 2) * (N * ∫ x, ‖x‖ ^ 3 ∂ρ))) := by
  set G := multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) (∑ _i : Fin N, momentMatrix ρ)
  have h2ρ : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) ρ :=
    (integrable_norm_of_pow3 (P := ρ) (Y := id) measurable_id h3).2
  have hQ : (momentMatrix ρ).PosSemidef := momentMatrix_posSemidef _ h2ρ
  have hQs : (∑ _i : Fin N, momentMatrix ρ).PosSemidef :=
    Matrix.posSemidef_sum _ fun _ _ => hQ
  have : IsProbabilityMeasure G := inferInstance
  let P : Measure ((Fin N → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n)) :=
    (Measure.pi fun _ : Fin N => ρ).prod G
  let X : (Fin N → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun ω => ∑ i, ω.1 i
  let Y : (Fin N → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun ω => ω.2
  have hXm : Measurable X :=
    Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_fst
  have hYm : Measurable Y := measurable_snd
  have hmemρ : MemLp (id : EuclideanSpace ℝ (Fin n) → _) 2 ρ :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).2 h2ρ
  have hmemG : MemLp (id : EuclideanSpace ℝ (Fin n) → _) 2 G := IsGaussian.memLp_two_id
  have hmp1 : ∀ i : Fin N, MeasurePreserving (fun ω : (Fin N → EuclideanSpace ℝ (Fin n)) ×
      EuclideanSpace ℝ (Fin n) => ω.1 i) P ρ := fun i =>
    (measurePreserving_eval (fun _ : Fin N => ρ) i).comp
      (measurePreserving_fst (μ := Measure.pi fun _ : Fin N => ρ) (ν := G))
  have hX2 : MemLp X 2 P := by
    have : X = ∑ i : Fin N, (fun ω : (Fin N → EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n) => ω.1 i) := by
      funext ω; simp [X]
    rw [this]
    exact memLp_finsetSum' _ fun i _ => hmemρ.comp_measurePreserving (hmp1 i)
  have hY2 : MemLp Y 2 P :=
    hmemG.comp_measurePreserving (measurePreserving_snd (μ := Measure.pi fun _ : Fin N => ρ) (ν := G))
  have hlawY : P.map Y = G := by
    have := (measurePreserving_snd (μ := Measure.pi fun _ : Fin N => ρ) (ν := G)).map_eq
    exact this
  have hlawX : P.map X = (Measure.pi fun _ : Fin N => ρ).map (fun p => ∑ i, p i) := by
    have hsm : Measurable (fun p : Fin N → EuclideanSpace ℝ (Fin n) => ∑ i, p i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    have e : X = (fun p : Fin N → EuclideanSpace ℝ (Fin n) => ∑ i, p i) ∘ Prod.fst := rfl
    rw [e, ← Measure.map_map hsm measurable_fst]
    congr 1
    exact (measurePreserving_fst (μ := Measure.pi fun _ : Fin N => ρ) (ν := G)).map_eq
  have hlind : ∀ {K : ℝ} {g : EuclideanSpace ℝ (Fin n) → ℝ}, TestFn K g →
      |∫ ω, g (X ω) ∂P - ∫ ω, g (Y ω) ∂P| ≤ K * ((2 + c4 / 2) * (N * ∫ x, ‖x‖ ^ 3 ∂ρ)) := by
    intro K g hg
    have e1 : ∫ ω, g (X ω) ∂P = ∫ x, g x ∂((Measure.pi fun _ : Fin N => ρ).map
        (fun p => ∑ i, p i)) := by
      rw [← hlawX, integral_map hXm.aemeasurable hg.measurable.aestronglyMeasurable]
    have e2 : ∫ ω, g (Y ω) ∂P = ∫ x, g x ∂G := by
      rw [← hlawY, integral_map hYm.aemeasurable hg.measurable.aestronglyMeasurable]
    rw [e1, e2]
    have := lindeberg_gauss hg (fun _ : Fin N => ρ) (fun i c => h0 c) (fun i => h3)
    refine this.trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdual := wassersteinE_one_le_of_dual P X Y hXm hYm hX2 hY2
    (2 * ε * Real.sqrt n + 2 / ε ^ 2 * ((2 + c4 / 2) * (N * ∫ x, ‖x‖ ^ 3 ∂ρ))) (by
      intro h hh
      refine le_of_forall_pos_le_add fun η hη => ?_
      set m := ∫ ω, ‖X ω‖ ^ 2 ∂P + ∫ ω, ‖Y ω‖ ^ 2 ∂P
      have hm0 : 0 ≤ m := add_nonneg (integral_nonneg fun _ => by positivity)
        (integral_nonneg fun _ => by positivity)
      have hR : 0 < m / (4 * η) + 1 := by positivity
      have := u5_w1_test_bound P X Y hXm hYm hX2 hY2 hlind hh hε hR
      have hmR : m / (4 * (m / (4 * η) + 1)) ≤ η := by
        rw [div_le_iff₀ (by positivity)]
        have : η * (4 * (m / (4 * η) + 1)) = m + 4 * η := by field_simp
        rw [this]; linarith
      linarith)
  have e1 : law P X = (Measure.pi fun _ : Fin N => ρ).map (fun p => ∑ i, p i) := hlawX
  have e2 : law P Y = G := hlawY
  rw [e1, e2] at hdual
  exact hdual

end HRS.U5
