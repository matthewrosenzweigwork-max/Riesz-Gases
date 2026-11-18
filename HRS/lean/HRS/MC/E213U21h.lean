import HRS.MC.E213U21g

/-!
# Packet e213u21 (part h): the crude bound for `errVal` and the real-analysis constructions of the sequences

* `u21_err_crude`: `errVal ≤ 2 √N + C/6` if `‖Kproj a‖ ≤ C`;
* `u21_sup_construction`: from a uniformly small family of nonnegative values to a null sequence `A`;
* `u21_tendsto_exp`: `exp(-c R) → 0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U21

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

section Crude

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u21_err_crude (T : ℝ) (C : ℝ) (hC : ∀ a : ℝ, 0 ≤ a → ‖gd.Kproj T a‖ ≤ C) {N : ℕ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N)
    (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : Φ ∈ CbUnitBall (PathSpace d m T) 5) :
    gd.errVal T N a Φ P X ≤ 2 * Real.sqrt N + C / 6 := by
  have habs : ∀ z, |Φ z| ≤ 1 := by
    intro z
    have := HRS.MC.E213U6.u6_norm_iteratedFDeriv_le hΦ (j := 0) (by norm_num) z
    rw [norm_iteratedFDeriv_zero] at this
    simpa using this
  have h1 := HRS.MC.E213U6.u6_abs_integral_law_le P (HRS.Main.windowZeta m T a P X) Φ habs
  have h2 := HRS.MC.E213U6.u6_abs_integral_law_le gd.P₀ (gd.Zwin T a) Φ habs
  have hKa : ‖gd.Kproj T a‖ ≤ C := hC a ha
  have h3 : |∫ ω, ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
      (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) ∂gd.P₀| ≤ C := by
    have := norm_integral_le_of_norm_le_const (μ := gd.P₀)
      (f := fun ω => ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
        (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω))) (C := C)
      (Filter.Eventually.of_forall fun ω => by
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        have h4 := HRS.MC.E213U6.u6_norm_iteratedFDeriv_le hΦ (j := 3) (by norm_num) (gd.Zwin T a ω)
        have h5 : ‖((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)‖ ≤ C := hKa
        calc _ ≤ C * 1 := mul_le_mul h5 h4 (norm_nonneg _)
              ((norm_nonneg ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)).trans h5)
          _ = C := mul_one C)
    rw [Real.norm_eq_abs] at this
    simpa using this
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hKa
  unfold GaussData.errVal
  have hs : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  generalize (∫ z, Φ z ∂(law P (HRS.Main.windowZeta m T a P X))) = A at h1
  generalize (∫ z, Φ z ∂(law gd.P₀ (gd.Zwin T a))) = B at h2
  generalize (∫ ω, ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
    (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) ∂gd.P₀) = Cc at h3
  have e1 : |Real.sqrt N * (A - B)| ≤ Real.sqrt N * 2 := by
    rw [abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left ((abs_sub A B).trans (by linarith)) hs
  have e2 : |(1 / 6 : ℝ) * Cc| ≤ C / 6 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6)]
    linarith
  calc _ ≤ |Real.sqrt N * (A - B)| + |(1 / 6 : ℝ) * Cc| := abs_sub _ _
    _ ≤ Real.sqrt N * 2 + C / 6 := add_le_add e1 e2
    _ = _ := by ring

end Crude

theorem u21_sup_construction (V : ℕ → Set ℝ) (hV0 : ∀ N, ∀ x ∈ V N, 0 ≤ x)
    (hV : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ x ∈ V N, x ≤ ε) (g : ℕ → ℝ) (hg : ∀ N, 0 ≤ g N) :
    ∃ (A : ℕ → ℝ) (n0 : ℕ), (∀ N, 0 ≤ A N) ∧ Tendsto A atTop (𝓝 0) ∧ (∀ N, n0 ≤ N → ∀ x ∈ V N, x ≤ A N) ∧
      (∀ N, N < n0 → A N = g N) := by
  classical
  obtain ⟨n0, hn0⟩ := hV 1 one_pos
  refine ⟨fun N => if n0 ≤ N then max (sSup (V N)) 0 else g N, n0, ?_, ?_, ?_, ?_⟩
  · intro N
    dsimp only
    split_ifs
    · exact le_max_right _ _
    · exact hg N
  · rw [tendsto_order]
    refine ⟨fun a' ha' => Eventually.of_forall fun N => ?_, fun a' ha' => ?_⟩
    · split_ifs
      · exact lt_of_lt_of_le ha' (le_max_right _ _)
      · exact lt_of_lt_of_le ha' (hg N)
    · obtain ⟨N₁, hN₁⟩ := hV (a' / 2) (by linarith)
      refine eventually_atTop.2 ⟨max N₁ n0, fun N hN => ?_⟩
      have hn : n0 ≤ N := (le_max_right _ _).trans hN
      rw [if_pos hn]
      refine lt_of_le_of_lt (max_le (Real.sSup_le (fun x hx => hN₁ N ((le_max_left _ _).trans hN) x hx)
        (by linarith)) (by linarith)) (by linarith)
  · intro N hN x hx
    dsimp only
    rw [if_pos hN]
    exact (le_csSup ⟨1, fun y hy => hn0 N hN y hy⟩ hx).trans (le_max_left _ _)
  · intro N hN
    dsimp only
    rw [if_neg (not_le.2 hN)]

theorem u21_tendsto_exp {c : ℝ} (hc : 0 < c) : Tendsto (fun R : ℕ => Real.exp (-c * R)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℕ => c * (R : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  refine this.congr fun R => ?_
  simp only [Function.comp, neg_mul]

end HRS.MC.E213U21

end
