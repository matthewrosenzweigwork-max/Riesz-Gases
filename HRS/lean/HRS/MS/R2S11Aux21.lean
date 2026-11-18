import HRS.MS.R2S11Aux20

/-!
# S11.2 (a) from S11.1, the Gaussian comparison and the cubic-tensor norm bound
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2S11

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s11_partA_of_h11 (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β γ : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) (T : ℝ) (hT : 0 < T) (lam : ℝ)
    (hlam : 0 < lam)
    (h11 : type_of% (r2_tensor_relaxation hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam))
    (hG : S11GaussCompare d s a β γ T lam) (hK : S11KappaBound d s a β γ T lam) :
    S11PartA d s a β γ T lam := by
  obtain ⟨c, hc, C, hC⟩ := h11
  obtain ⟨K, hK⟩ := hK
  set Cp : ℝ := max C 0 with hCp
  set K0 : ℝ := max K 0 with hK0
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  have hK00 : 0 ≤ K0 := le_max_right _ _
  refine ⟨c, hc, Cp * (1 + K0), ?_⟩
  intro ρβ hρ hP κγ κβ h1 h2 Ω' Ω'' _ _ P' P'' _ _ Zγ Zβ hZ1 hZ2 N hN Ω _ P _ X₀ W X εN hreal hlaw hε u hu Φ hΦ
  set e1 : ℝ := Real.exp (-2 * (lam / β) * u) with he1
  set e2 : ℝ := Real.exp (-c * u) with he2
  have he10 : 0 ≤ e1 := (Real.exp_pos _).le
  have he20 : 0 ≤ e2 := (Real.exp_pos _).le
  have hwm : AEMeasurable (processWindow (wholeSpaceIndex d) T u Zγ) P' :=
    s11_window_aemeas P' (hZ1 (u + T)) hT.le hu le_rfl
  have hδ_ok : ∀ M : (R2X d T) [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 →
      |∫ ζ, M ![processWindow (wholeSpaceIndex d) T u Zγ ζ, processWindow (wholeSpaceIndex d) T u Zγ ζ] ∂P' -
        ∫ ζ, M ![processWindow (wholeSpaceIndex d) T 0 Zβ ζ, processWindow (wholeSpaceIndex d) T 0 Zβ ζ] ∂P''| ≤
        Cp * e1 := fun M hM =>
    ((hC ρβ hρ hP).1 P' P'' Zγ Zβ hZ1 hZ2 u hu M hM).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) he10)
  have hAB := hG ρβ hρ hP Φ (hΦ.1.of_le (by norm_num)) 1 (Cp * e1)
    (fun x => s11_cbUnit_bound hΦ (by norm_num) x) P' P'' Zγ Zβ hZ1 hZ2 u hu hδ_ok
  obtain ⟨hFc, hFb⟩ := s11_cubic_F hΦ.1 (κβ : TensorDual (R2X d T) 3)
  have hκβ : ‖(κβ : TensorDual (R2X d T) 3)‖ ≤ K0 :=
    (hK ρβ hρ hP κβ h2).trans (le_max_left _ _)
  have hAB' := hG ρβ hρ hP (fun x => (κβ : TensorDual (R2X d T) 3) (iteratedFDeriv ℝ 3 Φ x)) hFc
    ‖(κβ : TensorDual (R2X d T) 3)‖ (Cp * e1)
    (fun x => (hFb x).trans (by
      have := s11_cbUnit_bound hΦ (by norm_num : 5 ≤ 5) x
      nlinarith [norm_nonneg (κβ : TensorDual (R2X d T) 3)])) P' P'' Zγ Zβ hZ1 hZ2 u hu hδ_ok
  have hr1 := s11_cubic_diff_bound P' _ hwm (κγ u) κβ hΦ
  have hr2 : ‖κγ u - κβ‖ ≤ Cp * e2 :=
    ((hC ρβ hρ hP).2 u hu (κγ u) κβ (h1 u hu) h2).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) he20)
  have hε' := hε u hu Φ hΦ
  have hsN : 1 ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]; exact_mod_cast (by omega : 1 ≤ N)
  set A : ℝ := ∫ ζ, Φ (processWindow (wholeSpaceIndex d) T u Zγ ζ) ∂P' with hA
  set B : ℝ := ∫ ζ, Φ (processWindow (wholeSpaceIndex d) T 0 Zβ ζ) ∂P'' with hB
  set a1 : ℝ := ∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T u P X ζ) ∂P with ha1
  set Eγ : ℝ := r2CubicExpect P' (processWindow (wholeSpaceIndex d) T u Zγ) (κγ u) Φ with hEγ
  set Eκ : ℝ := r2CubicExpect P' (processWindow (wholeSpaceIndex d) T u Zγ) κβ Φ with hEκ
  set Eβ : ℝ := r2CubicExpect P'' (processWindow (wholeSpaceIndex d) T 0 Zβ) κβ Φ with hEβ
  have key := s11_alg (s := Real.sqrt N) (p := Real.sqrt N * (a1 - A) - 1 / 6 * Eγ) (q := A - B)
    (r := Eγ - Eκ) (t := Eκ - Eβ) (εN := εN) (δ := Cp * e1) (C := Cp) (e1 := e1) (e2 := e2) (K0 := K0)
    hsN hε' (by refine hAB.trans (le_of_eq ?_); ring) (hr1.trans hr2) (by
      refine hAB'.trans ?_
      have : 0 ≤ Cp * e1 := mul_nonneg hCp0 he10
      nlinarith [mul_le_mul_of_nonneg_right hκβ this]) rfl hCp0 hK00 he10 he20
  have hs0' : 0 < Real.sqrt N := by linarith
  have eq : (a1 - B - 1 / (6 * Real.sqrt N) * Eβ) =
      (Real.sqrt N * (a1 - A) - 1 / 6 * Eγ) / Real.sqrt N + (A - B) + (Eγ - Eκ) / (6 * Real.sqrt N) +
        (Eκ - Eβ) / (6 * Real.sqrt N) := by
    field_simp
    ring
  rw [eq]
  exact key

end HRS.MS.R2S11
