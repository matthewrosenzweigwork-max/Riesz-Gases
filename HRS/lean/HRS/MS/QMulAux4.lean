import HRS.MS.QMulAux3

/-!
# MS-QMUL, part 4: pointwise Leibniz bounds
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.QMul
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- `Φ_f(x) = ∑_{l ≤ m} ‖D^l f(x)‖` -/
def qm_Phi (m : ℕ) (f : Euc d → ℂ) (x : Euc d) : ℝ :=
  ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l f x‖

theorem qm_Phi_nonneg (m : ℕ) (f : Euc d → ℂ) (x : Euc d) : 0 ≤ qm_Phi m f x :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem qm_leibniz {m : ℕ} {θ : Euc d → ℝ} {A : ℝ} (hθ : ContDiff ℝ m θ)
    (hA : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j θ x‖ ≤ A) {f : Euc d → ℂ} (hf : ContDiff ℝ m f)
    {k : ℕ} (hk : k ≤ m) (x : Euc d) :
    ‖iteratedFDeriv ℝ k (fun y => (θ y : ℂ) * f y) x‖ ≤
      (2 ^ m * ((m : ℝ) + 1)) * A * qm_Phi m f x := by
  have hθc : ContDiff ℝ m (fun y => (θ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hθ
  have h1 := norm_iteratedFDeriv_mul_le hθc hf x (n := k) (by exact_mod_cast hk)
  refine h1.trans ?_
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _) x)
  have hnorm : ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun y => (θ y : ℂ)) x‖ ≤ A := by
    intro j hj
    have := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (f := θ) (hθ.contDiffAt) (x := x)
      (i := j) (by exact_mod_cast hj)
    have e : (fun y => (θ y : ℂ)) = Complex.ofRealLI ∘ θ := rfl
    rw [e, this]
    exact hA j hj x
  have hterm : ∀ j ∈ Finset.range (k + 1),
      (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun y => (θ y : ℂ)) x‖ *
        ‖iteratedFDeriv ℝ (k - j) f x‖ ≤ 2 ^ m * A * qm_Phi m f x := by
    intro j hj
    have hj' : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hc : (k.choose j : ℝ) ≤ 2 ^ m := by
      have := Nat.choose_le_two_pow k j
      calc (k.choose j : ℝ) ≤ 2 ^ k := by exact_mod_cast this
        _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hk
    have hP : ‖iteratedFDeriv ℝ (k - j) f x‖ ≤ qm_Phi m f x := by
      unfold qm_Phi
      exact Finset.single_le_sum (f := fun l => ‖iteratedFDeriv ℝ l f x‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
    exact mul_le_mul (mul_le_mul hc (hnorm j (hj'.trans hk)) (norm_nonneg _) (by positivity)) hP
      (norm_nonneg _) (by positivity)
  calc _ ≤ ∑ j ∈ Finset.range (k + 1), 2 ^ m * A * qm_Phi m f x := Finset.sum_le_sum hterm
    _ = ((k : ℝ) + 1) * (2 ^ m * A * qm_Phi m f x) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ ((m : ℝ) + 1) * (2 ^ m * A * qm_Phi m f x) := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hk)
        have := qm_Phi_nonneg m f x
        positivity
    _ = _ := by ring

theorem qm_Phi_sq (m : ℕ) (f : Euc d → ℂ) (x : Euc d) :
    qm_Phi m f x ^ 2 ≤ (((m : ℝ) + 1) * ((d : ℝ) + 1) ^ m) *
      ∑ l ∈ Finset.range (m + 1), ∑ i : Fin l → Fin d, ‖qm_pd i f x‖ ^ 2 := by
  unfold qm_Phi
  have h1 : (∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l f x‖) ^ 2 ≤
      ((m : ℝ) + 1) * ∑ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l f x‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 1))
      (f := fun l => ‖iteratedFDeriv ℝ l f x‖)
    simpa using this
  have h2 : ∀ l ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ l f x‖ ^ 2 ≤
      ((d : ℝ) + 1) ^ m * ∑ i : Fin l → Fin d, ‖qm_pd i f x‖ ^ 2 := by
    intro l hl
    have hl' : l ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have a1 := qm_norm_le_sum (iteratedFDeriv ℝ l f x)
    have a2 : ‖iteratedFDeriv ℝ l f x‖ ^ 2 ≤ (∑ i : Fin l → Fin d, ‖qm_pd i f x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) a1 2
    have a3 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin l → Fin d)))
      (f := fun i => ‖qm_pd i f x‖)
    have a4 : ((Finset.univ : Finset (Fin l → Fin d)).card : ℝ) ≤ ((d : ℝ) + 1) ^ m := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      push_cast
      calc (d : ℝ) ^ l ≤ ((d : ℝ) + 1) ^ l := pow_le_pow_left₀ (by positivity) (by linarith) l
        _ ≤ ((d : ℝ) + 1) ^ m := pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]) hl'
    calc ‖iteratedFDeriv ℝ l f x‖ ^ 2 ≤ _ := a2
      _ ≤ _ := a3
      _ ≤ _ := mul_le_mul_of_nonneg_right a4 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  calc _ ≤ _ := h1
    _ ≤ ((m : ℝ) + 1) * ∑ l ∈ Finset.range (m + 1), (((d : ℝ) + 1) ^ m *
          ∑ i : Fin l → Fin d, ‖qm_pd i f x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum h2) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

end HRS.MS.QMul
