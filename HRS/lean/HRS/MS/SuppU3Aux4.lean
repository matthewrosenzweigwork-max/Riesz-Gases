import HRS.MS.SuppU3Aux3

/-!
# U3, part 4: the `C_b^m` norm of `x ↦ ∑_j (B Ψ_j(x), Ψ_j(x))` from the derivative bounds of `Ψ_j`
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.SuppU3

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The bilinear form `(u, v) ↦ (B u, v)`. -/
def u3_bil (B : H →L[ℝ] H) : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ).comp B

theorem u3_bil_apply (B : H →L[ℝ] H) (u v : H) : u3_bil B u v = inner ℝ (B u) v := by
  simp [u3_bil]

theorem u3_bil_norm (B : H →L[ℝ] H) (hB : ‖B‖ ≤ 1) : ‖u3_bil B‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one (fun u v => ?_)
  rw [u3_bil_apply]
  calc ‖inner ℝ (B u) v‖ ≤ ‖B u‖ * ‖v‖ := norm_inner_le_norm _ _
    _ ≤ (‖B‖ * ‖u‖) * ‖v‖ := by gcongr; exact B.le_opNorm u
    _ ≤ 1 * ‖u‖ * ‖v‖ := by gcongr
    
theorem u3_bil_deriv (B : H →L[ℝ] H) (hB : ‖B‖ ≤ 1) {Ψ : Euc d → H} (hΨ : ContDiff ℝ ∞ Ψ) (m : ℕ)
    {K : ℝ} (hK : 0 ≤ K) (hΨb : ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k Ψ x‖ ≤ K) (k : ℕ) (hk : k ≤ m)
    (x : Euc d) :
    ‖iteratedFDeriv ℝ k (fun y => inner ℝ (B (Ψ y)) (Ψ y)) x‖ ≤ 2 ^ k * K ^ 2 := by
  have e : (fun y => inner ℝ (B (Ψ y)) (Ψ y)) = fun y => u3_bil B (Ψ y) (Ψ y) := by
    funext y; rw [u3_bil_apply]
  rw [e]
  have h1 := (u3_bil B).norm_iteratedFDeriv_le_of_bilinear hΨ hΨ x (n := k)
    (by exact_mod_cast le_top)
  refine h1.trans ?_
  have hb := u3_bil_norm B hB
  calc ‖u3_bil B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i Ψ x‖ *
        ‖iteratedFDeriv ℝ (k - i) Ψ x‖
      ≤ 1 * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K * K := by
        refine mul_le_mul hb (Finset.sum_le_sum fun i hi => ?_)
          (Finset.sum_nonneg fun i _ => by positivity) zero_le_one
        have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have h1 := hΨb i (hi'.trans hk) x
        have h2 := hΨb (k - i) ((Nat.sub_le _ _).trans hk) x
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) hK)
    _ = 2 ^ k * K ^ 2 := by
        rw [one_mul]
        have : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K * K =
            (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) * K ^ 2 := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => by ring
        rw [this]
        congr 1
        exact_mod_cast Nat.sum_range_choose k

theorem u3_h_cb (B : H →L[ℝ] H) (hB : ‖B‖ ≤ 1) (Ψ : Fin d → Euc d → H) (hΨ : ∀ j, ContDiff ℝ ∞ (Ψ j))
    (m : ℕ) {K : ℝ} (hK : 0 ≤ K) (hΨb : ∀ j, ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k (Ψ j) x‖ ≤ K) :
    HRS.MemCb m (fun x => ∑ j, inner ℝ (B (Ψ j x)) (Ψ j x)) ∧
      HRS.cbNorm m (fun x => ∑ j, inner ℝ (B (Ψ j x)) (Ψ j x)) ≤ (m + 1) * (d * 2 ^ m * K ^ 2) := by
  have hcd : ∀ j, ContDiff ℝ ∞ (fun y => inner ℝ (B (Ψ j y)) (Ψ j y)) := fun j =>
    ContDiff.inner ℝ (B.contDiff.comp (hΨ j)) (hΨ j)
  have hF : ContDiff ℝ m (fun x => ∑ j, inner ℝ (B (Ψ j x)) (Ψ j x)) :=
    ContDiff.sum fun j _ => (hcd j).of_le (by exact_mod_cast le_top)
  have hbd : ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k (fun x => ∑ j, inner ℝ (B (Ψ j x)) (Ψ j x)) x‖ ≤
      d * 2 ^ m * K ^ 2 := by
    intro k hk x
    rw [iteratedFDeriv_fun_sum_apply (fun j _ => ((hcd j).of_le (by exact_mod_cast le_top)).contDiffAt)]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖iteratedFDeriv ℝ k (fun y => inner ℝ (B (Ψ j y)) (Ψ j y)) x‖
        ≤ ∑ _j : Fin d, (2 ^ m * K ^ 2) := Finset.sum_le_sum fun j _ =>
          (u3_bil_deriv B hB (hΨ j) m hK (hΨb j) k hk x).trans
            (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) (sq_nonneg K))
      _ = d * 2 ^ m * K ^ 2 := by simp; ring
  refine ⟨⟨hF, fun k hk => ⟨d * 2 ^ m * K ^ 2, ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩; exact hbd k hk x
  · unfold HRS.cbNorm
    calc ∑ k ∈ Finset.range (m + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ k (fun x => ∑ j, inner ℝ (B (Ψ j x)) (Ψ j x)) z‖
        ≤ ∑ _k ∈ Finset.range (m + 1), (d * 2 ^ m * K ^ 2 : ℝ) :=
          Finset.sum_le_sum fun k hk => ciSup_le fun x =>
            hbd k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) x
      _ = (m + 1) * (d * 2 ^ m * K ^ 2) := by simp

end HRS.MS.SuppU3
