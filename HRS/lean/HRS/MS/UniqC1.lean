import HRS.MP.RdGenerator
import HRS.Whole.AppendixBKernel

/-!
# Packet C1 of `UniqPlan`: the advecting-drift bounds for `b^σ = meanFieldDriftW D (ρ (t-σ))`

For the whole-space mean-field drift `b^σ(x) = M ∇g*μ^{t-σ} - ∇V` we prove everything in
`HRS.Whole.IsAdvectingDrift m Cb t b` except the joint continuity in `(σ,x)` (packet C2): smoothness
`C^{m+1}`, the derivative bounds `‖∇^{⊗j} b^σ‖ ≤ Cb` for `1 ≤ j ≤ m+1`, and the growth bound
`‖b^σ(x)‖ ≤ Cb (1+‖x‖)`, with the explicit constant `c1Cb d s m MB Λ ΛV G₀`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.UniqC1
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MP.RdGen

variable {d : ℕ}

/-- The pointwise (per-time) part of `IsAdvectingDrift`: smoothness, derivative bounds, growth. -/
structure AdvBounds (m : ℕ) (Cb : ℝ) (f : Euc d → Euc d) : Prop where
  smooth : ContDiff ℝ (m + 1) f
  deriv_bdd : ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ Cb
  growth : ∀ x, ‖f x‖ ≤ Cb * (1 + ‖x‖)

/-- Norm of the `n`-th derivative of a vector `∑_i U_i e_i`, by the sum of the component norms. -/
theorem c1_vec_pt (n : ℕ) (U : Fin d → Euc d → ℝ) (hU : ∀ i, ContDiff ℝ (n : WithTop ℕ∞) (U i))
    (x : Euc d) :
    ‖iteratedFDeriv ℝ n (fun x => ∑ i, U i x • (EuclideanSpace.single i (1 : ℝ) : Euc d)) x‖ ≤
      ∑ i, ‖iteratedFDeriv ℝ n (U i) x‖ := by
  have hcd : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      ContDiffAt ℝ (n : WithTop ℕ∞)
        (fun x => U i x • (EuclideanSpace.single i (1 : ℝ) : Euc d)) x :=
    fun i _ => ((hU i).smul contDiff_const).contDiffAt
  rw [iteratedFDeriv_fun_sum_apply hcd]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  set c : ℝ →L[ℝ] Euc d := ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)
  have hc : ‖c‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => ?_
    simp [c, norm_smul]
  have e : (fun x => U i x • (EuclideanSpace.single i (1 : ℝ) : Euc d)) = c ∘ U i := by
    funext x; simp [c]
  rw [e]
  have h1 := c.norm_iteratedFDeriv_comp_left ((hU i).contDiffAt (x := x)) (le_refl (n : WithTop ℕ∞))
  have h3 : 0 ≤ ‖iteratedFDeriv ℝ n (U i) x‖ := norm_nonneg _
  calc _ ≤ ‖c‖ * ‖iteratedFDeriv ℝ n (U i) x‖ := h1
    _ ≤ 1 * ‖iteratedFDeriv ℝ n (U i) x‖ := mul_le_mul_of_nonneg_right hc h3
    _ = _ := one_mul _

theorem c1_vec_decomp (f : Euc d → Euc d) :
    f = fun x => ∑ i, f x i • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
  funext x
  ext k
  simp [Pi.single_apply]

/-- Assembling the vector bounds from component bounds. -/
theorem c1_vec_of_comp {m : ℕ} {C0 C1 : ℝ} (f : Euc d → Euc d)
    (hsm : ∀ i, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => f x i))
    (hder : ∀ i, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ j (fun x => f x i) x‖ ≤ C1)
    (hgr : ∀ i, ∀ x, ‖f x i‖ ≤ C0 * (1 + ‖x‖)) :
    AdvBounds m (max (d * C1) (d * C0)) f := by
  refine ⟨?_, fun j hj1 hjm x => ?_, fun x => ?_⟩
  · have : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f := contDiff_euclidean.2 hsm
    exact_mod_cast this
  · have hU : ∀ i, ContDiff ℝ (j : WithTop ℕ∞) (fun x => f x i) := fun i =>
      (hsm i).of_le (by exact_mod_cast hjm)
    have h := c1_vec_pt j (fun i x => f x i) hU x
    rw [← c1_vec_decomp f] at h
    refine h.trans ((Finset.sum_le_sum fun i _ => hder i j hj1 hjm x).trans ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_max_left _ _
  · have h1 : ‖f x‖ ≤ ∑ i, ‖f x i‖ := by
      conv_lhs => rw [c1_vec_decomp f]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      simp [norm_smul]
    refine h1.trans ?_
    calc ∑ i, ‖f x i‖ ≤ ∑ i : Fin d, C0 * (1 + ‖x‖) := Finset.sum_le_sum fun i _ => hgr i x
      _ = (d * C0) * (1 + ‖x‖) := by simp; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end HRS.MS.UniqC1
