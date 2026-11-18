import HRS.MS.SA16Y4Fam1
import HRS.MS.SA16PForce6

/-!
# S.A.16 (SA16Y4) Dr1: component bounds of a `C^{k}` vector field with bounded derivatives

`sa16y4_comp_bounds`: for `b : Euc d → Euc d` of class `C^k` (`k ≥ 1`), `‖b 0‖ ≤ A`, `‖D^j b‖ ≤ L` (`1 ≤ j ≤ k`), the coordinate
functions `y ↦ b y i` are `C^k`, satisfy `|b y i| ≤ A + L ‖y‖` and `‖D^j (b · i)‖ ≤ L`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Dr1
variable {d : ℕ}

lemma sa16y4_comp_bounds {k : ℕ} (hk : 1 ≤ k) {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hb : ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) b) {A L : ℝ} (hA : ‖b 0‖ ≤ A)
    (hL : ∀ j, 1 ≤ j → j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ L) (i : Fin d) :
    ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) (fun y => b y i) ∧ (∀ y, |b y i| ≤ A + L * ‖y‖) ∧
      ∀ j, 1 ≤ j → j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j (fun y => b y i) x‖ ≤ L := by
  set P : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := EuclideanSpace.proj i with hP
  have hproj : ‖P‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      rw [one_mul, Real.norm_eq_abs]
      have := PiLp.norm_apply_le v i
      simpa [hP, Real.norm_eq_abs] using this
  have hfun : (fun y => b y i) = P ∘ b := rfl
  refine ⟨?_, fun y => ?_, fun j hj1 hjk x => ?_⟩
  · rw [hfun]; exact P.contDiff.comp hb
  · have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 1 le_rfl hk 0)
    have hlip : ‖b y - b 0‖ ≤ L * ‖y - 0‖ := by
      refine Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := b) (s := Set.univ)
        (fun z _ => (hb.differentiable (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hk)) z) (fun z _ => ?_) convex_univ
        (Set.mem_univ 0) (Set.mem_univ y)
      have := hL 1 le_rfl hk z
      rwa [norm_iteratedFDeriv_one] at this
    have h1 : |b y i| ≤ ‖b y‖ := by
      rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le (b y) i
    have h2 : ‖b y‖ ≤ ‖b 0‖ + ‖b y - b 0‖ := by
      calc ‖b y‖ = ‖b 0 + (b y - b 0)‖ := by congr 1; abel
        _ ≤ ‖b 0‖ + ‖b y - b 0‖ := norm_add_le _ _
    simp only [sub_zero] at hlip
    linarith
  · rw [hfun]
    refine (P.norm_iteratedFDeriv_comp_left (hb.contDiffAt) (by exact_mod_cast hjk)).trans ?_
    calc ‖P‖ * ‖iteratedFDeriv ℝ j b x‖ ≤ 1 * L :=
          mul_le_mul hproj (hL j hj1 hjk x) (norm_nonneg _) zero_le_one
      _ = L := one_mul L

end Dr1

end HRS.Whole.AppendixA.Phase2SA16R
