import HRS.MS.SA16ZE2

/-!
# S.A.16 (SA16Z) E3: the integrand of the level-`j` pairing and its splitting
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section E3
variable {d : ℕ} {s : ℝ}

/-- the Schwartz tensor of the `j`-th derivatives of `φ` -/
def sa16z_Wt {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (j : ℕ) : (Fin j → Fin d) → 𝓢(Euc d, ℝ) :=
  fun κ => sa16z_schw (sa16s_cc_partialDeriv hφ κ)

lemma sa16z_Wt_coe {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (j : ℕ) (κ : Fin j → Fin d) :
    ⇑(sa16z_Wt hφ j κ) = partialDeriv κ φ := rfl

lemma sa16z_vn_eq {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (j : ℕ) (x : Euc d) :
    vnorm (fun κ => sa16z_Wt hφ j κ x) = sa16sz_vn φ j x := rfl

/-- the `B^l` part of the integrand (in the `dm`-form) -/
def sa16z_IBd (cA cs : ℝ) (μ φ : Euc d → ℝ) (p θ : ℝ) (l : Fin d) (j : ℕ) (x : Euc d) : ℝ :=
  sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x *
    (cA * (sa16z_dm μ l x * sa16z_pv d θ l (partialDeriv idx φ) x) -
      cs * sa16z_Q j idx l (fun a κ => sa16z_dm μ a x * sa16z_pv d θ l (partialDeriv κ φ) x))

/-- the same, with the matrix `B^l` and `√μ` as in the absorption lemma -/
lemma sa16z_IBd_eq {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hpos : ∀ x, 0 ≤ μ x) {Λ : ℝ}
    (hCb : sa16z_Cb 2 Λ μ) (hφ : IsCcInfty φ) (cA cs p θ : ℝ) (l : Fin d) (j : ℕ) (x : Euc d) :
    sa16z_IBd cA cs μ φ p θ l j x =
      vnorm (fun κ => sa16z_Wt hφ j κ x) ^ (p - 2) * ∑ i : Fin j → Fin d, sa16z_Wt hφ j i x *
        (Real.sqrt (μ x) * ∑ k : Fin j → Fin d, sa16z_Bm cA cs μ l j x i k *
          pvOdd d θ (fun u : Euc d => u l) (fun y => sa16z_Wt hφ j k y) x) := by
  unfold sa16z_IBd
  rw [sa16z_vn_eq]
  congr 1
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [sa16z_Bm_apply]
  have hd1 := sa16z_hh_mul hμ hpos hCb
  have h2 : sa16z_Q j idx l (fun a κ => sa16z_dm μ a x * sa16z_pv d θ l (partialDeriv κ φ) x) =
      Real.sqrt (μ x) * sa16z_Q j idx l (fun a κ => sa16z_hh μ a x * pvOdd d θ (fun u : Euc d => u l)
        (fun y => sa16z_Wt hφ j κ y) x) := by
    rw [← sa16z_Q_smul]
    refine sa16z_Q_congr j idx l fun a κ => ?_
    rw [hd1 a x]; simp only [sa16z_pv]; rw [sa16z_Wt_coe]; ring
  rw [h2, hd1 l x]
  have e : ∀ κ : Fin j → Fin d, (fun y => sa16z_Wt hφ j κ y) = partialDeriv κ φ := fun κ => rfl
  have e' : sa16z_Wt hφ j idx x = partialDeriv idx φ x := rfl
  simp only [e, e', sa16z_pv]
  ring

end E3

end HRS.Whole.AppendixA.Phase2SA16R
