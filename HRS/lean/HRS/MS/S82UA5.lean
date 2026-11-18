import HRS.MS.S82UA4

/-!
# S8.2 A01 (S82U): measurable symmetric model of the canonical triple and its pointwise bound
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T

/-- centered force (model): `∇g(x-z) - F(x)`. -/
def uc {d : ℕ} (Fm : Euc d → Euc d) (x z : Euc d) : Euc d :=
  rieszKernelGrad d (criticalS d) (x - z) - Fm x

def uT {d : ℕ} (Fm : Euc d → Euc d) (gt : Euc d → Euc d → Euc d) (x y z : Euc d) : ℝ :=
  -inner ℝ (uc Fm x z) (gt x y) - inner ℝ (uc Fm y z) (gt y x)

def uGm {d : ℕ} (Fm : Euc d → Euc d) (gt : Euc d → Euc d → Euc d) (Jt : Euc d → Euc d → ℝ)
    (x y z : Euc d) : ℝ :=
  (uT Fm gt x y z + uT Fm gt x z y + uT Fm gt y z x - Jt x y - Jt x z - Jt y z) / 3

open Classical in
def uG {d : ℕ} (Fm : Euc d → Euc d) (gt : Euc d → Euc d → Euc d) (Jt : Euc d → Euc d → ℝ)
    (x y z : Euc d) : ℝ :=
  if x ≠ y ∧ x ≠ z ∧ y ≠ z then uGm Fm gt Jt x y z else 0

lemma uT_comm {d : ℕ} (Fm : Euc d → Euc d) (gt : Euc d → Euc d → Euc d) (x y z : Euc d) :
    uT Fm gt x y z = uT Fm gt y x z := by
  unfold uT; ring

lemma uGm_swap12 {d : ℕ} (Fm : Euc d → Euc d) (gt : Euc d → Euc d → Euc d) (Jt : Euc d → Euc d → ℝ)
    (hJ : ∀ x y, Jt x y = Jt y x) (x y z : Euc d) : uGm Fm gt Jt x y z = uGm Fm gt Jt y x z := by
  unfold uGm
  rw [uT_comm Fm gt x y z, hJ x y]
  ring

lemma uGm_swap23 {d : ℕ} (Fm : Euc d → Euc d) (gt : Euc d → Euc d → Euc d) (Jt : Euc d → Euc d → ℝ)
    (hJ : ∀ x y, Jt x y = Jt y x) (x y z : Euc d) : uGm Fm gt Jt x y z = uGm Fm gt Jt x z y := by
  unfold uGm
  rw [uT_comm Fm gt z y x, hJ y z]
  ring

lemma uG_symm {d : ℕ} (Fm : Euc d → Euc d) (gt : Euc d → Euc d → Euc d) (Jt : Euc d → Euc d → ℝ)
    (hJ : ∀ x y, Jt x y = Jt y x) (x y z : Euc d) :
    uG Fm gt Jt x y z = uG Fm gt Jt y x z ∧ uG Fm gt Jt x y z = uG Fm gt Jt x z y := by
  unfold uG
  constructor
  · by_cases h : x ≠ y ∧ x ≠ z ∧ y ≠ z
    · have h' : y ≠ x ∧ y ≠ z ∧ x ≠ z := ⟨h.1.symm, h.2.2, h.2.1⟩
      rw [if_pos h, if_pos h']; exact uGm_swap12 Fm gt Jt hJ x y z
    · have h' : ¬ (y ≠ x ∧ y ≠ z ∧ x ≠ z) := fun h'' => h ⟨h''.1.symm, h''.2.2, h''.2.1⟩
      rw [if_neg h, if_neg h']
  · by_cases h : x ≠ y ∧ x ≠ z ∧ y ≠ z
    · have h' : x ≠ z ∧ x ≠ y ∧ z ≠ y := ⟨h.2.1, h.1, h.2.2.symm⟩
      rw [if_pos h, if_pos h']; exact uGm_swap23 Fm gt Jt hJ x y z
    · have h' : ¬ (x ≠ z ∧ x ≠ y ∧ z ≠ y) := fun h'' => h ⟨h''.2.1, h''.1, h''.2.2.symm⟩
      rw [if_neg h, if_neg h']

lemma u_grad_odd {d : ℕ} {x y : Euc d} (hxy : x ≠ y) :
    rieszKernelGrad d (criticalS d) (y - x) = -rieszKernelGrad d (criticalS d) (x - y) := by
  have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
  have hz' : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  rw [HRS.Whole.movtr_rieszKernelGrad_eq _ hz', HRS.Whole.movtr_rieszKernelGrad_eq _ hz,
    show y - x = -(x - y) by abel, norm_neg, smul_neg, neg_smul]

/-- Grouping of the three `T`-terms into three edges plus mean-force terms. -/
lemma uT_group {d : ℕ} (Fm : Euc d → Euc d) (gt : Euc d → Euc d → Euc d) {x y z : Euc d}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    uT Fm gt x y z + uT Fm gt x z y + uT Fm gt y z x =
      -inner ℝ (rieszKernelGrad d (criticalS d) (x - z)) (gt x y - gt z y)
      - inner ℝ (rieszKernelGrad d (criticalS d) (y - z)) (gt y x - gt z x)
      - inner ℝ (rieszKernelGrad d (criticalS d) (x - y)) (gt x z - gt y z)
      + (inner ℝ (Fm x) (gt x y) + inner ℝ (Fm y) (gt y x) + inner ℝ (Fm x) (gt x z) +
          inner ℝ (Fm z) (gt z x) + inner ℝ (Fm y) (gt y z) + inner ℝ (Fm z) (gt z y)) := by
  have o1 := u_grad_odd hxz
  have o2 := u_grad_odd hyz
  have o3 := u_grad_odd hxy
  unfold uT uc
  rw [o1, o2, o3]
  simp only [inner_sub_left, inner_sub_right, inner_neg_left]
  ring

end HRS.MS.S82U
