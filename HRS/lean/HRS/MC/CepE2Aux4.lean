import HRS.MC.CepE2Aux3

/-!
# Packet CEPE2, auxiliary 4: the resolvent `J_n`, the Yosida inequality, firm nonexpansiveness
-/

open Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE2

open HRS.MC.CepE1

variable {N : ℕ}

/-- The resolvent: the solution `x` of `n (z - x) = ∇Φ(x)` in the alcove. -/
def cepe2_J {a : ℝ} (ha : 0 < a) (n : ℝ) (z : Ch N) : Ch N :=
  if h : 0 < n then Classical.choose (cepe2_exists_resolvent ha h z) else z

theorem cepe2_J_spec {a : ℝ} (ha : 0 < a) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    cepe2_J ha n z ∈ cep_Alcove N ∧
      n • (z - cepe2_J ha n z) = cepe1_pairGrad (cepe1_h1 a N) (cepe2_J ha n z) := by
  unfold cepe2_J
  rw [dif_pos hn]
  exact Classical.choose_spec (cepe2_exists_resolvent ha hn z)

/-- Firm nonexpansiveness (in the form needed). -/
theorem cepe2_firm {a : ℝ} (ha : 0 < a) {n : ℝ} (hn : 0 < n) (z z' : Ch N) :
    ‖cepe2_J ha n z - cepe2_J ha n z'‖ ^ 2 ≤ inner ℝ (z - z') (cepe2_J ha n z - cepe2_J ha n z') := by
  obtain ⟨hA, hF⟩ := cepe2_J_spec ha hn z
  obtain ⟨hA', hF'⟩ := cepe2_J_spec ha hn z'
  set x := cepe2_J ha n z
  set x' := cepe2_J ha n z'
  have hmon := cepe2_monotone ha.le hA hA'
  rw [← hF, ← hF', ← smul_sub, inner_smul_left] at hmon
  have : (z - x) - (z' - x') = (z - z') - (x - x') := by abel
  rw [this, inner_sub_left, real_inner_self_eq_norm_sq] at hmon
  simp only [conj_trivial] at hmon
  have : 0 ≤ n * (inner ℝ (z - z') (x - x') - ‖x - x'‖ ^ 2) := by linarith
  have := nonneg_of_mul_nonneg_right this hn
  linarith

theorem cepe2_lip {a : ℝ} (ha : 0 < a) {n : ℝ} (hn : 0 < n) (z z' : Ch N) :
    ‖(z - cepe2_J ha n z) - (z' - cepe2_J ha n z')‖ ≤ ‖z - z'‖ := by
  have hf := cepe2_firm ha hn z z'
  set x := cepe2_J ha n z
  set x' := cepe2_J ha n z'
  have e : (z - x) - (z' - x') = (z - z') - (x - x') := by abel
  rw [e]
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [norm_sub_sq_real]
  nlinarith

theorem cepe2_expand (u v : Ch N) (m n : ℝ) :
    inner ℝ (u - v) (m⁻¹ • u - n⁻¹ • v) =
      m⁻¹ * ‖u‖ ^ 2 + n⁻¹ * ‖v‖ ^ 2 - (m⁻¹ + n⁻¹) * inner ℝ u v := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm u v]
  ring

theorem cepe2_yosida {a : ℝ} (ha : 0 < a) {m n : ℝ} (hm : 0 < m) (hn : 0 < n) (x y : Ch N) :
    -((1 / m + 1 / n) * inner ℝ (m • (x - cepe2_J ha m x)) (n • (y - cepe2_J ha n y))) ≤
      inner ℝ (m • (x - cepe2_J ha m x) - n • (y - cepe2_J ha n y)) (x - y) := by
  obtain ⟨hA, hF⟩ := cepe2_J_spec ha hm x
  obtain ⟨hA', hF'⟩ := cepe2_J_spec ha hn y
  set p := cepe2_J ha m x
  set q := cepe2_J ha n y
  set u := m • (x - p) with hu
  set v := n • (y - q) with hv
  have hmon := cepe2_monotone ha.le hA hA'
  rw [← hF, ← hF'] at hmon
  have e : x - y = (p - q) + (m⁻¹ • u - n⁻¹ • v) := by
    rw [hu, hv, smul_smul, smul_smul, inv_mul_cancel₀ hm.ne', inv_mul_cancel₀ hn.ne', one_smul, one_smul]
    abel
  rw [e, inner_add_right]
  have h2 := cepe2_expand u v m n
  have h3 : 0 ≤ m⁻¹ * ‖u‖ ^ 2 + n⁻¹ * ‖v‖ ^ 2 := by positivity
  have : (1 / m + 1 / n) = m⁻¹ + n⁻¹ := by simp
  rw [this]
  nlinarith

end HRS.MC.CepE2
