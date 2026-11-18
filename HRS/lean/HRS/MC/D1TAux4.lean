import HRS.MC.D1TAux3

/-!
# Packet D1T, auxiliary file 4: the uniform domination of `G_ε(t)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators

namespace HRS.MC.D1T

open HRS

variable {d : ℕ}

theorem d1t_exists_eta (x : Torus d) (hx : x ≠ 0) :
    ∃ (i0 : Fin d) (η : ℝ), 0 < η ∧ ∀ n : ℤ, η ≤ |Torus.rep x i0 - n| := by
  obtain ⟨i0, hi0⟩ : ∃ i0, x i0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  refine ⟨i0, |Torus.rep x i0 - round (Torus.rep x i0)|, ?_, fun n => round_le _ n⟩
  rw [abs_pos]
  intro h
  apply hi0
  have h1 : Torus.rep x i0 = round (Torus.rep x i0) := by linarith
  have h2 : x i0 = ((Torus.rep x i0 : ℝ) : UnitAddCircle) := by
    have := congrFun (Torus.mk_rep x) i0
    exact this.symm
  rw [h2, h1, AddCircle.coe_eq_zero_iff]
  exact ⟨round (Torus.rep x i0), by simp⟩

theorem d1t_A_eq {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) (x : Torus d) :
    ∑' k : Lattice d, Real.exp (-ε * Lattice.enorm k ^ 2) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 *
        Torus.cosMode k x = d1tG ψ x ε t + fdlPsiHat ψ 0 ^ 2 := by
  classical
  have hs1 := d1t_term_summable hψ hε t x
  have hs2 : Summable fun k : Lattice d => if k = 0 then fdlPsiHat ψ 0 ^ 2 else 0 :=
    (hasSum_ite_eq (0 : Lattice d) (fdlPsiHat ψ 0 ^ 2)).summable
  have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
  have hpt : ∀ k : Lattice d, Real.exp (-ε * Lattice.enorm k ^ 2) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 *
        Torus.cosMode k x = Real.exp (-ε * Lattice.enorm k ^ 2) * d1tB ψ t k * Torus.cosMode k x +
          (if k = 0 then fdlPsiHat ψ 0 ^ 2 else 0) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [d1tB, h0, cosMode_zero, Lattice.enorm]
    · simp [d1tB, hk]
  simp_rw [hpt]
  rw [hs1.tsum_add hs2, tsum_ite_eq]
  rfl


theorem d1t_G_bound {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (x : Torus d) (hx : x ≠ 0) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∃ M K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, 0 < t →
      |d1tG ψ x ε t| ≤ (if t ≤ δ0 then M else K * (t ^ (2 * (d + 1)))⁻¹) := by
  obtain ⟨i0, η, hη, hη'⟩ := d1t_exists_eta x hx
  obtain ⟨M0, hM0⟩ := d1t_loc hψ hη i0 hη'
  obtain ⟨K, hK0, hK⟩ := d1t_tail hψ
  refine ⟨η / 2, half_pos hη, M0 + fdlPsiHat ψ 0 ^ 2, K, hK0, fun ε hε hε1 t ht => ?_⟩
  split_ifs with hle
  · have h1 := hM0 ε hε hε1 t ht hle
    rw [Torus.mk_rep] at h1
    have h2 := d1t_A_eq hψ hε t x
    have h3 : d1tG ψ x ε t = (∑' k : Lattice d, Real.exp (-ε * Lattice.enorm k ^ 2) *
        fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 * Torus.cosMode k x) - fdlPsiHat ψ 0 ^ 2 := by
      rw [h2]; ring
    rw [h3]
    calc _ ≤ |∑' k : Lattice d, Real.exp (-ε * Lattice.enorm k ^ 2) *
        fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 * Torus.cosMode k x| + |fdlPsiHat ψ 0 ^ 2| :=
          abs_sub _ _
      _ ≤ _ := by
          rw [abs_of_nonneg (sq_nonneg (fdlPsiHat ψ 0))]
          linarith
  · obtain ⟨hs, hle'⟩ := hK t ht
    unfold d1tG
    have hs2 := d1t_term_summable hψ hε t x
    calc |∑' k : Lattice d, Real.exp (-ε * Lattice.enorm k ^ 2) * d1tB ψ t k * Torus.cosMode k x|
        = ‖∑' k : Lattice d, Real.exp (-ε * Lattice.enorm k ^ 2) * d1tB ψ t k * Torus.cosMode k x‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∑' k : Lattice d, ‖Real.exp (-ε * Lattice.enorm k ^ 2) * d1tB ψ t k * Torus.cosMode k x‖ :=
          norm_tsum_le_tsum_norm hs2.norm
      _ ≤ ∑' k : Lattice d, d1tB ψ t k := by
          refine hs2.norm.tsum_le_tsum (fun k => ?_) hs
          rw [Real.norm_eq_abs]
          refine (d1t_term_bound ε t x k).trans (mul_le_of_le_one_left (d1tB_nonneg ψ t k) ?_)
          exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hε.le (sq_nonneg (Lattice.enorm k))])
      _ ≤ _ := hle'

end HRS.MC.D1T
