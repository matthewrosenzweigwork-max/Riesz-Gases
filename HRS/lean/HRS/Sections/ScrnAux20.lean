import HRS.Sections.ScrnAux19

/-!
# Packet SCRN, part 20: sup bounds of `D¹ f^r`, `D² f^r` from the coefficients of `ψ` (with time decay)

If `‖ĝ(k)‖ ≤ ‖ψ̂(k)‖` for all `k` and `‖ĝ(k)‖ ≤ θ ‖ψ̂(k)‖` for `k ≠ 0`, then
`‖D^i lift g‖ ≤ 2 θ ∑_k (2π|k|)^i ‖ψ̂(k)‖` for `i = 1, 2` (`scrn_trans_deriv`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace HRS

variable {d : ℕ}

open PDE

lemma scrn_two_pi_enorm_nonneg (k : Lattice d) : 0 ≤ 2 * Real.pi * Lattice.enorm k :=
  mul_nonneg (by positivity) (norm_nonneg _)

lemma scrn_enorm_zero : Lattice.enorm (0 : Lattice d) = 0 := by
  unfold Lattice.enorm Lattice.toEuc
  rw [show (WithLp.toLp 2 fun i => (((0 : Lattice d) i : ℤ) : ℝ)) = (0 : Euc d) from by
    ext i; simp]
  simp

theorem scrn_trans_deriv {g ψ : Torus d → ℝ} (hg : Continuous g) {θ : ℝ} (hθ : 0 ≤ θ)
    (hcoef : ∀ k, ‖coeffOf g k‖ ≤ ‖coeffOf ψ k‖)
    (hdec : ∀ k, k ≠ 0 → ‖coeffOf g k‖ ≤ θ * ‖coeffOf ψ k‖)
    (hsum : ∀ i : ℕ, i ≤ 2 → Summable fun k : Lattice d =>
      (2 * Real.pi * Lattice.enorm k) ^ i * ‖coeffOf ψ k‖) :
    Torus.IsCk 2 g ∧
    (∀ y : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift g) y‖ ≤
      2 * θ * ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ 1 * ‖coeffOf ψ k‖) ∧
    (∀ y : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift g) y‖ ≤
      2 * θ * ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ 2 * ‖coeffOf ψ k‖) := by
  have hsg : ∀ i : ℕ, i ≤ 2 → Summable fun k : Lattice d =>
      (2 * Real.pi * Lattice.enorm k) ^ i * ‖coeffOf g k‖ := by
    intro i hi
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (scrn_two_pi_enorm_nonneg k) _) (norm_nonneg _))
      (fun k => ?_) (hsum i hi)
    exact mul_le_mul_of_nonneg_left (hcoef k) (pow_nonneg (scrn_two_pi_enorm_nonneg k) _)
  obtain ⟨hCk, hbd⟩ := scrn_iteratedFDeriv_le hg (j := 2) hsg
  have key : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ∑' k : Lattice d,
      (2 * Real.pi * Lattice.enorm k) ^ i * ‖coeffOf g k‖ ≤
      θ * ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ i * ‖coeffOf ψ k‖ := by
    intro i hi1 hi2
    rw [← tsum_mul_left]
    refine (hsg i hi2).tsum_le_tsum (fun k => ?_) ((hsum i hi2).mul_left θ)
    by_cases hk : k = 0
    · subst hk
      rw [scrn_enorm_zero]
      simp [zero_pow (by omega : i ≠ 0)]
    · calc (2 * Real.pi * Lattice.enorm k) ^ i * ‖coeffOf g k‖
          ≤ (2 * Real.pi * Lattice.enorm k) ^ i * (θ * ‖coeffOf ψ k‖) :=
            mul_le_mul_of_nonneg_left (hdec k hk) (pow_nonneg (scrn_two_pi_enorm_nonneg k) _)
        _ = θ * ((2 * Real.pi * Lattice.enorm k) ^ i * ‖coeffOf ψ k‖) := by ring
  refine ⟨hCk, fun y => ?_, fun y => ?_⟩
  · refine (hbd 1 (by norm_num) y).trans ?_
    have := key 1 le_rfl (by norm_num)
    nlinarith
  · refine (hbd 2 le_rfl y).trans ?_
    have := key 2 (by norm_num) le_rfl
    nlinarith

/-- The `ψ`-sums `S_i = ∑_k (2π|k|)^i ‖ψ̂(k)‖ ≲ ℓ^{-d/2-i}` for `i = 0, 1, 2`. -/
theorem scrn_S_bound (hd : 0 < d) (x₀ : Euc d) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∀ i : ℕ, i ≤ 2 →
      Summable (fun k : Lattice d =>
        (2 * Real.pi * Lattice.enorm k) ^ i * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖) ∧
      ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ i *
        ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ ≤ C * ℓ ^ (-((d : ℝ) / 2) - i) := by
  have hb : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 →
      Summable (fun k : Lattice d =>
        (2 * Real.pi * Lattice.enorm k) ^ i * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖) ∧
      ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ i *
        ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ ≤ C * ℓ ^ (-((d : ℝ) / 2) - i) := by
    intro i
    obtain ⟨C, hC, h⟩ := scrn_psi_wsum hd x₀ hφ hc (r := (i : ℝ)) (Nat.cast_nonneg i) (e := 1)
      le_rfl
    refine ⟨(2 * Real.pi) ^ i * C, by positivity, fun ℓ hℓ hℓ1 => ?_⟩
    obtain ⟨hs, hsum⟩ := h ℓ hℓ hℓ1
    have e : ∀ k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ i *
        ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ =
        (2 * Real.pi) ^ i * (Lattice.enorm k ^ (i : ℝ) * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ ^ 1) := by
      intro k
      rw [mul_pow, Real.rpow_natCast, pow_one]; ring
    simp_rw [e]
    refine ⟨hs.mul_left _, ?_⟩
    rw [tsum_mul_left]
    have hexp : (d : ℝ) * (1 : ℕ) / 2 - ((d : ℝ) + i) = -((d : ℝ) / 2) - i := by push_cast; ring
    rw [hexp] at hsum
    calc (2 * Real.pi) ^ i * ∑' k : Lattice d, Lattice.enorm k ^ (i : ℝ) *
          ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ ^ 1
        ≤ (2 * Real.pi) ^ i * (C * ℓ ^ (-((d : ℝ) / 2) - i)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  choose C hC0 hC using hb
  refine ⟨C 0 + C 1 + C 2, by have := hC0 0; have := hC0 1; have := hC0 2; positivity,
    fun ℓ hℓ hℓ1 i hi => ⟨(hC i ℓ hℓ hℓ1).1, ?_⟩⟩
  refine (hC i ℓ hℓ hℓ1).2.trans ?_
  have hp : 0 ≤ ℓ ^ (-((d : ℝ) / 2) - i) := Real.rpow_nonneg hℓ.le _
  refine mul_le_mul_of_nonneg_right ?_ hp
  have h0 := hC0 0
  have h1 := hC0 1
  have h2 := hC0 2
  interval_cases i <;> linarith

end HRS
