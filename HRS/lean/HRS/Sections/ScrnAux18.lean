import HRS.Sections.ScrnAux17

/-!
# Packet SCRN, part 18: weighted lattice sums of the Fourier coefficients of the mesoscopic test

For `ψ = mesoTest d ℓ x₀ φ` and `ℓ ∈ (0,1]`, `r ≥ 0`, `e ≥ 1`:
`∑_k |k|^r ‖ψ̂(k)‖^e ≤ C ℓ^{d e/2 - (d + r)}` (`scrn_psi_wsum`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate FourierTransform

namespace HRS

variable {d : ℕ}

open PDE

theorem scrn_psi_wsum (hd : 0 < d) (x₀ : Euc d) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) {r : ℝ} (hr : 0 ≤ r) {e : ℕ}
    (he : 1 ≤ e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 →
      Summable (fun k : Lattice d => Lattice.enorm k ^ r * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ ^ e) ∧
      ∑' k : Lattice d, Lattice.enorm k ^ r * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ ^ e ≤
        C * ℓ ^ ((d : ℝ) * e / 2 - ((d : ℝ) + r)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (d : ℝ) + r < e * N := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((d + r : ℝ))
    refine ⟨N, ?_⟩
    have : (N : ℝ) ≤ e * N := by
      have : (1 : ℝ) ≤ e := by exact_mod_cast he
      nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    linarith
  obtain ⟨C, hC, hW⟩ := scrn_wsum hd hr he hN
  obtain ⟨A, hA, hF⟩ := scrn_fourier_bound hφ hc N
  refine ⟨C * A ^ e, by positivity, fun ℓ hℓ hℓ1 => ?_⟩
  obtain ⟨hs, hsum⟩ := hW (𝓕 (scrnPhiC φ)) A hA (fun ξ => (hF ξ).1) ℓ hℓ hℓ1
  have heq : ∀ k : Lattice d, Lattice.enorm k ^ r * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ ^ e =
      ℓ ^ ((d : ℝ) * e / 2) *
        (Lattice.enorm k ^ r * ‖𝓕 (scrnPhiC φ) (ℓ • Lattice.toEuc k)‖ ^ e) := by
    intro k
    rw [scrn_norm_psi hℓ x₀ hφ hc, mul_pow, ← Real.rpow_natCast (ℓ ^ ((d : ℝ) / 2)) e,
      ← Real.rpow_mul hℓ.le]
    have : (d : ℝ) / 2 * (e : ℝ) = (d : ℝ) * e / 2 := by ring
    rw [this]; ring
  simp_rw [heq]
  refine ⟨hs.mul_left _, ?_⟩
  rw [tsum_mul_left]
  have hl : 0 ≤ ℓ ^ ((d : ℝ) * e / 2) := Real.rpow_nonneg hℓ.le _
  calc ℓ ^ ((d : ℝ) * e / 2) * ∑' k : Lattice d,
        Lattice.enorm k ^ r * ‖𝓕 (scrnPhiC φ) (ℓ • Lattice.toEuc k)‖ ^ e
      ≤ ℓ ^ ((d : ℝ) * e / 2) * (C * A ^ e * ℓ ^ (-((d : ℝ) + r))) :=
        mul_le_mul_of_nonneg_left hsum hl
    _ = C * A ^ e * ℓ ^ ((d : ℝ) * e / 2 - ((d : ℝ) + r)) := by
        have : ℓ ^ ((d : ℝ) * e / 2) * ℓ ^ (-((d : ℝ) + r)) =
            ℓ ^ ((d : ℝ) * e / 2 - ((d : ℝ) + r)) := by
          rw [← Real.rpow_add hℓ, sub_eq_add_neg]
        calc ℓ ^ ((d : ℝ) * e / 2) * (C * A ^ e * ℓ ^ (-((d : ℝ) + r)))
            = C * A ^ e * (ℓ ^ ((d : ℝ) * e / 2) * ℓ ^ (-((d : ℝ) + r))) := by ring
          _ = _ := by rw [this]

end HRS
