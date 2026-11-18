import HRS.MC.D47Aux6

/-!
# Packet D47, auxiliary facts 7: the one-sided Itô bound (D.5) for every `η ≥ λ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MC.D47

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1 HRS.MC.D3T3 HRS.StaticLimitAux

variable {d : ℕ}

lemma d47_ito (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → ∀ X : Config d N, ∀ η : ℝ,
      smearScale d N Λ ≤ η →
        offDiagPairing (fun x y => Torus.laplacian (fdlTruncT ψ s b η) (x - y))
            X (withDensityReal ρ)
          ≤ |Torus.laplacian (fdlTruncT ψ s b η) 0| / N ∧
        |Torus.laplacian (fdlTruncT ψ s b η) 0| / N
          ≤ C * Λ ^ ((s + 2) / d) * (N : ℝ) ^ ((s + 2) / d - 1) := by
  obtain ⟨M, hM0, hM⟩ := d47_tsum_bound hd hs0 hψ hb.1
  refine ⟨4 * Real.pi ^ 2 * M, by positivity, fun Λ hΛ N hN ρ hρ X η hη => ?_⟩
  have := isProb_withDensityReal hρ
  have hl0 : 0 < smearScale d N Λ := d47_lam_pos hN hΛ
  have hη0 : 0 < η := lt_of_lt_of_le hl0 hη
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set b' : Lattice d → ℝ := fun k => 4 * Real.pi ^ 2 * (Lattice.enorm k ^ 2 * d47_a ψ s b η k) with hb'
  have hb'0 : ∀ k, 0 ≤ b' k := fun k =>
    mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (d47_a_nonneg hb.1.le hη0 k))
  have hb's : Summable b' := ((d47_summable hd hs0 hψ hb.1 hη0).1).mul_left (4 * Real.pi ^ 2)
  have hΔ : Torus.laplacian (fdlTruncT ψ s b η) = fun x => -specKernel b' x := by
    rw [d47_lap_eq hd hs0 hsd hψ hb hη0]
    funext x
    unfold specKernel
    simp only [neg_mul, tsum_neg]
    rfl
  have hT : ∑' k, b' k = 4 * Real.pi ^ 2 * ∑' k : Lattice d, Lattice.enorm k ^ 2 * d47_a ψ s b η k :=
    tsum_mul_left
  have hT0 : 0 ≤ ∑' k, b' k := tsum_nonneg hb'0
  have hΔ0 : Torus.laplacian (fdlTruncT ψ s b η) 0 = -(∑' k, b' k) := by
    rw [hΔ]; simp only [d47_spec_zero]
  have habs : |Torus.laplacian (fdlTruncT ψ s b η) 0| = ∑' k, b' k := by
    rw [hΔ0, abs_neg, abs_of_nonneg hT0]
  refine ⟨?_, ?_⟩
  · have hoff : offDiagPairing (fun x y => Torus.laplacian (fdlTruncT ψ s b η) (x - y)) X
        (withDensityReal ρ) =
        2 * modE (fun x => Torus.laplacian (fdlTruncT ψ s b η) x) N X (withDensityReal ρ) := by
      unfold offDiagPairing modE
      ring
    rw [hoff, habs, hΔ, d47_modE_neg]
    have hlow := d47_modE_spec_lower hb'0 hb's (withDensityReal ρ) hN X
    rw [d47_spec_zero] at hlow
    have h1 : -modE (specKernel b') N X (withDensityReal ρ) ≤ (∑' k, b' k) / (2 * N) := by
      have e : -(∑' k, b' k) / (2 * (N : ℝ)) = -((∑' k, b' k) / (2 * N)) := neg_div _ _
      linarith
    calc 2 * -modE (specKernel b') N X (withDensityReal ρ) ≤ 2 * ((∑' k, b' k) / (2 * N)) := by
          linarith
      _ = (∑' k, b' k) / N := by field_simp
  · rw [habs, hT]
    have h1 := hM η hη0
    have h2 : η ^ (-s - 2) ≤ smearScale d N Λ ^ (-s - 2) :=
      Real.rpow_le_rpow_of_nonpos hl0 hη (by linarith)
    have hdiv := d47_lam_div hd hN hΛ (s + 2)
    have e : -s - 2 = -(s + 2) := by ring
    have h3 : ∑' k : Lattice d, Lattice.enorm k ^ 2 * d47_a ψ s b η k ≤
        M * smearScale d N Λ ^ (-(s + 2)) := by
      rw [← e]
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hM0)
    calc 4 * Real.pi ^ 2 * (∑' k : Lattice d, Lattice.enorm k ^ 2 * d47_a ψ s b η k) / N
        ≤ 4 * Real.pi ^ 2 * (M * smearScale d N Λ ^ (-(s + 2))) / N := by
          gcongr
      _ = 4 * Real.pi ^ 2 * M * (smearScale d N Λ ^ (-(s + 2)) / N) := by ring
      _ = 4 * Real.pi ^ 2 * M * Λ ^ ((s + 2) / d) * (N : ℝ) ^ ((s + 2) / d - 1) := by
          rw [hdiv]; ring

end HRS.MC.D47
