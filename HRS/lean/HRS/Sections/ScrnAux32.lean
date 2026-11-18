import HRS.Sections.ScrnAux31

/-!
# Packet SCRN, part 32: norms of a decayed copy `g` of the mesoscopic test

`ScrnDecay ψ g θ`: `|ĝ| ≤ |ψ̂|` and `|ĝ(k)| ≤ θ|ψ̂(k)|` for `k ≠ 0` (this is the situation of `f^r`, with
`θ = e^{-(t-r)λ_*}`).  For `ψ = mesoTest d ℓ x₀ φ`, `ℓ ≤ 1`, the sup norms of `D¹g, D²g`, the `ℓ¹`/weighted
`ℓ²` sums of `ĝ` are bounded by `θ` times the powers of `ℓ` of `ψ`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace HRS

variable {d : ℕ}

open PDE

/-- `g` is a `θ`-decayed copy of `ψ` on the non-zero modes. -/
structure ScrnDecay (ψ g : Torus d → ℝ) (θ : ℝ) : Prop where
  nonneg : 0 ≤ θ
  le_one : θ ≤ 1
  cont : Continuous g
  le : ∀ k, ‖coeffOf g k‖ ≤ ‖coeffOf ψ k‖
  decay : ∀ k, k ≠ 0 → ‖coeffOf g k‖ ≤ θ * ‖coeffOf ψ k‖

/-- Weighted `ℓ²` sums of the coefficients of a decayed copy. -/
theorem scrn_decay_wsum (hd : 0 < d) (x₀ : Euc d) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∀ (g : Torus d → ℝ) (θ : ℝ),
      ScrnDecay (mesoTest d ℓ x₀ φ) g θ →
      Summable (fun k : Lattice d => (2 * Real.pi * Lattice.enorm k) ^ r * ‖coeffOf g k‖ ^ 2) ∧
      ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ r * ‖coeffOf g k‖ ^ 2 ≤
        (θ * C * ℓ ^ (-r / 2)) ^ 2 := by
  obtain ⟨C0, hC0, hW⟩ := scrn_psi_wsum hd x₀ hφ hc (r := r) hr.le (e := 2) (by norm_num)
  refine ⟨Real.sqrt ((2 * Real.pi) ^ r * C0), Real.sqrt_nonneg _, fun ℓ hℓ hℓ1 g θ hθ => ?_⟩
  obtain ⟨hs, hsum⟩ := hW ℓ hℓ hℓ1
  have hterm : ∀ k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ r * ‖coeffOf g k‖ ^ 2 ≤
      θ ^ 2 * ((2 * Real.pi) ^ r * (Lattice.enorm k ^ r * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ ^ 2)) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [scrn_enorm_zero]
      simp [Real.zero_rpow hr.ne']
    · have hx : 0 ≤ Lattice.enorm k := norm_nonneg _
      rw [Real.mul_rpow (by positivity) hx]
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (hθ.decay k hk) 2
      have h2 : (2 * Real.pi) ^ r * Lattice.enorm k ^ r ≥ 0 := by positivity
      calc (2 * Real.pi) ^ r * Lattice.enorm k ^ r * ‖coeffOf g k‖ ^ 2
          ≤ (2 * Real.pi) ^ r * Lattice.enorm k ^ r * (θ * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖) ^ 2 :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = _ := by ring
  have hs' : Summable (fun k : Lattice d => θ ^ 2 * ((2 * Real.pi) ^ r *
      (Lattice.enorm k ^ r * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ ^ 2))) :=
    (hs.mul_left _).mul_left _
  have hsg : Summable (fun k : Lattice d => (2 * Real.pi * Lattice.enorm k) ^ r * ‖coeffOf g k‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (scrn_two_pi_enorm_nonneg k) _)
      (sq_nonneg _)) hterm hs'
  refine ⟨hsg, ?_⟩
  calc ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ r * ‖coeffOf g k‖ ^ 2
      ≤ ∑' k : Lattice d, θ ^ 2 * ((2 * Real.pi) ^ r *
          (Lattice.enorm k ^ r * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ ^ 2)) := hsg.tsum_le_tsum hterm hs'
    _ = θ ^ 2 * ((2 * Real.pi) ^ r * ∑' k : Lattice d,
          Lattice.enorm k ^ r * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ ^ 2) := by
        rw [tsum_mul_left, tsum_mul_left]
    _ ≤ θ ^ 2 * ((2 * Real.pi) ^ r * (C0 * ℓ ^ ((d : ℝ) * (2 : ℕ) / 2 - ((d : ℝ) + r)))) := by
        gcongr
    _ = (θ * Real.sqrt ((2 * Real.pi) ^ r * C0) * ℓ ^ (-r / 2)) ^ 2 := by
        have e1 : (d : ℝ) * (2 : ℕ) / 2 - ((d : ℝ) + r) = -r := by push_cast; ring
        rw [e1]
        have e2 : (ℓ ^ (-r / 2)) ^ 2 = ℓ ^ (-r) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ.le]; congr 1; push_cast; ring
        have e3 : Real.sqrt ((2 * Real.pi) ^ r * C0) ^ 2 = (2 * Real.pi) ^ r * C0 :=
          Real.sq_sqrt (by positivity)
        calc θ ^ 2 * ((2 * Real.pi) ^ r * (C0 * ℓ ^ (-r))) =
            θ ^ 2 * (Real.sqrt ((2 * Real.pi) ^ r * C0) ^ 2) * (ℓ ^ (-r / 2)) ^ 2 := by
              rw [e2, e3]; ring
          _ = _ := by ring

/-- Sup norms of `D⁰, D¹, D²` and the `ℓ¹` sum `∑ 2π|k| |ĝ|` of a decayed copy. -/
theorem scrn_decay_deriv (hd : 0 < d) (x₀ : Euc d) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∀ (g : Torus d → ℝ) (θ : ℝ),
      ScrnDecay (mesoTest d ℓ x₀ φ) g θ →
      Torus.IsCk 2 g ∧
      (∀ y : Euc d, ‖iteratedFDeriv ℝ 0 (Torus.lift g) y‖ ≤ C * ℓ ^ (-((d : ℝ) / 2))) ∧
      (∀ y : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift g) y‖ ≤ θ * C * ℓ ^ (-((d : ℝ) / 2) - 1)) ∧
      (∀ y : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift g) y‖ ≤ θ * C * ℓ ^ (-((d : ℝ) / 2) - 2)) ∧
      (Summable fun k : Lattice d => 2 * Real.pi * Lattice.enorm k * ‖coeffOf g k‖) ∧
      ∑' k : Lattice d, 2 * Real.pi * Lattice.enorm k * ‖coeffOf g k‖ ≤
        θ * C * ℓ ^ (-((d : ℝ) / 2) - 1) := by
  obtain ⟨CS, hCS, hS⟩ := scrn_S_bound hd x₀ hφ hc
  refine ⟨2 * CS, by positivity, fun ℓ hℓ hℓ1 g θ hθ => ?_⟩
  have hsum : ∀ i : ℕ, i ≤ 2 → Summable fun k : Lattice d =>
      (2 * Real.pi * Lattice.enorm k) ^ i * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ :=
    fun i hi => (hS ℓ hℓ hℓ1 i hi).1
  obtain ⟨hCk, hD1, hD2⟩ := scrn_trans_deriv hθ.cont hθ.nonneg hθ.le hθ.decay hsum
  have hp1 : 0 ≤ ℓ ^ (-((d : ℝ) / 2) - 1) := Real.rpow_nonneg hℓ.le _
  have hp2 : 0 ≤ ℓ ^ (-((d : ℝ) / 2) - 2) := Real.rpow_nonneg hℓ.le _
  have hp0 : 0 ≤ ℓ ^ (-((d : ℝ) / 2)) := Real.rpow_nonneg hℓ.le _
  have hS1 := (hS ℓ hℓ hℓ1 1 (by norm_num)).2
  have hS2 := (hS ℓ hℓ hℓ1 2 le_rfl).2
  have hS0 := (hS ℓ hℓ hℓ1 0 (by norm_num)).2
  have hS1s := (hS ℓ hℓ hℓ1 1 (by norm_num)).1
  refine ⟨hCk, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    -- sup norm from the `ℓ¹` sum of all modes
    have hsg : ∀ i : ℕ, i ≤ 0 → Summable fun k : Lattice d =>
        (2 * Real.pi * Lattice.enorm k) ^ i * ‖coeffOf g k‖ := by
      intro i hi
      have : i = 0 := by omega
      subst this
      simp only [pow_zero, one_mul]
      refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) hθ.le ?_
      simpa using hsum 0 (by norm_num)
    obtain ⟨-, hb⟩ := scrn_iteratedFDeriv_le hθ.cont (j := 0) hsg
    refine (hb 0 le_rfl y).trans ?_
    simp only [pow_zero, one_mul]
    have h1 : ∑' k : Lattice d, ‖coeffOf g k‖ ≤ ∑' k : Lattice d, ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ := by
      refine (hsg 0 le_rfl |>.congr (fun k => by simp)).tsum_le_tsum hθ.le ?_
      simpa using hsum 0 (by norm_num)
    have h2 : ∑' k : Lattice d, ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ ≤ CS * ℓ ^ (-((d : ℝ) / 2) - (0 : ℕ)) := by
      simpa using hS0
    have h3 : (∑' k : Lattice d, ‖coeffOf g k‖) ≤ CS * ℓ ^ (-((d : ℝ) / 2)) := by
      simpa using h1.trans h2
    nlinarith [h3]
  · intro y
    refine (hD1 y).trans ?_
    have : ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ 1 * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ ≤
        CS * ℓ ^ (-((d : ℝ) / 2) - 1) := by simpa using hS1
    have h0 := hθ.nonneg
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  · intro y
    refine (hD2 y).trans ?_
    have : ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ 2 * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ ≤
        CS * ℓ ^ (-((d : ℝ) / 2) - 2) := by simpa using hS2
    have h0 := hθ.nonneg
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  · -- the `ℓ¹` sum with the weight `2π|k|`
    have hle : ∀ k : Lattice d, 2 * Real.pi * Lattice.enorm k * ‖coeffOf g k‖ ≤
        θ * ((2 * Real.pi * Lattice.enorm k) ^ 1 * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖) := by
      intro k
      by_cases hk : k = 0
      · subst hk; rw [scrn_enorm_zero]; simp
      · calc 2 * Real.pi * Lattice.enorm k * ‖coeffOf g k‖
            ≤ 2 * Real.pi * Lattice.enorm k * (θ * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖) :=
              mul_le_mul_of_nonneg_left (hθ.decay k hk) (scrn_two_pi_enorm_nonneg k)
          _ = _ := by ring
    exact Summable.of_nonneg_of_le (fun k => mul_nonneg (scrn_two_pi_enorm_nonneg k) (norm_nonneg _))
      hle (hS1s.mul_left θ)
  · have hle : ∀ k : Lattice d, 2 * Real.pi * Lattice.enorm k * ‖coeffOf g k‖ ≤
        θ * ((2 * Real.pi * Lattice.enorm k) ^ 1 * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖) := by
      intro k
      by_cases hk : k = 0
      · subst hk; rw [scrn_enorm_zero]; simp
      · calc 2 * Real.pi * Lattice.enorm k * ‖coeffOf g k‖
            ≤ 2 * Real.pi * Lattice.enorm k * (θ * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖) :=
              mul_le_mul_of_nonneg_left (hθ.decay k hk) (scrn_two_pi_enorm_nonneg k)
          _ = _ := by ring
    have hsg : Summable fun k : Lattice d => 2 * Real.pi * Lattice.enorm k * ‖coeffOf g k‖ :=
      Summable.of_nonneg_of_le (fun k => mul_nonneg (scrn_two_pi_enorm_nonneg k) (norm_nonneg _))
        hle (hS1s.mul_left θ)
    calc ∑' k : Lattice d, 2 * Real.pi * Lattice.enorm k * ‖coeffOf g k‖
        ≤ ∑' k : Lattice d, θ * ((2 * Real.pi * Lattice.enorm k) ^ 1 *
            ‖coeffOf (mesoTest d ℓ x₀ φ) k‖) := hsg.tsum_le_tsum hle (hS1s.mul_left θ)
      _ = θ * ∑' k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ 1 *
            ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ := tsum_mul_left
      _ ≤ θ * (CS * ℓ ^ (-((d : ℝ) / 2) - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ hθ.nonneg
          simpa using hS1
      _ ≤ θ * (2 * CS) * ℓ ^ (-((d : ℝ) / 2) - 1) := by
          have := mul_nonneg hθ.nonneg (mul_nonneg hCS hp1)
          nlinarith

end HRS
