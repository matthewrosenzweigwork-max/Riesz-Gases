import HRS.MS.R2WinOrbTRD14

/-!
# S10.3 packet [C], assembly part 1: data bounds for the two terminal levels and the linear-layer reductions

Prefix `s103d_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103d_data`: for the density `ρ_τ ∈ U2Dec (N+3)`, the derivative `ρ'_τ ∈ U2Dec (N+1)` and a test function `φ ∈ SyN 3 (N+4)`:
  `L_τ φ ∈ DatD (N+2)` and `L_τ L_τ φ + Q_{ρ'_τ} φ ∈ Sy N` (jets decaying like `(1+‖x‖)⁻¹`), with constants linear in the data and independent of `τ`.
* `s103d_hLay_of_lin`, `s103d_timeReg_of_lin`: from a bound `M (l - e)` (resp. `M (t - τ)`) to the `ε`-`δ` forms used by `s103c_step`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul HRS.MS.Who HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.R2WinOrb
  HRS.MS.MovOsc

variable {d : ℕ}

theorem s103d_hLay_of_lin {N0 : ℕ} {fam : ℝ → ℝ → Euc d → ℝ} {χ : ℝ → Euc d → ℝ} {T1 M : ℝ} (hM : 0 ≤ M)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T1, ∀ e l : ℝ, 0 ≤ e → e < l → l ≤ T1 → e ≤ t → t ≤ l →
      Bd N0 (M * (l - e)) (fun y => (fam l e y - fam e e y) / (l - e) - χ t y)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T1, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ e l : ℝ, 0 ≤ e → e < l → l ≤ T1 →
      e ≤ t → t ≤ l → l - e < δ → Bd N0 ε (fun y => (fam l e y - fam e e y) / (l - e) - χ t y) := by
  intro t ht ε hε
  refine ⟨ε / (M + 1), by positivity, fun e l he hel hlT het htl hlδ => ?_⟩
  refine (h t ht e l he hel hlT het htl).mono_A ?_
  have h1 : M * (l - e) ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hlδ.le hM
  have h2 : M * (ε / (M + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  exact h1.trans h2

theorem s103d_timeReg_of_lin {N0 : ℕ} {t M : ℝ} {u : ℝ → Euc d → ℝ} (hM : 0 ≤ M)
    (h : ∀ τ ∈ Set.Icc (0 : ℝ) t, Bd N0 (M * (t - τ)) (fun y => u τ y - u t y)) :
    S103cTimeReg N0 t u := by
  intro ε hε
  refine ⟨ε / (M + 1), by positivity, fun τ hτ hlt => ?_⟩
  refine (h τ hτ).mono_A ?_
  have h1 : M * (t - τ) ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hlt.le hM
  have h2 : M * (ε / (M + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  exact h1.trans h2

theorem s103d_data {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ) (N : ℕ) {L : ℝ}
    (hL : (d : ℝ) + ((N + 2 : ℕ) : ℝ) + s + 3 < L) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ (Aρ Ad Aφ : ℝ), 0 ≤ Aρ → 0 ≤ Ad → 0 ≤ Aφ →
      ∀ (ρ ρ' : ℝ → Euc d → ℝ) (τ : ℝ) (φ : Euc d → ℝ),
        U2Dec (N + 3) L Aρ (ρ τ) → U2Dec (N + 1) L Ad (ρ' τ) → SyN 3 (N + 4) Aφ φ →
        DatD (N + 2) (C2 * ((1 + Aρ) * Aφ))
          (fun y => generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ φ y) ∧
        Sy N (C2 * ((1 + Aρ) ^ 2 * (1 + Ad) * (1 + Aφ)))
          (fun y => generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ
              (fun x => generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ φ x) y +
            s103nQ d s (ρ' τ) φ y) := by
  have hLN : (d : ℝ) + N + s + 3 < L := by
    have : (N : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by push_cast; linarith
    linarith
  obtain ⟨Cg1, hCg10, hCg1⟩ := s103c_g1_datd hd hs0 hsd a β (N + 2) hL
  obtain ⟨Cq, hCq0, hCq⟩ := s103b_q_sy hd hs0 hsd N hLN
  set c0 : ℝ := |β⁻¹| * d + d * (|a| * ((N : ℝ) + 1)) with hc0
  have hc00 : 0 ≤ c0 := by positivity
  refine ⟨(c0 + Cq + 1) * Cg1 + Cq, by positivity, fun Aρ Ad Aφ hAρ hAd hAφ ρ ρ' τ φ hρ hρ' hφ => ?_⟩
  set Cf := (quadraticGradientDyn d s a β).coeff ρ with hCf
  have hψ : DatD (N + 2) (Cg1 * ((1 + Aρ) * Aφ)) (fun y => generatorW Cf τ φ y) := by
    have := hCg1 Aρ Aφ (ρ τ) φ hAρ hAφ hρ hφ
    have e : (fun y => generatorW Cf τ φ y) =
        fun x => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ τ)) 0 φ x :=
      funext fun x => s103n_gen_frozen ρ τ φ x
    rw [e]; exact this
  refine ⟨by
    have e : Cg1 * ((1 + Aρ) * Aφ) ≤ ((c0 + Cq + 1) * Cg1 + Cq) * ((1 + Aρ) * Aφ) := by
      have h0 : 0 ≤ (1 + Aρ) * Aφ := by positivity
      nlinarith [mul_nonneg hc00 (mul_nonneg hCg10 h0), mul_nonneg hCq0 (mul_nonneg hCg10 h0), mul_nonneg hCq0 h0]
    exact hψ.mono_A e, ?_⟩
  -- the second datum
  have hA1 : 0 ≤ Cg1 * ((1 + Aρ) * Aφ) := hψ.nonneg
  have hρ1 : U2Dec (N + 1) L Aρ (ρ τ) := ult_U2Dec_mono hρ (by omega)
  have hL0 := s103c_L0_sy (N := N) a β hψ
  have hQ1 := hCq Aρ (ρ τ) hAρ hρ1 (Cg1 * ((1 + Aρ) * Aφ)) (fun y => generatorW Cf τ φ y) hψ.1
    (fun i h1 h2 y => hψ.2.1 i (by omega) y)
  have hφ2 : ContDiff ℝ ((N + 2 : ℕ) : WithTop ℕ∞) φ :=
    hφ.1.of_le (by exact_mod_cast (by omega : N + 2 ≤ N + 4))
  have hQ2 := hCq Ad (ρ' τ) hAd hρ' Aφ φ hφ2 (fun i h1 h2 y => by
    have := hφ.bd.2 i (by omega) y
    exact this)
  have hsplit : (fun y => generatorW Cf τ (fun x => generatorW Cf τ φ x) y) =
      fun y => s83_L0 a β⁻¹ (fun x => generatorW Cf τ φ x) y +
        s103bQ d s (ρ τ) (fun x => generatorW Cf τ φ x) y :=
    funext fun y => s103b_gen_split s a β ρ τ _ y
  have hnQ : (fun y => s103nQ d s (ρ' τ) φ y) = s103bQ d s (ρ' τ) φ :=
    funext fun y => s103c_nQ_eq _ _ y
  have e1 : (fun y => generatorW Cf τ (fun x => generatorW Cf τ φ x) y + s103nQ d s (ρ' τ) φ y) =
      fun y => (s83_L0 a β⁻¹ (fun x => generatorW Cf τ φ x) y +
        s103bQ d s (ρ τ) (fun x => generatorW Cf τ φ x) y) + s103bQ d s (ρ' τ) φ y := by
    funext y
    rw [s103b_gen_split s a β ρ τ _ y, s103c_nQ_eq]
  rw [e1]
  have hsum := (hL0.add hQ1).add hQ2
  refine hsum.mono_A ?_
  have hX : 0 ≤ (1 + Aρ) ^ 2 * (1 + Ad) * (1 + Aφ) := by positivity
  have h0 : 0 ≤ (1 + Aρ) * Aφ := by positivity
  have hb1 : (c0 * (Cg1 * ((1 + Aρ) * Aφ)) + Cq * Aρ * (Cg1 * ((1 + Aρ) * Aφ))) ≤
      (c0 + Cq) * Cg1 * ((1 + Aρ) ^ 2 * (1 + Ad) * (1 + Aφ)) := by
    have k1 : (1 + Aρ) * Aφ ≤ (1 + Aρ) ^ 2 * (1 + Ad) * (1 + Aφ) := by
      have a1 : (1 + Aρ) ≤ (1 + Aρ) ^ 2 := by nlinarith
      have a2 : (1 : ℝ) ≤ (1 + Ad) := by linarith
      have a3 : Aφ ≤ 1 + Aφ := by linarith
      calc (1 + Aρ) * Aφ ≤ (1 + Aρ) ^ 2 * (1 + Aφ) :=
            mul_le_mul a1 a3 hAφ (by positivity)
        _ ≤ (1 + Aρ) ^ 2 * (1 + Ad) * (1 + Aφ) := by
            have : (1 + Aρ) ^ 2 ≤ (1 + Aρ) ^ 2 * (1 + Ad) := by nlinarith [sq_nonneg (1 + Aρ)]
            exact mul_le_mul_of_nonneg_right this (by positivity)
    have k2 : Aρ * ((1 + Aρ) * Aφ) ≤ (1 + Aρ) * ((1 + Aρ) * Aφ) := by
      exact mul_le_mul_of_nonneg_right (by linarith) h0
    have k3 : (1 + Aρ) * ((1 + Aρ) * Aφ) ≤ (1 + Aρ) ^ 2 * (1 + Ad) * (1 + Aφ) := by
      have : (1 + Aρ) * ((1 + Aρ) * Aφ) = (1 + Aρ) ^ 2 * Aφ := by ring
      rw [this]
      have : (1 + Aρ) ^ 2 * Aφ ≤ (1 + Aρ) ^ 2 * (1 + Ad) * (1 + Aφ) := by
        have a2 : (1 : ℝ) ≤ (1 + Ad) := by linarith
        have a3 : Aφ ≤ 1 + Aφ := by linarith
        calc (1 + Aρ) ^ 2 * Aφ ≤ (1 + Aρ) ^ 2 * (1 + Aφ) :=
              mul_le_mul_of_nonneg_left a3 (by positivity)
          _ ≤ (1 + Aρ) ^ 2 * (1 + Ad) * (1 + Aφ) := by
              have : (1 + Aρ) ^ 2 ≤ (1 + Aρ) ^ 2 * (1 + Ad) := by nlinarith [sq_nonneg (1 + Aρ)]
              exact mul_le_mul_of_nonneg_right this (by positivity)
      exact this
    have hcc : 0 ≤ c0 * Cg1 := mul_nonneg hc00 hCg10
    have hcq : 0 ≤ Cq * Cg1 := mul_nonneg hCq0 hCg10
    calc c0 * (Cg1 * ((1 + Aρ) * Aφ)) + Cq * Aρ * (Cg1 * ((1 + Aρ) * Aφ)) =
        c0 * Cg1 * ((1 + Aρ) * Aφ) + Cq * Cg1 * (Aρ * ((1 + Aρ) * Aφ)) := by ring
      _ ≤ c0 * Cg1 * ((1 + Aρ) ^ 2 * (1 + Ad) * (1 + Aφ)) +
          Cq * Cg1 * ((1 + Aρ) ^ 2 * (1 + Ad) * (1 + Aφ)) := by
          exact add_le_add (mul_le_mul_of_nonneg_left k1 hcc) (mul_le_mul_of_nonneg_left (k2.trans k3) hcq)
      _ = _ := by ring
  have hb2 : Cq * Ad * Aφ ≤ Cq * ((1 + Aρ) ^ 2 * (1 + Ad) * (1 + Aφ)) := by
    have : Ad * Aφ ≤ (1 + Aρ) ^ 2 * (1 + Ad) * (1 + Aφ) := by
      have b1 : 1 ≤ (1 + Aρ) ^ 2 := one_le_pow₀ (by linarith)
      calc Ad * Aφ ≤ (1 + Ad) * (1 + Aφ) := mul_le_mul (by linarith) (by linarith) hAφ (by linarith)
        _ ≤ (1 + Aρ) ^ 2 * ((1 + Ad) * (1 + Aφ)) := by
            have : 0 ≤ (1 + Ad) * (1 + Aφ) := by positivity
            nlinarith
        _ = _ := by ring
    calc Cq * Ad * Aφ = Cq * (Ad * Aφ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hCq0
  calc (c0 * (Cg1 * ((1 + Aρ) * Aφ)) + Cq * Aρ * (Cg1 * ((1 + Aρ) * Aφ))) + Cq * Ad * Aφ ≤
      (c0 + Cq) * Cg1 * ((1 + Aρ) ^ 2 * (1 + Ad) * (1 + Aφ)) +
        Cq * ((1 + Aρ) ^ 2 * (1 + Ad) * (1 + Aφ)) := add_le_add hb1 hb2
    _ ≤ _ := by nlinarith [mul_nonneg hCg10 hX]

end HRS.MS.R2WinOrbNL

end
