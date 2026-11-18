import HRS.MS.UniqE3h

/-!
# E3 of `UniqPlan.md`, part 9: packaged statements (D), (T), and the `forwardPairing` form

* `e3_diffusion` **(D)**: `2 ν ∫ u Δφ_σ ≤ -ν ∫ ς |∇z_ε|² + ν Γ ∫_{B̄(Ψ_σ c, 2L)} z_ε²`.
* `e3_transport` **(T)**: `|2 (-⟨u, ∑ ∂_i(b_i φ_σ)⟩) + ∫ (b·∇ς) z_ε² + ∫ (div b) ς z_ε²| ≤ C₂ ε B²`.
* (C) is `e3_ball_le_cellEnergy` / `e3_integral_le_cellEnergy` / `e3_cellEnergy_le` (file `UniqE3g`, `UniqE3c`).
* `e3_forwardPairing_form`: the combined estimate for `forwardPairing + fpNonloc`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3

variable {d : ℕ}

/-- **(D)** diffusion part. `Γ` depends only on `χ, Cb, t`. -/
theorem e3_diffusion {D : WholeDyn d} (hν : 0 ≤ D.invβ) {t : ℝ} {m : ℕ} {Cb K : ℝ}
    {χ χh : Euc d → ℝ} {b : ℝ → Euc d → Euc d} {Ψ : ℝ → Euc d → Euc d} (hχ : IsUlocCutoff χ)
    (hCb : 0 ≤ Cb) (hF : FlowBundle d m Cb t χ χh b Ψ K) :
    ∃ Γ : ℝ, 0 ≤ Γ ∧ ∀ (u : Euc d → ℝ) (B : ℝ), LocMass B u →
      ∀ σ ∈ Icc (0 : ℝ) t, ∀ ε : ℝ, 0 < ε → ∀ c : Euc d,
        2 * fpDiff D u (phiTest d χ Ψ σ c ε u) ≤
          -(D.invβ * ∫ x, varsigma χ Ψ σ c x * ‖fderiv ℝ (moll d ε u) x‖ ^ 2) +
            D.invβ * Γ * ∫ x in closedBall (Ψ σ c) (2 * Real.exp (Cb * t)), moll d ε u x ^ 2 := by
  obtain ⟨Γ, hΓ0, hΓ⟩ := e3_varsigma_grad_sq hχ hF.flow hCb
  refine ⟨Γ, hΓ0, fun u B hLM σ hσ ε hε c => ?_⟩
  rw [phiTest_eq_moll]
  exact e3_diffusion_bound hν hε hLM (hF.contDiff σ hσ c) (hF.compact_supp σ hσ c)
    (fun x => (hF.range σ hσ c x).1) hΓ0 (hΓ σ hσ c) (isCompact_closedBall _ _) (hF.supp σ hσ c)

/-- **(T)** transport part: `2(-⟨u, ∑∂_i(b_iφ_σ)⟩) + ∫(b·∇ς)z_ε² = -∫(div b)ς z_ε² + R_T`, `|R_T| ≤ C₂ ε B²`. -/
theorem e3_transport {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} {t : ℝ} (ht : 0 ≤ t) {m : ℕ}
    (hm : 1 ≤ m) {Cb K : ℝ} {χ χh : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d} (hχ : IsUlocCutoff χ)
    (hb : IsAdvectingDrift m Cb t (fun σ => meanFieldDriftW D (ρ (t - σ))))
    (hF : FlowBundle d m Cb t χ χh (fun σ => meanFieldDriftW D (ρ (t - σ))) Ψ K) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ∀ (u : Euc d → ℝ) (B : ℝ), 0 ≤ B → ulocNormE 1 χ u ≤ ENNReal.ofReal B →
        ∀ σ ∈ Icc (0 : ℝ) t, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ c : Euc d,
          |2 * (-fpTrans (meanFieldDriftW D (ρ (t - σ))) u (phiTest d χ Ψ σ c ε u)) +
              (∫ x, inner ℝ (meanFieldDriftW D (ρ (t - σ)) x) (gradient (varsigma χ Ψ σ c) x) *
                moll d ε u x ^ 2) +
              ∫ x, (∑ i, D1 i (fun y => meanFieldDriftW D (ρ (t - σ)) y i) x) *
                varsigma χ Ψ σ c x * moll d ε u x ^ 2| ≤ C₂ * ε * B ^ 2 := by
  have hCb : 0 ≤ Cb := uc3_Cb_nonneg ht hb
  obtain ⟨N₁, hN₁⟩ := e3_moll_sq_set_le d (2 * Real.exp (Cb * t) + 1)
  obtain ⟨N₂, hN₂⟩ := e3_grad_sq_set_le d (2 * Real.exp (Cb * t) + 1)
  set Q : ℝ := (3 / 2) * N₁ + K ^ 2 * N₁ + N₂ with hQ
  refine ⟨2 * d * Cb * Q, by positivity, ?_⟩
  intro u B hB hu σ hσ ε hε hε1 c
  have hLM : LocMass B u := locMass_of_ulocNormE (m := 1) hχ hB hu
  have hdrift : DriftFacts (meanFieldDriftW D (ρ (t - σ))) Cb := driftFacts_of_advecting hm hb hσ
  have hς1 : ContDiff ℝ 1 (varsigma χ Ψ σ c) := (hF.contDiff σ hσ c).of_le (by norm_num)
  have hςc : HasCompactSupport (varsigma χ Ψ σ c) := hF.compact_supp σ hσ c
  have hSball : closedBall (Ψ σ c) (2 * Real.exp (Cb * t)) ⊆
      ball (Ψ σ c) (2 * Real.exp (Cb * t) + 1) := closedBall_subset_ball (by linarith)
  rw [phiTest_eq_moll]
  have hinner : ∀ x, inner ℝ (meanFieldDriftW D (ρ (t - σ)) x) (gradient (varsigma χ Ψ σ c) x) =
      ∑ i, meanFieldDriftW D (ρ (t - σ)) x i * D1 i (varsigma χ Ψ σ c) x := fun x =>
    e3_inner_gradient _ _ _
  simp_rw [hinner]
  have hTr := e3_transport_identity hdrift.smooth hε hLM hς1 hςc
  have hG : LocMass B (fun y => ‖u y‖) :=
    ⟨hLM.1.norm, fun c' => by simpa only [enorm_norm] using hLM.2 c'⟩
  have hR := e3_rem_total_bound hdrift hCb hε hLM hς1 (fun x => (hF.range σ hσ c x).1)
    (fun x => (hF.range σ hσ c x).2) (fun x => hF.fderiv_le σ hσ c x) (isCompact_closedBall _ _)
    (hF.supp σ hσ c)
    (hN₁ ε hε hε1 B _ hG (Ψ σ c) _ hSball) (hN₁ ε hε hε1 B u hLM (Ψ σ c) _ hSball)
    (hN₂ hχ u B hB hu ε hε hε1 (Ψ σ c) _ hSball)
  have e : 2 * (-fpTrans (meanFieldDriftW D (ρ (t - σ))) u
        (moll d ε (fun x => varsigma χ Ψ σ c x * moll d ε u x))) +
      (∫ x, (∑ i, meanFieldDriftW D (ρ (t - σ)) x i * D1 i (varsigma χ Ψ σ c) x) *
        moll d ε u x ^ 2) +
      ∫ x, (∑ i, D1 i (fun y => meanFieldDriftW D (ρ (t - σ)) y i) x) *
        varsigma χ Ψ σ c x * moll d ε u x ^ 2 =
      2 * ∑ i, ∫ x, u x * transRem d ε (meanFieldDriftW D (ρ (t - σ)))
        (fun x => varsigma χ Ψ σ c x * moll d ε u x) i x := by
    linarith
  rw [e, abs_mul, abs_two]
  have : 2 * d * Cb * Q * ε * B ^ 2 = 2 * (d * (ε * Cb * (B ^ 2 * Q))) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left hR (by norm_num)

/-- The combined estimate in terms of `forwardPairing` (diffusion + transport + nonlocal): the nonlocal
part `fpNonloc` is added back. -/
theorem e3_forwardPairing_form {D : WholeDyn d} (hν : 0 ≤ D.invβ) {ρ : ℝ → Euc d → ℝ} {t : ℝ}
    (ht : 0 ≤ t) {m : ℕ} (hm : 1 ≤ m) {Cb K : ℝ} {χ χh : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d}
    (hχ : IsUlocCutoff χ)
    (hb : IsAdvectingDrift m Cb t (fun σ => meanFieldDriftW D (ρ (t - σ))))
    (hF : FlowBundle d m Cb t χ χh (fun σ => meanFieldDriftW D (ρ (t - σ))) Ψ K) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ (u : Euc d → ℝ) (B : ℝ), 0 ≤ B → ulocNormE 1 χ u ≤ ENNReal.ofReal B →
        ∀ σ ∈ Icc (0 : ℝ) t, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ c : Euc d,
          2 * (forwardPairing D ρ t σ u (phiTest d χ Ψ σ c ε u) +
              fpNonloc D ρ t σ u (phiTest d χ Ψ σ c ε u)) +
            ∫ x, inner ℝ (meanFieldDriftW D (ρ (t - σ)) x) (gradient (varsigma χ Ψ σ c) x) *
              moll d ε u x ^ 2 ≤
          -(D.invβ * ∫ x, varsigma χ Ψ σ c x * ‖fderiv ℝ (moll d ε u) x‖ ^ 2) +
            C₁ * (D.invβ + 1) * (cellEnergy χ Ψ σ (moll d ε u)).toReal + C₂ * ε * B ^ 2 := by
  obtain ⟨C₁, C₂, h1, h2, h⟩ := e3_diffusion_transport hν ht hm hχ hb hF
  refine ⟨C₁, C₂, h1, h2, fun u B hB hu σ hσ ε hε hε1 c => ?_⟩
  have := (h u B hB hu σ hσ ε hε hε1 c).2
  rw [forwardPairing_split]
  linarith

end HRS.MS.UniqE3
