import HRS.Commutator.Torus.Defs
import HRS.Commutator.Torus.Layer
import HRS.Commutator.Torus.External
import HRS.Commutator.Torus.TBRAux1
import HRS.Commutator.Torus.TBRAux2
import HRS.Commutator.Torus.TUNITAux3
import HRS.Commutator.Torus.TUNITAux6
import HRS.Commutator.Torus.TUNITAux8
import HRS.Commutator.Torus.TUNITBAux2

/-!
# Torus sub-Coulomb commutator: unit-scale pieces, Proposition 1.2 and Theorem 1.1 on `𝕋^d`

Torus analogue of `Whole/Unit.lean` + `Whole/Assembly.lean`.  **Proved here from the statements of
`Layer.lean`/`External.lean`**: `high_bound_T`, `unit_estimate_T`, `scaleQT_mono`, `scale_estimate_T` (Proposition 1.2 for
bounded densities, all `η ∈ (0,1]`), `subcoulomb_commutator_scale_T` (Proposition 1.2), `torus_subcoulomb_commutator`
(Theorem 1.1).

Deviations from the `ℝ^d` note (reasons in `Defs.lean`): repository kernel (no `s⁻¹`), `η ∈ (0,1]`, no log hypothesis, signed `ρ`
as a function, `X ∉ collisionSet`, torus transport norm (`IsFracDeriv`, zero mode removed), `λ ≤ 1` automatic (`‖μ‖_∞ ≥ 1`).
The lemma layer holds for `η ≤ η₀(d,s)`; the passage to `(η₀, 1]` is `scaleQT_mono` (no scaling of the torus is needed).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d N : ℕ} {s : ℝ}

/-- `commAT = 𝒞_g(v,ν)` (deleted-diagonal formula = iterated integral over `ν = μ_N-μ`; `∇g` odd). -/
theorem commAT_eq_CcommT (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (ρ : Torus d → ℝ)
    (hρ : BddDensityT ρ) {N : ℕ} (hN : 1 ≤ N) (X : Config d N) (hX : X ∉ collisionSet d N)
    (v : Torus d → Euc d) (L : ℝ) (hL : 0 ≤ L) (hv : IsLipschitzVF L v) :
    commAT s X ρ v = CcommT (periodicRieszGrad d s) v (chargeT X ρ) := by
  exact tunit_commAT_eq hd hs0 hsd ρ hρ hN X v L hL hv

/-- `(5.full-decomposition)` at scale `η`. -/
theorem CcommT_decomp (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ 1) (ρ : Torus d → ℝ) (hρ : BddDensityT ρ) {N : ℕ} (hN : 1 ≤ N) (X : Config d N)
    (hX : X ∉ collisionSet d N) (v : Torus d → Euc d) (L : ℝ) (hL : 0 ≤ L) (hv : IsLipschitzVF L v) :
    CcommT (periodicRieszGrad d s) v (chargeT X ρ) =
      CcommT (ghiForceT s η) v (chargeT X ρ) + CcommT (gloForceT s η) (PleqT η v) (chargeT X ρ) +
        CcommT (gloForceT s η) (PgtT η v) (chargeT X ρ) := by
  exact tunit_decomp hd hs0 hsd η hη hη1 ρ hρ hN X v L hL hv

/-- `(5.remainderbound)` on the torus: `|𝒞_{g_>}(v,ν)| ≲ C(v) Q_η` (Lemma 3.1, `inhomogeneous_T`, `energy_control_T`). -/
theorem remainder_bound_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ 0 < C ∧ ∀ p : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ ρ : Torus d → ℝ, BddDensityT ρ → ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N →
      ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
        |CcommT (ghiForceT s η) v (chargeT X ρ)| ≤ C * K * scaleQT s Cp p η X ρ := by
  exact tunitb_rem_main hd hs0 hsd

/-- `(5.lowpartbound)` on the torus (`low_velocity_T`, `scoercive_T`, `energy_control_T`). -/
theorem low_bound_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ 0 < C ∧ ∀ p : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ ρ : Torus d → ℝ, BddDensityT ρ → ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N →
      ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
        |CcommT (gloForceT s η) (PleqT η v) (chargeT X ρ)| ≤ C * K * scaleQT s Cp p η X ρ := by
  exact tunitb_low_main hd hs0 hsd

/-- `(5.highidentity)` on the torus, `u = ∇g_≤ * ν`. -/
theorem high_identity_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ 1) (ρ : Torus d → ℝ) (hρ : BddDensityT ρ) {N : ℕ} (hN : 1 ≤ N) (X : Config d N)
    (hX : X ∉ collisionSet d N) (v : Torus d → Euc d) (L : ℝ) (hL : 0 ≤ L) (hv : IsLipschitzVF L v) :
    CcommT (gloForceT s η) (PgtT η v) (chargeT X ρ) =
      (2 / (N : ℝ)) * ∑ i, inner ℝ (PgtT η v (X i)) ((chargeT X ρ).convForce (gloForceT s η) (X i)) -
        2 * ∫ x, ρ x * inner ℝ (PgtT η v x) ((chargeT X ρ).convForce (gloForceT s η) x) := by
  exact tunit_high_identity hd hs0 hsd η hη hη1 ρ hρ hN X v L hL hv

/-- `(5.atomicclosing)` on the torus: Hölder for sequences over the `≈η^{-d}` cells with `energy_control_T (d)`,
`vhi_cell_sampling_T`, `usample_T`, `potential_T`, `scoercive_T` (all powers of `η` cancel). -/
theorem high_particles_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ 0 < C ∧ ∀ p : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ ρ : Torus d → ℝ, BddDensityT ρ → ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N →
      ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
        (1 / (N : ℝ)) * ∑ i, |inner ℝ (PgtT η v (X i))
            ((chargeT X ρ).convForce (gloForceT s η) (X i))| ≤ C * K * scaleQT s Cp p η X ρ := by
  exact tunit_particles_main hd hs0 hsd

/-- `(5.backgroundclosing)` on the torus: Sobolev duality, `product_T`, `energy_control_T (c)`. -/
theorem high_background_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ 0 < C ∧ ∀ p : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ ρ : Torus d → ℝ, BddDensityT ρ → ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N →
      ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
        |∫ x, ρ x * inner ℝ (PgtT η v x) ((chargeT X ρ).convForce (gloForceT s η) x)| ≤
          C * K * scaleQT s Cp p η X ρ := by
  exact tunit_background_main hd hs0 hsd

/-- The high-frequency transport bound, from `high_identity_T`, `high_particles_T`, `high_background_T`. -/
theorem high_bound_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ 0 < C ∧ ∀ p : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ ρ : Torus d → ℝ, BddDensityT ρ → ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N →
      ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
        |CcommT (gloForceT s η) (PgtT η v) (chargeT X ρ)| ≤ C * K * scaleQT s Cp p η X ρ := by
  obtain ⟨e₁, C₁, he₁, he₁1, hC₁, H₁⟩ := high_particles_T hd hs0 hsd
  obtain ⟨e₂, C₂, he₂, he₂1, hC₂, H₂⟩ := high_background_T hd hs0 hsd
  refine ⟨min e₁ e₂, 2 * C₁ + 2 * C₂, lt_min he₁ he₂, le_trans (min_le_left _ _) he₁1, by positivity,
    fun p hp => ?_⟩
  obtain ⟨c₁, hc₁, G₁⟩ := H₁ p hp
  obtain ⟨c₂, hc₂, G₂⟩ := H₂ p hp
  refine ⟨max c₁ c₂, lt_max_of_lt_left hc₁, fun Cp hCp η hη hηe ρ hρ N X hN hX v K hv => ?_⟩
  have hη1 : η ≤ 1 := le_trans hηe (le_trans (min_le_left _ _) he₁1)
  obtain ⟨L, hL0, hLip⟩ : ∃ L : ℝ, 0 ≤ L ∧ IsLipschitzVF L v := by
    obtain ⟨L, F, hL, -, hLip, -, -⟩ := hv
    exact ⟨L, hL, hLip⟩
  have e1 := G₁ Cp (le_trans (le_max_left _ _) hCp) η hη (le_trans hηe (min_le_left _ _)) ρ hρ N X hN hX v K hv
  have e2 := G₂ Cp (le_trans (le_max_right _ _) hCp) η hη (le_trans hηe (min_le_right _ _)) ρ hρ N X hN hX v K hv
  rw [high_identity_T hd hs0 hsd η hη hη1 ρ hρ hN X hX v L hL0 hLip]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set A := ∑ i, inner ℝ (PgtT η v (X i)) ((chargeT X ρ).convForce (gloForceT s η) (X i)) with hA
  set B := ∫ x, ρ x * inner ℝ (PgtT η v x) ((chargeT X ρ).convForce (gloForceT s η) x) with hB
  have hA' : |A| ≤ ∑ i, |inner ℝ (PgtT η v (X i)) ((chargeT X ρ).convForce (gloForceT s η) (X i))| :=
    Finset.abs_sum_le_sum_abs _ _
  have h1 : |(2 / (N : ℝ)) * A| ≤ 2 * (C₁ * K * scaleQT s Cp p η X ρ) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / N)]
    calc 2 / (N : ℝ) * |A|
        ≤ 2 / (N : ℝ) * ∑ i, |inner ℝ (PgtT η v (X i))
            ((chargeT X ρ).convForce (gloForceT s η) (X i))| :=
          mul_le_mul_of_nonneg_left hA' (by positivity)
      _ = 2 * ((1 / (N : ℝ)) * ∑ i, |inner ℝ (PgtT η v (X i))
            ((chargeT X ρ).convForce (gloForceT s η) (X i))|) := by ring
      _ ≤ 2 * (C₁ * K * scaleQT s Cp p η X ρ) := by gcongr
  have h2 : |2 * B| ≤ 2 * (C₂ * K * scaleQT s Cp p η X ρ) := by
    rw [abs_mul, abs_two]
    linarith
  calc |(2 / (N : ℝ)) * A - 2 * B|
      ≤ |(2 / (N : ℝ)) * A| + |2 * B| := abs_sub _ _
    _ ≤ 2 * (C₁ * K * scaleQT s Cp p η X ρ) + 2 * (C₂ * K * scaleQT s Cp p η X ρ) := add_le_add h1 h2
    _ = (2 * C₁ + 2 * C₂) * K * scaleQT s Cp p η X ρ := by ring

/-- The unit-scale estimate `(5.unitestimate)` on the torus, original variables: for `η ≤ η₀`,
`|𝖠₁[X,μ,v]| ≤ C·C(v)·Q_η` (`C_p` large).  Proved from the three bounds and the decomposition. -/
theorem unit_estimate_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ 0 < C ∧ ∀ p : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ ρ : Torus d → ℝ, BddDensityT ρ → ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N →
      ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
        |commAT s X ρ v| ≤ C * K * scaleQT s Cp p η X ρ := by
  obtain ⟨e₁, C₁, he₁, he₁1, hC₁, H₁⟩ := remainder_bound_T hd hs0 hsd
  obtain ⟨e₂, C₂, he₂, he₂1, hC₂, H₂⟩ := low_bound_T hd hs0 hsd
  obtain ⟨e₃, C₃, he₃, he₃1, hC₃, H₃⟩ := high_bound_T hd hs0 hsd
  refine ⟨min (min e₁ e₂) e₃, C₁ + C₂ + C₃, lt_min (lt_min he₁ he₂) he₃,
    le_trans (min_le_right _ _) he₃1, by positivity, fun p hp => ?_⟩
  obtain ⟨c₁, hc₁, G₁⟩ := H₁ p hp
  obtain ⟨c₂, hc₂, G₂⟩ := H₂ p hp
  obtain ⟨c₃, hc₃, G₃⟩ := H₃ p hp
  refine ⟨max (max c₁ c₂) c₃, lt_max_of_lt_left (lt_max_of_lt_left hc₁),
    fun Cp hCp η hη hηe ρ hρ N X hN hX v K hv => ?_⟩
  have hηa : η ≤ e₁ := le_trans hηe (le_trans (min_le_left _ _) (min_le_left _ _))
  have hηb : η ≤ e₂ := le_trans hηe (le_trans (min_le_left _ _) (min_le_right _ _))
  have hηc : η ≤ e₃ := le_trans hηe (min_le_right _ _)
  have hη1 : η ≤ 1 := le_trans hηc he₃1
  obtain ⟨L, hL0, hLip⟩ : ∃ L : ℝ, 0 ≤ L ∧ IsLipschitzVF L v := by
    obtain ⟨L, F, hL, -, hLip, -, -⟩ := hv
    exact ⟨L, hL, hLip⟩
  have x1 := G₁ Cp (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCp) η hη hηa ρ hρ N X hN hX v K hv
  have x2 := G₂ Cp (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCp) η hη hηb ρ hρ N X hN hX v K hv
  have x3 := G₃ Cp (le_trans (le_max_right _ _) hCp) η hη hηc ρ hρ N X hN hX v K hv
  rw [commAT_eq_CcommT hd hs0 hsd ρ hρ hN X hX v L hL0 hLip,
    CcommT_decomp hd hs0 hsd η hη hη1 ρ hρ hN X hX v L hL0 hLip]
  calc |CcommT (ghiForceT s η) v (chargeT X ρ) + CcommT (gloForceT s η) (PleqT η v) (chargeT X ρ) +
          CcommT (gloForceT s η) (PgtT η v) (chargeT X ρ)|
      ≤ |CcommT (ghiForceT s η) v (chargeT X ρ) + CcommT (gloForceT s η) (PleqT η v) (chargeT X ρ)| +
          |CcommT (gloForceT s η) (PgtT η v) (chargeT X ρ)| := abs_add_le _ _
    _ ≤ |CcommT (ghiForceT s η) v (chargeT X ρ)| + |CcommT (gloForceT s η) (PleqT η v) (chargeT X ρ)| +
          |CcommT (gloForceT s η) (PgtT η v) (chargeT X ρ)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ C₁ * K * scaleQT s Cp p η X ρ + C₂ * K * scaleQT s Cp p η X ρ + C₃ * K * scaleQT s Cp p η X ρ := by
        gcongr
    _ = (C₁ + C₂ + C₃) * K * scaleQT s Cp p η X ρ := by ring

/-- The exponent `d(1-1/p) - s` is positive for `p > d/(d-s)`. -/
theorem exp_pos_T (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (p : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) :
    0 ≤ (d : ℝ) * (1 - (p⁻¹).toReal) - s := by
  have hds : (0 : ℝ) < d - s := by linarith
  have hd : (0 : ℝ) < d := by linarith
  by_cases hpt : p = ⊤
  · subst hpt
    simp only [ENNReal.inv_top, ENNReal.toReal_zero, sub_zero, mul_one]
    linarith
  · have h := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hpt).1 hp
    have hq : 0 < p.toReal := lt_of_le_of_lt (by positivity) h
    rw [ENNReal.toReal_inv]
    rw [div_lt_iff₀ hds] at h
    have h2 : (d : ℝ) / p.toReal < d - s := by
      rw [div_lt_iff₀ hq]; linarith
    have e : (d : ℝ) * (1 - p.toReal⁻¹) - s = (d - s) - d / p.toReal := by
      rw [div_eq_mul_inv]; ring
    linarith

/-- Monotonicity in the scale (the range extension from `η ≤ η₂` to `η ≤ 1`, explicit algebra): for
`η₂ ≤ η ≤ 1` and `C_p ≥ C_p' + |log η₂|/2 + C_p' η₂^{-s}`, `Q_{η₂}(C_p') ≤ Q_η(C_p)`. -/
theorem scaleQT_mono (hs0 : 0 ≤ s) (p : ℝ≥0∞) (hexp : 0 ≤ (d : ℝ) * (1 - (p⁻¹).toReal) - s)
    {N : ℕ} (hN : 1 ≤ N) (X : Config d N) (ρ : Torus d → ℝ) {Cp' Cp η₂ η : ℝ} (hCp' : 0 ≤ Cp')
    (hη₂ : 0 < η₂) (h21 : η₂ ≤ η) (hη1 : η ≤ 1)
    (hCp : Cp' + |Real.log η₂| / 2 + Cp' * η₂ ^ (-s) ≤ Cp) :
    scaleQT s Cp' p η₂ X ρ ≤ scaleQT s Cp p η X ρ := by
  have hη : 0 < η := lt_of_lt_of_le hη₂ h21
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hM : 0 ≤ normT p ρ := ENNReal.toReal_nonneg
  have h1 : η₂ ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) ≤ η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) :=
    Real.rpow_le_rpow hη₂.le h21 hexp
  have h2 : 1 ≤ η ^ (-s) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hη hη1 (by linarith)
  have hlog : Real.log η ≤ 0 := Real.log_nonpos hη.le hη1
  have hlog2 : (if s = 0 then Real.log η / (2 * (N : ℝ)) else 0) -
      (if s = 0 then Real.log η₂ / (2 * (N : ℝ)) else 0) ≤ (|Real.log η₂| / 2) / N := by
    split_ifs
    · have : Real.log η₂ ≥ -|Real.log η₂| := neg_abs_le _
      have h3 : Real.log η / (2 * (N : ℝ)) - Real.log η₂ / (2 * (N : ℝ)) ≤ (|Real.log η₂| / 2) / N := by
        rw [← sub_div]
        rw [div_le_div_iff₀ (by positivity) hNpos]
        nlinarith
      exact h3
    · simp only [sub_zero]
      positivity
  unfold scaleQT
  have hMη : 0 ≤ normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := by positivity
  have hMη2 : normT p ρ * η₂ ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) ≤
      normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := mul_le_mul_of_nonneg_left h1 hM
  have hCpCp' : Cp' ≤ Cp := by
    have : 0 ≤ |Real.log η₂| / 2 + Cp' * η₂ ^ (-s) := by positivity
    linarith
  have h4 : Cp' * (η₂ ^ (-s) / (N : ℝ)) + (|Real.log η₂| / 2) / N ≤ Cp / N := by
    rw [← mul_div_assoc, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hNpos.le
  have h5 : Cp / N ≤ Cp * (η ^ (-s) / (N : ℝ)) := by
    have : 0 ≤ Cp := le_trans hCp' hCpCp'
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by nlinarith) hNpos.le
  have h6 : Cp' * (normT p ρ * η₂ ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s)) ≤
      Cp * (normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s)) :=
    mul_le_mul hCpCp' hMη2 (by positivity) (le_trans hCp' hCpCp')
  nlinarith [h4, h5, h6, hlog2]

/-- Proposition 1.2 for bounded densities, all `η ∈ (0,1]` (from `unit_estimate_T`, `energy_control_T (a)` and
`scaleQT_mono`). -/
theorem scale_estimate_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ≥0∞, ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp : ℝ, 0 < Cp ∧ ∀ ρ : Torus d → ℝ, BddDensityT ρ →
      ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N →
      ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        0 ≤ scaleQT s Cp p η X ρ ∧ |commAT s X ρ v| ≤ C * K * scaleQT s Cp p η X ρ := by
  obtain ⟨η₀, C, hη₀, hη₀1, hC, U⟩ := unit_estimate_T hd hs0 hsd
  obtain ⟨Cb, η₁, hCb, hη₁, hη₁1, E⟩ := energy_control_T hd hs0 hsd
  refine ⟨C, hC, fun p hp => ?_⟩
  obtain ⟨c₀, hc₀, Uc⟩ := U p hp
  obtain ⟨c₁, hc₁, Ec⟩ := E p hp
  have hexp := exp_pos_T hs0 (by linarith : s < (d : ℝ)) p hp
  set η₂ := min η₀ η₁ with hη₂
  have hη₂0 : 0 < η₂ := lt_min hη₀ hη₁
  have hη₂1 : η₂ ≤ 1 := le_trans (min_le_left _ _) hη₀1
  set c := max c₀ c₁ with hc
  have hcpos : 0 < c := lt_max_of_lt_left hc₀
  refine ⟨c + |Real.log η₂| / 2 + c * η₂ ^ (-s), by positivity, ?_⟩
  intro ρ hρ N X hN hX v K hv η hη hη1
  have hK : 0 ≤ K := by
    obtain ⟨L, F, hL, hF, -, -, hLK⟩ := hv
    linarith
  have hcc : c ≤ c + |Real.log η₂| / 2 + c * η₂ ^ (-s) := by
    have : 0 ≤ |Real.log η₂| / 2 + c * η₂ ^ (-s) := by positivity
    linarith
  -- the base case at scale η₂
  have hnn : 0 ≤ scaleQT s c p η₂ X ρ := by
    have := (Ec c (le_max_right _ _) η₂ hη₂0 (min_le_right _ _) ρ hρ N X hN hX).1
    have h0 : 0 ≤ η₂ ^ (-s) / (N : ℝ) + normT p ρ * η₂ ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have hM : 0 ≤ normT p ρ := ENNReal.toReal_nonneg
      positivity
    linarith
  have hbd := Uc c (le_max_left _ _) η₂ hη₂0 (min_le_left _ _) ρ hρ N X hN hX v K hv
  by_cases hle : η ≤ η₂
  · have hnn' := (Ec _ (le_trans (le_max_right _ _) hcc) η hη (le_trans hle (min_le_right _ _)) ρ hρ N X hN hX).1
    have h0 : 0 ≤ η ^ (-s) / (N : ℝ) + normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have hM : 0 ≤ normT p ρ := ENNReal.toReal_nonneg
      positivity
    refine ⟨by linarith, ?_⟩
    exact Uc _ (le_trans (le_max_left _ _) hcc) η hη (le_trans hle (min_le_left _ _)) ρ hρ N X hN hX v K hv
  · have hle := not_le.1 hle
    have hmono := scaleQT_mono hs0 p hexp hN X ρ (Cp' := c) (Cp := c + |Real.log η₂| / 2 + c * η₂ ^ (-s))
      hcpos.le hη₂0 hle.le hη1 (le_refl _)
    refine ⟨le_trans hnn hmono, ?_⟩
    calc |commAT s X ρ v| ≤ C * K * scaleQT s c p η₂ X ρ := hbd
      _ ≤ C * K * scaleQT s (c + |Real.log η₂| / 2 + c * η₂ ^ (-s)) p η X ρ := by
          have : 0 ≤ C * K := by positivity
          exact mul_le_mul_of_nonneg_left hmono this

/-- Absolute convergence for `ρ ∈ L¹ ∩ L^p`, `p > d/(d-s)` (Hölder; the kernels have the integrable singularities
`|x|^{-s}`, `|x|^{-s}`, `log`; `[N] L782-799`; no log hypothesis needed on the compact torus). -/
theorem integrable_of_Lp_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (ρ : Torus d → ℝ) (h1 : Integrable ρ)
    (hpρ : MemLp ρ p volume) (v : Torus d → Euc d) (L : ℝ) (hL : 0 ≤ L) (hv : IsLipschitzVF L v)
    {N : ℕ} (X : Config d N) (hX : X ∉ collisionSet d N) :
    EnergyIntegrableT s X ρ ∧ CommIntegrableT s X ρ v := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hds : (0 : ℝ) < d - s := by linarith
  have hsd' : s < (d : ℝ) := by linarith
  -- a real exponent `r > d/(d-s)` with `ρ ∈ L^r`
  obtain ⟨r, hr, hρr⟩ : ∃ r : ℝ, (d : ℝ) / (d - s) < r ∧ MemLp ρ (ENNReal.ofReal r) volume := by
    by_cases hpt : p = ⊤
    · refine ⟨2 * d / (d - s), ?_, ?_⟩
      · rw [div_lt_div_iff_of_pos_right hds]; linarith
      · subst hpt
        exact hpρ.mono_exponent le_top
    · refine ⟨p.toReal, ?_, ?_⟩
      · exact (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hpt).1 hp
      · rw [ENNReal.ofReal_toReal hpt]; exact hpρ
  have hge1 : (1 : ℝ) ≤ (d : ℝ) / (d - s) := by
    rw [le_div_iff₀ hds]; linarith
  have hr1 : 1 < r := lt_of_le_of_lt hge1 hr
  haveI hH : (ENNReal.ofReal r).HolderConjugate (ENNReal.ofReal r.conjExponent) :=
    (Real.HolderConjugate.conjExponent hr1).ennrealOfReal
  set q : ℝ := r.conjExponent with hqdef
  have hq : 0 < q := (Real.HolderConjugate.conjExponent hr1).symm.pos
  -- exponent of the dominating function
  have hrd : d * (r - 1) > s * r := by
    rw [div_lt_iff₀ hds] at hr
    nlinarith [hr]
  have hsq : s * q < d := by
    rw [hqdef, Real.conjExponent, mul_div_assoc', div_lt_iff₀ (by linarith : (0 : ℝ) < r - 1)]
    linarith
  set a : ℝ := tbrA s ((d : ℝ) / (2 * q)) with hadef
  have hε : 0 < (d : ℝ) / (2 * q) := div_pos hd0 (by linarith)
  have ha : 0 ≤ a := by
    unfold tbrA at hadef; rw [hadef]
    split_ifs
    · exact hε.le
    · exact hs0
  have hsa : s = 0 ∨ a = s := by
    by_cases h0 : s = 0
    · exact Or.inl h0
    · exact Or.inr (by rw [hadef]; unfold tbrA; rw [if_neg h0])
  have hs0a : s = 0 → 0 < a := fun h0 => by
    rw [hadef]; unfold tbrA; rw [if_pos h0]; exact hε
  have haq : a * q < d := by
    by_cases h0 : s = 0
    · have : a = (d : ℝ) / (2 * q) := by rw [hadef]; unfold tbrA; rw [if_pos h0]
      rw [this]
      have : (d : ℝ) / (2 * q) * q = d / 2 := by field_simp
      linarith
    · have : a = s := by rw [hadef]; unfold tbrA; rw [if_neg h0]
      rw [this]; exact hsq
  have hG : MemLp (tbrG (d := d) a) (ENNReal.ofReal q) volume :=
    tbr_memLp_G hd1 ha hq haq
  have hGm : Measurable (tbrG (d := d) a) := tbr_G_measurable a
  -- energy kernel
  obtain ⟨C₁, hC₁, hE⟩ := tbr_periodicRiesz_le hd hs0 hsd' ha hsa hs0a
  have hEm : Measurable (fun z : Torus d × Torus d => periodicRiesz d s (z.1 - z.2)) :=
    (CoercAux.measurable_periodicRiesz_one hd1 hs0 hsd').comp (measurable_fst.sub measurable_snd)
  have hk1 : ∀ x y : Torus d, x ≠ y →
      |(fun x y : Torus d => periodicRiesz d s (x - y)) x y| ≤ C₁ * |tbrG (d := d) a (x - y)| := by
    intro x y hxy
    have h := hE (x - y) (sub_ne_zero.2 hxy)
    rw [abs_of_nonneg (le_trans zero_le_one (tbr_G_one_le (d := d) a (x - y)))]
    exact h
  have hEI : EnergyIntegrableT s X ρ :=
    tbr_pairIntegrable (k := fun x y : Torus d => periodicRiesz d s (x - y)) hd1 hGm hG hρr h1 hEm
      hC₁ hk1 X
  -- commutator kernel
  obtain ⟨C₂, hC₂, hC⟩ := tbr_commKernel_le hd hs0 hsd' hsa hL hv
  have hvc : Continuous v := IsLipschitzVF.continuous hL hv
  have hCm : Measurable (fun z : Torus d × Torus d => commKernel (periodicRieszGrad d s) v z.1 z.2) := by
    unfold commKernel
    refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
    refine Measurable.inner ?_ ?_
    · exact (hvc.measurable.comp measurable_fst).sub (hvc.measurable.comp measurable_snd)
    · exact (KernelGrad.measurable_periodicRieszGrad hsd').comp (measurable_fst.sub measurable_snd)
  have hk2 : ∀ x y : Torus d, x ≠ y →
      |commKernel (periodicRieszGrad d s) v x y| ≤ C₂ * |tbrG (d := d) a (x - y)| := by
    intro x y hxy
    have h := hC x y hxy
    rw [abs_of_nonneg (le_trans zero_le_one (tbr_G_one_le (d := d) a (x - y)))]
    exact h
  have hCI : CommIntegrableT s X ρ v :=
    tbr_pairIntegrable (k := commKernel (periodicRieszGrad d s) v) hd1 hGm hG hρr h1 hCm
      hC₂ hk2 X
  exact ⟨hEI, hCI⟩

/-- The approximation `(5.density-approximation)` on the torus: `ρ_m = ρ1_{|ρ|≤m}/c_m` bounded of mass one,
`‖ρ_m‖_p → ‖ρ‖_p`, `F_N`, `𝖠₁` converge (dominated convergence, `|ρ_m| ≤ 2|ρ|`). -/
theorem density_approx_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (ρ : Torus d → ℝ) (h1 : Integrable ρ)
    (hpρ : MemLp ρ p volume) (hmass : ∫ x, ρ x = 1) :
    ∃ ρm : ℕ → Torus d → ℝ, (∀ m, BddDensityT (ρm m)) ∧
      Tendsto (fun m => normT p (ρm m)) atTop (𝓝 (normT p ρ)) ∧
      ∀ (N : ℕ) (X : Config d N), X ∉ collisionSet d N → ∀ (v : Torus d → Euc d) (L : ℝ), 0 ≤ L →
        IsLipschitzVF L v →
        Tendsto (fun m => modEnergyT s X (ρm m)) atTop (𝓝 (modEnergyT s X ρ)) ∧
        Tendsto (fun m => commAT s X (ρm m) v) atTop (𝓝 (commAT s X ρ v)) := by
  have hd1 : 1 ≤ d := by omega
  have hsd' : s < (d : ℝ) := by linarith
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact absurd hp (not_lt.2 zero_le)
  -- a measurable representative `σ` of `ρ`
  obtain ⟨σ, hσm, hσe⟩ : ∃ σ : Torus d → ℝ, Measurable σ ∧ σ =ᵐ[volume] ρ :=
    ⟨h1.aestronglyMeasurable.mk ρ, h1.aestronglyMeasurable.stronglyMeasurable_mk.measurable,
      h1.aestronglyMeasurable.ae_eq_mk.symm⟩
  have hσI : Integrable σ := h1.congr hσe.symm
  have hσp : MemLp σ p volume := hpρ.ae_eq hσe.symm
  have hσmass : ∫ x, σ x = 1 := by
    rw [integral_congr_ae hσe]
    exact hmass
  have hnI : Integrable (fun y => ‖σ y‖) := hσI.norm
  have hnp : MemLp (fun y => ‖σ y‖) p volume := hσp.norm
  have hbd := tbr_rho_bound_ev hσm hσI hσmass
  have hlim := tbr_rho_tendsto hσm hσI hσmass
  have hKm1 : Measurable (fun z : Torus d × Torus d => periodicRiesz d s (z.1 - z.2)) :=
    (CoercAux.measurable_periodicRiesz_one hd1 hs0 hsd').comp (measurable_fst.sub measurable_snd)
  refine ⟨tbrRho σ, fun m => ⟨tbr_rho_measurable hσm m, tbr_rho_bdd σ m, tbr_rho_mass σ m⟩, ?_, ?_⟩
  · have hnorm : normT p ρ = normT p σ := by
      unfold normT
      rw [eLpNorm_congr_ae hσe]
    rw [hnorm]
    by_cases hpt : p = ⊤
    · subst hpt
      exact tbr_normT_tendsto_top hσm hσI hσmass hσp
    · exact tbr_normT_tendsto_fin hp0 hpt hσp (fun m => tbr_rho_measurable hσm m)
        (fun m => tbr_rho_bdd σ m) hbd hlim
  · intro N X hX v L hL hv
    obtain ⟨hEI, hCI⟩ := integrable_of_Lp_T hd hs0 hsd p hp (fun y => ‖σ y‖) hnI hnp v L hL hv X hX
    have hCm : Measurable (fun z : Torus d × Torus d => commKernel (periodicRieszGrad d s) v z.1 z.2) :=
      tbr_commKernel_measurable hL hv hsd'
    have hmod := tbr_pairT_tendsto (K := fun x y : Torus d => periodicRiesz d s (x - y)) X hσm
      (fun m => tbr_rho_measurable hσm m) hKm1 hEI hbd hlim
    have hcom := tbr_pairT_tendsto (K := commKernel (periodicRieszGrad d s) v) X hσm
      (fun m => tbr_rho_measurable hσm m) hCm hCI hbd hlim
    have hρσ : ρ =ᵐ[volume] σ := hσe.symm
    constructor
    · have e : modEnergyT s X ρ = modEnergyT s X σ := by
        unfold modEnergyT
        rw [tbr_pairT_congr _ X hρσ]
      rw [e]
      exact hmod.const_mul (1 / 2)
    · have e : commAT s X ρ v = commAT s X σ v := by
        unfold commAT
        rw [tbr_pairT_congr _ X hρσ]
      rw [e]
      exact hcom

/-- **Proposition 1.2 on `𝕋^d`** (torus version of `[N] thm:scale`, repository kernel `periodicRiesz d s`):
`d ≥ 3`, `0 ≤ s < d-2`, `d/(d-s) < p ≤ ∞`, `μ ∈ L¹∩L^p` real of mass one, `v` Lipschitz with
`‖|∇|^{(d-s)/2}v‖_{L^{2d/(d-s-2)}(𝕋^d)} < ∞` (`C(v) ≤ K`), `X` pairwise distinct, `0 < η ≤ 1`:
`|𝖠₁| ≤ C C(v)(F_N - (log η)/(2N)1_{s=0} + C_p(η^{-s}/N + ‖μ‖_p η^{d(1-1/p)-s}))`, bracket `≥ 0`,
`C = C(d,s)`, `C_p = C_p(d,s,p)` (constants for the repository's kernel; for the note's kernel `g = s⁻¹|x|^{-s}` multiply
`F_N, 𝖠₁` by `s⁻¹`).  Proved from `scale_estimate_T`, `integrable_of_Lp_T`, `density_approx_T`. -/
theorem subcoulomb_commutator_scale_T (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ≥0∞, ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp : ℝ, 0 < Cp ∧ ∀ ρ : Torus d → ℝ, Integrable ρ → MemLp ρ p volume → ∫ x, ρ x = 1 →
      ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
      ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N → ∀ η : ℝ, 0 < η → η ≤ 1 →
        EnergyIntegrableT s X ρ ∧ CommIntegrableT s X ρ v ∧
        0 ≤ scaleQT s Cp p η X ρ ∧ |commAT s X ρ v| ≤ C * K * scaleQT s Cp p η X ρ := by
  obtain ⟨C, hC, S⟩ := scale_estimate_T hd hs0 hsd
  refine ⟨C, hC, fun p hp => ?_⟩
  obtain ⟨Cp, hCp, S'⟩ := S p hp
  refine ⟨Cp, hCp, fun ρ h1 hpρ hmass v K hv N X hN hX η hη hη1 => ?_⟩
  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧ IsLipschitzVF L v := by
    obtain ⟨L, F, hL, -, hLip, -, -⟩ := hv
    exact ⟨L, hL, hLip⟩
  obtain ⟨hE, hCI⟩ := integrable_of_Lp_T hd hs0 hsd p hp ρ h1 hpρ v L hL0 hL X hX
  obtain ⟨ρm, hbdd, hnorm, hlim⟩ := density_approx_T hd hs0 hsd p hp ρ h1 hpρ hmass
  obtain ⟨hF, hA⟩ := hlim N X hX v L hL0 hL
  have hm := fun m => S' (ρm m) (hbdd m) N X hN hX v K hv η hη hη1
  have hQ : Tendsto (fun m => scaleQT s Cp p η X (ρm m)) atTop (𝓝 (scaleQT s Cp p η X ρ)) := by
    unfold scaleQT
    exact (hF.sub tendsto_const_nhds).add
      (tendsto_const_nhds.mul (tendsto_const_nhds.add (hnorm.mul tendsto_const_nhds)))
  refine ⟨hE, hCI, ge_of_tendsto hQ (Eventually.of_forall fun m => (hm m).1), ?_⟩
  exact le_of_tendsto_of_tendsto hA.abs (tendsto_const_nhds.mul hQ)
    (Eventually.of_forall fun m => (hm m).2)

/-- `‖μ‖_{L^∞(𝕋^d)} ≥ 1` for a mass-one density (`1 = ∫μ ≤ ‖μ‖_∞ vol(𝕋^d)`), so `λ ≤ 1`. -/
theorem normT_top_ge_one (ρ : Torus d → ℝ) (h1 : Integrable ρ) (hinf : MemLp ρ ⊤ volume)
    (hmass : ∫ x, ρ x = 1) : 1 ≤ normT ⊤ ρ := by
  have hfin : eLpNorm ρ ⊤ volume < ⊤ := hinf.eLpNorm_lt_top
  have hae : ∀ᵐ x ∂(volume : Measure (Torus d)), ‖ρ x‖ₑ ≤ eLpNorm ρ ⊤ volume := by
    rw [eLpNorm_exponent_top h1.aestronglyMeasurable]
    exact ae_le_eLpNormEssSup
  have hbd : ∀ᵐ x ∂(volume : Measure (Torus d)), ‖ρ x‖ ≤ normT ⊤ ρ := by
    filter_upwards [hae] with x hx
    unfold normT
    rw [← toReal_enorm (ρ x)]
    exact ENNReal.toReal_mono hfin.ne hx
  have key := norm_integral_le_of_norm_le_const hbd
  rw [hmass, Real.norm_eq_abs, abs_one, measureReal_def, measure_univ, ENNReal.toReal_one,
    mul_one] at key
  exact key

/-- **Theorem 1.1 on `𝕋^d`** (torus version of `[N] thm:main`, repository kernel): `d ≥ 3`, `0 ≤ s < d-2`; there are `C, C₀ > 0`
depending only on `d, s` such that for every real `μ ∈ L¹ ∩ L^∞(𝕋^d)` of mass one, every `v` with
`C(v) ≤ K`, `λ = (N‖μ‖_∞)^{-1/d} (≤ 1)`, and every pairwise distinct `X_N` (`N ≥ 1`),
`|𝖠₁| ≤ C C(v)(F_N - (log λ)/(2N)1_{s=0} + C₀‖μ‖_∞λ^{d-s})`, bracket `≥ 0`, integrals absolutely convergent.
Deviations from the `ℝ^d` Theorem 1.1: repository kernel (`F^{repo} = tScale·F^{note}`, `C₀^{repo} = tScale·C₀^{note}`), no
log-integrability hypothesis, torus transport norm, `X ∉ collisionSet`.  Proved from Proposition 1.2 with `p = ∞`, `η = λ`. -/
theorem torus_subcoulomb_commutator (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C C₀ : ℝ, 0 < C ∧ 0 < C₀ ∧ ∀ ρ : Torus d → ℝ, Integrable ρ → MemLp ρ ⊤ volume →
      ∫ x, ρ x = 1 → ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
      ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N →
        EnergyIntegrableT s X ρ ∧ CommIntegrableT s X ρ v ∧
        0 ≤ modEnergyT s X ρ - (if s = 0 then Real.log (lamT d N ρ) / (2 * (N : ℝ)) else 0) +
              C₀ * normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s) ∧
        |commAT s X ρ v| ≤ C * K *
          (modEnergyT s X ρ - (if s = 0 then Real.log (lamT d N ρ) / (2 * (N : ℝ)) else 0) +
            C₀ * normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s)) := by
  obtain ⟨C, hC, S⟩ := subcoulomb_commutator_scale_T hd hs0 hsd
  obtain ⟨Cp, hCp, S'⟩ := S ⊤ (by simp)
  refine ⟨C, 2 * Cp, hC, by positivity, fun ρ h1 hinf hmass v K hv N X hN hX => ?_⟩
  have hM1 := normT_top_ge_one ρ h1 hinf hmass
  have hM : 0 < normT ⊤ ρ := lt_of_lt_of_le one_pos hM1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hNM : 0 < (N : ℝ) * normT ⊤ ρ := mul_pos hNpos hM
  have hlam : 0 < lamT d N ρ := Real.rpow_pos_of_pos hNM _
  have hNM1 : 1 ≤ (N : ℝ) * normT ⊤ ρ := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hlam1 : lamT d N ρ ≤ 1 := by
    unfold lamT
    exact Real.rpow_le_one_of_one_le_of_nonpos hNM1 (by
      have : (0 : ℝ) < d := by
        have : (3 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      have : (0 : ℝ) ≤ 1 / d := by positivity
      rw [neg_div]; linarith)
  have hlamd : lamT d N ρ ^ (d : ℝ) = ((N : ℝ) * normT ⊤ ρ)⁻¹ := by
    unfold lamT
    rw [← Real.rpow_mul hNM.le, show (-(1 : ℝ) / d) * d = -1 by field_simp, Real.rpow_neg_one]
  have hkey : lamT d N ρ ^ (-s) / (N : ℝ) = normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s) := by
    rw [sub_eq_add_neg, Real.rpow_add hlam, hlamd]
    field_simp
  obtain ⟨hE, hCI, hQ, hA⟩ := S' ρ h1 hinf hmass v K hv N X hN hX (lamT d N ρ) hlam hlam1
  have hQe : scaleQT s Cp ⊤ (lamT d N ρ) X ρ =
      modEnergyT s X ρ - (if s = 0 then Real.log (lamT d N ρ) / (2 * (N : ℝ)) else 0) +
        2 * Cp * normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s) := by
    unfold scaleQT
    simp only [ENNReal.inv_top, ENNReal.toReal_zero, sub_zero, mul_one]
    rw [hkey]
    ring
  rw [hQe] at hQ hA
  exact ⟨hE, hCI, hQ, hA⟩

end HRS.Commutator.TorusNote
