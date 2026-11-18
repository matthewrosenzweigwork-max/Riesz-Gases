import HRS.Commutator.Torus.Defs
import HRS.Commutator.Torus.Layer
import HRS.Commutator.Torus.External
import HRS.Commutator.Torus.Assembly

/-!
# The torus Theorem 1.1 implies the `s < d-2` branch of `HRS.commutator_estimate`

`HRS.Commutator.commutator_estimate_sub` (`HRS/Energy/Commutator/SubAssembly.lean`) is the branch used by
`commutator_estimate_of_packets` (`Assembly.lean`) for `0 ≤ s < d-2`; its proof there uses the packets H1, H3, H4, H5 (Route H,
now **replaced**).  `commutator_estimate_sub_of_torus` below has the same statement (checked by `rfl`) and is proved from
`torus_subcoulomb_commutator`, the torus embedding `embedding_T` (`F = ‖|∇|^{(d+1)/2}v‖_{L^{2d/(d-1)}} ⇒
‖|∇|^{(d-s)/2}v‖_{L^{2d/(d-s-2)}} ≲ F`) and three elementary lemmas (identification of the repository's `rieszEnergy`,
`commQuantity` for `μ = ρ dx` with `modEnergyT`, `commAT`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d N : ℕ} {s : ℝ}

/-- `∫ f d(ρ dx) = ∫ f ρ dx` for a probability density `ρ ≥ 0` (unconditional: Mathlib's
`integral_withDensity_eq_integral_toReal_smul` holds without integrability hypotheses). -/
theorem tbr_integral_withDensity (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (f : Torus d → ℝ) :
    ∫ x, f x ∂(withDensityReal ρ) = ∫ x, f x * ρ x := by
  unfold withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul hρ.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have h : ∀ x, (ENNReal.ofReal (ρ x)).toReal • f x = f x * ρ x := fun x => by
    rw [ENNReal.toReal_ofReal (hρ.nonneg x), smul_eq_mul, mul_comm]
  simp only [h]

/-- The iterated integral against `ρ(x) ρ(y)`, with the factor `ρ(x)` pulled out of the inner integral. -/
theorem tbr_double (ρ : Torus d → ℝ) (k : Torus d → Torus d → ℝ) :
    ∫ x, ∫ y, k x y * ρ x * ρ y = ∫ x, (∫ y, k x y * ρ y) * ρ x := by
  congr 1
  funext x
  rw [← integral_mul_const]
  congr 1
  funext y
  ring

/-- `rieszEnergy d s X (ρ dx) = modEnergyT s X ρ` for a probability density (`∫ f d(ρ dx) = ∫ ρ f dx`, `ρ ≥ 0`;
unconditional, Bochner integrals on both sides). -/
theorem rieszEnergy_eq_T (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) {N : ℕ} (X : Config d N) :
    rieszEnergy d s X (withDensityReal ρ) = modEnergyT s X ρ := by
  unfold rieszEnergy modulatedEnergyKernel modulatedEnergy modEnergyT pairT
  simp only [tbr_integral_withDensity ρ hρ, tbr_double ρ]
  ring

/-- `commQuantity d s v X (ρ dx) = commAT s X ρ v` (same). -/
theorem commQuantity_eq_T (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) {N : ℕ} (X : Config d N)
    (v : Torus d → Euc d) :
    commQuantity d s v X (withDensityReal ρ) = commAT s X ρ v := by
  unfold commQuantity commQuantityWith offDiagPairing commAT pairT
  simp only [tbr_integral_withDensity ρ hρ, tbr_double ρ]

/-- `‖ρ‖_{L^∞} ≤ Λ` for `0 ≤ ρ ≤ Λ`. -/
theorem normT_top_le (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) :
    normT ⊤ ρ ≤ Λ := by
  have h : eLpNorm ρ ⊤ volume ≤ ENNReal.ofReal Λ := by
    rw [eLpNorm_exponent_top hρ.measurable.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg x)]; exact hΛ x)
  have hΛ0 : 0 ≤ Λ := le_trans (hρ.nonneg 0) (hΛ 0)
  exact ENNReal.toReal_le_of_le_ofReal hΛ0 h

/-- **The torus Theorem 1.1 implies the `0 ≤ s < d-2` branch of `HRS.commutator_estimate`**
(statement identical to `HRS.Commutator.commutator_estimate_sub`, checked by `rfl` in `BridgeCheck.lean`).  Constants: `C₀ = C₀^{torus}`, `C = C^{torus}·max(1, C_emb)`. -/
theorem commutator_estimate_sub_of_torus (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) - 2) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ (L F : ℝ) (v : Torus d → Euc d), 0 ≤ L → 0 ≤ F → IsLipschitzVF L v → HasFracBound d v F →
        |commQuantity d s v X (withDensityReal ρ)| ≤
          C * (L + F) * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  obtain ⟨C, C₀, hC, hC₀, H⟩ := torus_subcoulomb_commutator hd hs0 hs
  obtain ⟨Ce, hCe, E⟩ := embedding_T hd hs0 hs
  refine ⟨C₀, C * max 1 Ce, hC₀.le, by positivity, ?_⟩
  intro Λ hΛ N hN ρ hρ hΛρ X hX L F v hL hF hLip hfrac
  have h1 : Integrable ρ := by
    by_contra h
    have := hρ.integral_one
    rw [integral_undef h] at this
    exact zero_ne_one this
  have hinf : MemLp ρ ⊤ volume :=
    memLp_top_of_bound h1.aestronglyMeasurable |Λ| (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg x)]
      exact le_trans (hΛρ x) (le_abs_self Λ))
  obtain ⟨w, hw, hwn⟩ := E v F hF hfrac
  have hv' : TorusSubTransport d s v (L + Ce * F) :=
    ⟨L, Ce * F, hL, by positivity, hLip, ⟨w, hw, hwn⟩, le_refl _⟩
  obtain ⟨-, -, hQ, hA⟩ := H ρ h1 hinf hρ.integral_one v _ hv' N X (by omega) hX
  rw [commQuantity_eq_T ρ hρ X v, rieszEnergy_eq_T ρ hρ X]
  have hM1 := normT_top_ge_one ρ h1 hinf hρ.integral_one
  have hM : 0 < normT ⊤ ρ := lt_of_lt_of_le one_pos hM1
  have hMΛ := normT_top_le ρ hρ Λ hΛρ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hNM : 0 < (N : ℝ) * normT ⊤ ρ := mul_pos hNpos hM
  have hlam : 0 < lamT d N ρ := Real.rpow_pos_of_pos hNM _
  have hlamd : lamT d N ρ ^ (d : ℝ) = ((N : ℝ) * normT ⊤ ρ)⁻¹ := by
    unfold lamT
    rw [← Real.rpow_mul hNM.le, show (-(1 : ℝ) / d) * d = -1 by field_simp, Real.rpow_neg_one]
  have hlams : lamT d N ρ ^ (-s) = ((N : ℝ) * normT ⊤ ρ) ^ (s / d) := by
    unfold lamT
    rw [← Real.rpow_mul hNM.le]
    congr 1
    field_simp
  have hMl : normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s) ≤ Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) := by
    rw [sub_eq_add_neg, Real.rpow_add hlam, hlamd, hlams, Real.mul_rpow hNpos.le hM.le]
    have e : normT ⊤ ρ * (((N : ℝ) * normT ⊤ ρ)⁻¹ * ((N : ℝ) ^ (s / d) * normT ⊤ ρ ^ (s / d))) =
        (N : ℝ) ^ (s / d - 1) * normT ⊤ ρ ^ (s / d) := by
      rw [Real.rpow_sub_one hNpos.ne']
      field_simp
    rw [e, mul_comm]
    gcongr
  have hlogterm : (if s = 0 then -(Real.log (lamT d N ρ) / (2 * (N : ℝ))) else 0) ≤
      (if s = 0 then Real.log ((N : ℝ) * Λ) / (2 * d * N) else 0) := by
    split_ifs with h0
    · have h2 : Real.log (lamT d N ρ) = (-(1 : ℝ) / d) * Real.log ((N : ℝ) * normT ⊤ ρ) := by
        unfold lamT; rw [Real.log_rpow hNM]
      rw [h2]
      have h3 : Real.log ((N : ℝ) * normT ⊤ ρ) ≤ Real.log ((N : ℝ) * Λ) :=
        Real.log_le_log hNM (mul_le_mul_of_nonneg_left hMΛ hNpos.le)
      have : -((-(1 : ℝ) / d * Real.log ((N : ℝ) * normT ⊤ ρ)) / (2 * (N : ℝ))) =
          Real.log ((N : ℝ) * normT ⊤ ρ) / (2 * d * N) := by field_simp
      rw [this]
      gcongr
    · exact le_rfl
  have hQle : modEnergyT s X ρ - (if s = 0 then Real.log (lamT d N ρ) / (2 * (N : ℝ)) else 0) +
        C₀ * normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s) ≤
      modEnergyT s X ρ + oNΛ d s C₀ Λ N := by
    unfold oNΛ
    have h5 : C₀ * normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s) ≤ C₀ * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) := by
      calc C₀ * normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s)
          = C₀ * (normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s)) := by ring
        _ ≤ C₀ * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) := by gcongr
        _ = _ := by ring
    have h7 : -(if s = 0 then Real.log (lamT d N ρ) / (2 * (N : ℝ)) else 0) ≤
        (if s = 0 then Real.log ((N : ℝ) * Λ) / (2 * d * N) else 0) := by
      split_ifs at hlogterm ⊢ with h0
      · simpa [neg_div] using hlogterm
      · simp
    linarith
  have hL1 : 0 ≤ L + Ce * F := by positivity
  calc |commAT s X ρ v| ≤ C * (L + Ce * F) *
        (modEnergyT s X ρ - (if s = 0 then Real.log (lamT d N ρ) / (2 * (N : ℝ)) else 0) +
          C₀ * normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s)) := hA
    _ ≤ C * (L + Ce * F) * (modEnergyT s X ρ + oNΛ d s C₀ Λ N) := by
        have : 0 ≤ C * (L + Ce * F) := by positivity
        exact mul_le_mul_of_nonneg_left hQle this
    _ ≤ C * max 1 Ce * (L + F) * (modEnergyT s X ρ + oNΛ d s C₀ Λ N) := by
        have hY : 0 ≤ modEnergyT s X ρ + oNΛ d s C₀ Λ N := le_trans hQ hQle
        have hineq : C * (L + Ce * F) ≤ C * max 1 Ce * (L + F) := by
          have : L + Ce * F ≤ max 1 Ce * (L + F) := by
            have h1' : 1 ≤ max 1 Ce := le_max_left _ _
            have h2' : Ce ≤ max 1 Ce := le_max_right _ _
            nlinarith [mul_nonneg hL (sub_nonneg.2 h1'), mul_nonneg hF (sub_nonneg.2 h2')]
          calc C * (L + Ce * F) ≤ C * (max 1 Ce * (L + F)) := mul_le_mul_of_nonneg_left this hC.le
            _ = _ := by ring
        exact mul_le_mul_of_nonneg_right hineq hY

end HRS.Commutator.TorusNote
