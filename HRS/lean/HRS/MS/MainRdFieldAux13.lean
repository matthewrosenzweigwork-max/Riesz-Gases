import HRS.MS.MainRdFieldAux12

/-!
# S.A.6, packet P7b: the first-moment bound for one `N ≥ 2`

`sa6_core_moment`: `E‖Ξ‖ ≤ (1 + C_in²) + (1 + C_b (2dTK_k²)²) + (σ_N/2) K' T (𝔈_N + e_N)` (`N ≥ 2`, `t ≤ T`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem HRS.MH.DualityRd

variable {d : ℕ}

section CoreMoment

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}
  {Γ : ℕ} {e : ℕ → ℝ} {Kad K' Cin : ℝ} {εf : ℕ → ℝ}
  {Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (Γ : ℝ)}

theorem sa6_core_moment
    (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 3) (Γ + 3) C₀ 𝔈) (hΛ : 1 ≤ Λ)
    (hadj : AdjointDerivInput (Γ : ℝ) (mStar d) S.coeff S.T Kad) (he : ∀ N, 0 ≤ e N)
    (hsel : SelectedCommutatorInput S (Γ : ℝ) S.T K' C₀ Λ e)
    (hinit : TransportedInitialFieldRd S R Γ Cin εf Iemp I)
    {N : ℕ} (hN : 2 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T)
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ ρ ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal ρ) ζ))
    {Kk : ℝ} {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ)}
    (hK : Sa6Kern (S.coeff N) S.T Γ Kk Kern)
    {Ξ : (R N).Ω → HNeg d (Γ : ℝ)} (hΞm : Measurable Ξ) (hΞ : IsFluctFieldRepr S R N Γ t Ξ) :
    ∫⁻ ζ, ‖Ξ ζ‖ₑ ∂(R N).P ≤ ENNReal.ofReal ((1 + Cin ^ 2) +
      (1 + mrmCb * (2 * d * S.T * Kk ^ 2) ^ 2) + S.sigma N / 2 * max K' 0 * S.T * (𝔈 N + e N)) := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hT : 0 ≤ S.T := S.hT.le
  have htT : t ≤ S.T := ht.2
  have hσ := mrr_sigma_nonneg S N
  obtain ⟨ℱ, W', M, I', Rr, hF, hMad, hM, hIto, hI'meas0, hI'meas, hMt, hRm, hΞeq, hae, hpath⟩ :=
    sa6_decomp hS hΛ hadj he hsel hinit hN ht hinj hK hΞm hΞ
  have hc0 : 0 ≤ S.sigma N / 2 * max K' 0 := mul_nonneg (by positivity) (le_max_right _ _)
  have hL1 := sa6_remainder_L1 hS he hN1 hc0 Rr hpath hF
  have hK0 := hK.nonneg
  -- the martingale
  have hA : t * ((Fintype.card (Fin N × Fin d) : ℕ) : ℝ) * (|sa6_cN S N| * Kk) ^ 2 ≤
      2 * d * S.T * Kk ^ 2 := by
    have hc := sa6_cN_sq S hN0
    have hq1 := sa6_q_le_one S hN0
    have hq0 := sa6_qN_nonneg S N
    simp only [Fintype.card_prod, Fintype.card_fin]
    push_cast
    have e1 : t * ((N : ℝ) * d) * (|sa6_cN S N| * Kk) ^ 2 =
        t * d * (sa6_cN S N ^ 2 * N) * Kk ^ 2 := by rw [mul_pow, sq_abs]; ring
    rw [e1, hc]
    have h1 : t * (2 * S.qN N) ≤ S.T * 2 := mul_le_mul htT (by linarith) (by linarith) hT
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc t * d * (2 * S.qN N) * Kk ^ 2 = (t * (2 * S.qN N)) * (d * Kk ^ 2) := by ring
      _ ≤ (S.T * 2) * (d * Kk ^ 2) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring
  have hML := sa6_M_L1 (ℱ := ℱ) ht.1 (hM t) (B := |sa6_cN S N| * Kk) (A := 2 * d * S.T * Kk ^ 2)
    (mul_nonneg (abs_nonneg _) hK0)
    (fun r ω k => sa6_Z_norm hK (sa6_cN S N) htT (fun _ => S.T) (R N).X r ω k) hA
  -- the initial term
  have hIL : ∫⁻ ζ, ‖I' ζ‖ₑ ∂(R N).P ≤ ENNReal.ofReal (1 + Cin ^ 2) := by
    calc ∫⁻ ζ, ‖I' ζ‖ₑ ∂(R N).P = ∫⁻ ζ, ‖Iemp N t ζ‖ₑ ∂(R N).P :=
          lintegral_congr_ae (hae.mono fun ζ h => by
            show ‖I' ζ‖ₑ = ‖Iemp N t ζ‖ₑ
            rw [h])
      _ ≤ ∫⁻ ζ, (1 + ‖Iemp N t ζ‖ₑ ^ 2) ∂(R N).P :=
          lintegral_mono fun ζ => sa6_enorm_le_one_add_sq _
      _ = 1 + ∫⁻ ζ, ‖Iemp N t ζ‖ₑ ^ 2 ∂(R N).P := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ 1 + ENNReal.ofReal (Cin ^ 2) :=
          add_le_add le_rfl (le_trans le_self_add (hinit.moment N hN1 t ht))
      _ = ENNReal.ofReal (1 + Cin ^ 2) := by
          rw [ENNReal.ofReal_add (by norm_num) (sq_nonneg _)]; simp
  have hΞ' : ∀ ζ, ‖Ξ ζ‖ₑ ≤ ‖I' ζ‖ₑ + ‖M t ζ‖ₑ + ‖Rr ζ‖ₑ := fun ζ => by
    rw [hΞeq ζ]
    exact (enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
  have hρ0 : 0 ≤ S.sigma N / 2 * max K' 0 * S.T * (𝔈 N + e N) :=
    mul_nonneg (mul_nonneg hc0 hT) (add_nonneg h𝔈 (he N))
  calc ∫⁻ ζ, ‖Ξ ζ‖ₑ ∂(R N).P ≤ ∫⁻ ζ, (‖I' ζ‖ₑ + ‖M t ζ‖ₑ + ‖Rr ζ‖ₑ) ∂(R N).P := lintegral_mono hΞ'
    _ = ∫⁻ ζ, ‖I' ζ‖ₑ ∂(R N).P + ∫⁻ ζ, ‖M t ζ‖ₑ ∂(R N).P + ∫⁻ ζ, ‖Rr ζ‖ₑ ∂(R N).P := by
        rw [lintegral_add_left (f := fun ζ => ‖I' ζ‖ₑ + ‖M t ζ‖ₑ) (hI'meas.enorm.add hMt.enorm),
          lintegral_add_left (f := fun ζ => ‖I' ζ‖ₑ) hI'meas.enorm]
    _ ≤ ENNReal.ofReal (1 + Cin ^ 2) + ENNReal.ofReal (1 + mrmCb * (2 * d * S.T * Kk ^ 2) ^ 2) +
          ENNReal.ofReal (S.sigma N / 2 * max K' 0 * S.T * (𝔈 N + e N)) :=
        add_le_add (add_le_add hIL hML) hL1
    _ = _ := by
        have ha : 0 ≤ 1 + Cin ^ 2 := by positivity
        have hb : 0 ≤ 1 + mrmCb * (2 * d * S.T * Kk ^ 2) ^ 2 :=
          add_nonneg zero_le_one (mul_nonneg mrmCb_nonneg (sq_nonneg _))
        rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_add (add_nonneg ha hb) hρ0]

end CoreMoment

end HRS.MS.MainRdField
