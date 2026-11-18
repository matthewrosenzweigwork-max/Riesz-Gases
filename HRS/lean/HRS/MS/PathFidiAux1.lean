import HRS.MP.RdRemainder
import HRS.MS.GoFeatAux2
import HRS.MS.FcauTie
import HRS.MS.UlNormAux1
import HRS.MS.GenPathAux13
import HRS.MH.DualityRdFinal
import HRS.Prob.HilbertMartingale
import HRS.Main.A8PAux1
import HRS.Main.A8PAux11
import HRS.MH.CommSuperCS10
import HRS.Commutator.Whole.Bridge
import HRS.MS.SuppU15Aux1
import HRS.MS.SuppU15Aux2
import HRS.MS.SuppU15Aux3
import HRS.MH.CoercTestTie

/-!
# SA26 packet P1: S.A.26 `path_fidi_rd`, scalar facts, Schwartz tests, regularity, bounds

Plan (docs/SA26 scratch plan `SA26_PLAN.md`; verdict: the frozen statement is TRUE and non-vacuous as far as checked).
Row S.A.26 `HRS.Whole.AppendixALemmas.path_fidi_rd` (TeX supplement L10884-10891), route (a): exact multi-time duality
identity (`duality_identity_rd_proof`), vector martingale (`several_times_covariation`), commutator remainder (S.B.5 via the
bridge `selectedCommutator` of `PathFidiAux3`), covariance replacement by the coercivity test bound (S.A.19 pathwise),
Lindeberg `a8p_smooth_abstract`, convergence of the covariances from the stability hypothesis, identification of the limit.
Packets: P1 (this file): scalars, Schwartz tests, regularity, bounds of the adjoint inputs; P2 decomposition and martingale;
P3 B5 and the remainder; P4 covariance replacement; P5 convergence of covariances and surrogate laws; P6 null contact (case (c));
P7 Lindeberg, identification, squeeze; `PathFidiTie` the tie `path_fidi_rd_proof`.
Namespace `HRS.MS.PathFidi`, helper names `sa26_`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.PathFidi

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-! ### Scalars -/

theorem sa26_sigma_eq (S : WholeMainData d) (N : ℕ) : S.sigma N = S.AN N * S.κ N := by
  have hκ := (S.hκ N).ne'
  unfold WholeMainData.sigma WholeMainData.AN Ascale
  by_cases h : S.invβ N = 0
  · simp [sigmaScale, h]
  · simp only [h, if_false]
    field_simp

theorem sa26_qN_eq (S : WholeMainData d) (N : ℕ) : S.qN N = S.sigma N ^ 2 * S.invβ N / N := by
  unfold WholeMainData.qN qScale WholeMainData.sigma
  by_cases h : S.invβ N = 0
  · simp [h]
  · simp [h]

theorem sa26_qN_nonneg (S : WholeMainData d) (N : ℕ) : 0 ≤ S.qN N := by
  rw [sa26_qN_eq]
  have := S.hinvβ N
  positivity

theorem sa26_AN_nonneg (S : WholeMainData d) (N : ℕ) : 0 ≤ S.AN N := by
  have hκ := S.hκ N
  rw [show S.AN N = S.sigma N / S.κ N by
    rw [sa26_sigma_eq]; field_simp]
  exact div_nonneg (HRS.MP.RdRem.mrr_sigma_nonneg S N) hκ.le

theorem sa26_wN_nonneg (d N : ℕ) {E m₂ : ℝ} (hE : 0 ≤ E) (hm : 0 ≤ m₂) : 0 ≤ wN d N E m₂ := by
  unfold wN
  refine Real.iInf_nonneg fun R => ?_
  have hR : 0 < R.1 := lt_of_lt_of_le one_pos R.2
  have h1 : 0 ≤ R.1 ^ ((d : ℝ) / 2) := Real.rpow_nonneg hR.le _
  have h2 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h3 : 0 ≤ E ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hE _
  positivity

/-- The smallness hypothesis splits into its three nonnegative pieces. -/
theorem sa26_small_split (S : WholeMainData d) (efn 𝔈 εf : ℕ → ℝ) (m₂ : ℝ) (hm₂ : 0 ≤ m₂)
    (he : ∀ N, 0 ≤ efn N) (h𝔈 : ∀ N : ℕ, 1 ≤ N → 0 < 𝔈 N) (hεf : ∀ N : ℕ, 1 ≤ N → 0 ≤ εf N)
    (h : Tendsto (fun N => εf N + S.sigma N * (𝔈 N + efn N) + S.qN N * wN d N (𝔈 N) m₂) atTop (𝓝 0)) :
    Tendsto (fun N => S.sigma N * (𝔈 N + efn N)) atTop (𝓝 0) ∧
      Tendsto (fun N => S.qN N * wN d N (𝔈 N) m₂) atTop (𝓝 0) := by
  have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop 1
  refine ⟨?_, ?_⟩
  · refine squeeze_zero' ?_ ?_ h
    · filter_upwards [hev] with N hN
      exact mul_nonneg (HRS.MP.RdRem.mrr_sigma_nonneg S N) (add_nonneg (h𝔈 N hN).le (he N))
    · filter_upwards [hev] with N hN
      have h1 := hεf N hN
      have h2 : 0 ≤ S.qN N * wN d N (𝔈 N) m₂ :=
        mul_nonneg (sa26_qN_nonneg S N) (sa26_wN_nonneg d N (h𝔈 N hN).le hm₂)
      linarith
  · refine squeeze_zero' ?_ ?_ h
    · filter_upwards [hev] with N hN
      exact mul_nonneg (sa26_qN_nonneg S N) (sa26_wN_nonneg d N (h𝔈 N hN).le hm₂)
    · filter_upwards [hev] with N hN
      have h1 := hεf N hN
      have h2 : 0 ≤ S.sigma N * (𝔈 N + efn N) :=
        mul_nonneg (HRS.MP.RdRem.mrr_sigma_nonneg S N) (add_nonneg (h𝔈 N hN).le (he N))
      linarith

/-! ### The completion constant comparison -/

theorem sa26_oN_comp (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (Λ Cc : ℝ) :
    ∃ C₁ : ℝ, 0 < Λ → ∀ C₀ : ℝ, C₁ ≤ C₀ → ∀ N : ℕ, 1 ≤ N →
      oNΛ d s Cc (max Λ 1) N ≤ oNΛ d s C₀ Λ N := by
  refine ⟨(Cc * (max Λ 1) ^ (s / d) + (if s = 0 then (Real.log (max Λ 1) - Real.log Λ) / (2 * d) else 0)) /
    Λ ^ (s / d), fun hΛ C₀ hC N hN => ?_⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 < Λ ^ (s / d) := Real.rpow_pos_of_pos hΛ _
  have hb : 0 < (N : ℝ) ^ (s / d - 1) := Real.rpow_pos_of_pos hNpos _
  have hC : (Cc * (max Λ 1) ^ (s / d) + (if s = 0 then (Real.log (max Λ 1) - Real.log Λ) / (2 * d) else 0)) ≤
      C₀ * Λ ^ (s / d) := by
    rwa [div_le_iff₀ ha] at hC
  have hΛ1 : 0 < max Λ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  unfold oNΛ
  by_cases h0 : s = 0
  · subst h0
    simp only [if_true, zero_div, Real.rpow_zero, mul_one] at hC ⊢
    rw [Real.log_mul hNpos.ne' hΛ1.ne', Real.log_mul hNpos.ne' hΛ.ne']
    have e : (N : ℝ) ^ ((0 : ℝ) - 1) = (N : ℝ)⁻¹ := by simp [Real.rpow_neg_one]
    simp only [zero_sub, Real.rpow_neg_one]
    have h1 : (Real.log N + Real.log (max Λ 1)) / (2 * d * N) + Cc * (N : ℝ)⁻¹ ≤
        (Real.log N + Real.log Λ) / (2 * d * N) + C₀ * (N : ℝ)⁻¹ := by
      have : (Real.log N + Real.log (max Λ 1)) / (2 * d * N) - (Real.log N + Real.log Λ) / (2 * d * N)
          = ((Real.log (max Λ 1) - Real.log Λ) / (2 * d)) * (N : ℝ)⁻¹ := by
        field_simp
        ring
      have h2 : ((Real.log (max Λ 1) - Real.log Λ) / (2 * d) + Cc) * (N : ℝ)⁻¹ ≤ C₀ * (N : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hNpos.le)
      nlinarith
    exact h1
  · simp only [h0, if_false, zero_add, add_zero] at hC ⊢
    exact mul_le_mul_of_nonneg_right hC hb.le |>.trans' (by nlinarith)

/-! ### Regularity of the mean-field slices -/

theorem sa26_regular_mono {s Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} {r r' : ℕ} (hr : r' ≤ r)
    (h : IsRegularMFRd s r Λ T ρ) : IsRegularMFRd s r' Λ T ρ := by
  refine ⟨fun t ht => ?_, h.2⟩
  obtain ⟨hcb, hfin, hle⟩ := h.1 t ht
  have hw : weightedSupE r' ((d : ℝ) + 3) (ρ t) ≤ weightedSupE r ((d : ℝ) + 3) (ρ t) :=
    HRS.MS.Fcau.fcau_weightedSupE_mono hr _ _
  refine ⟨⟨hcb.1.of_le (by exact_mod_cast hr), fun j hj => hcb.2 j (hj.trans hr)⟩,
    lt_of_le_of_lt hw hfin, ?_⟩
  have h1 : HRS.cbNorm r' (ρ t) ≤ HRS.cbNorm r (ρ t) := HRS.MS.Go.s55_cb_mono hr
  have h2 : (weightedSupE r' ((d : ℝ) + 3) (ρ t)).toReal ≤ (weightedSupE r ((d : ℝ) + 3) (ρ t)).toReal :=
    ENNReal.toReal_mono hfin.ne hw
  linarith

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ} {𝔈 : ℕ → ℝ}

theorem sa26_rho_le (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S.T) (x : Euc d) : S.ρ N t x ≤ Λ := by
  obtain ⟨hmem, -, hle⟩ := (hS.mean_field.regular N hN).1 t ht
  exact Q09A.rho_le_of_cbNorm hmem ENNReal.toReal_nonneg hle x

theorem sa26_Lam_pos (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) : 0 < Λ := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) S.T := ⟨le_rfl, S.hT.le⟩
  have hprob := (hS.mean_field.solution 1 le_rfl).density 0 h0
  by_contra hΛ
  push_neg at hΛ
  have hz : ∀ x, S.ρ 1 0 x = 0 := fun x =>
    le_antisymm ((sa26_rho_le hS le_rfl h0 x).trans hΛ) (hprob.nonneg x)
  have := hprob.integral_one
  simp [hz] at this

theorem sa26_regSlice (hS : RdStanding S R MB Λ ΛV G₀ m20 (r) mV C₀ 𝔈) (hr : 3 ≤ r) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) : HRS.MH.DualityRd.RegSliceRd (S.ρ N t) := by
  obtain ⟨hcb, hfin, -⟩ := (hS.mean_field.regular N hN).1 t ht
  refine ⟨(hS.mean_field.solution N hN).density t ht,
    ⟨hcb.1.of_le (by exact_mod_cast hr), fun j hj => hcb.2 j (hj.trans hr)⟩, ?_⟩
  exact lt_of_le_of_lt (HRS.MS.Fcau.fcau_weightedSupE_mono hr _ _) hfin

theorem sa26_init_ae {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {P : Measure Ω} {D : WholeDyn d} {T : ℝ}
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (h : SelectedFlowRd P D T X₀ W X) : ∀ᵐ ζ ∂P, X 0 ζ = X₀ ζ := by
  rcases h.flow with ⟨h1, -⟩ | ⟨-, -, -, -, h2⟩ | ⟨-, -, -, -, h3⟩
  · exact h1.init
  · exact h2.toContact.init
  · exact h3.init

end HRS.MS.PathFidi
