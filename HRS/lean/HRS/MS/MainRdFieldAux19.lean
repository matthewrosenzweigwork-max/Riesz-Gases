import HRS.MS.MainRdFieldAux18
import HRS.MS.MainRdFieldAux15

/-!
# S.A.7, packet P9c: `rd_field_wasserstein_one` / `_two` for `Λ ≥ 1`

The Wasserstein bounds from the coupling step `sa6_core_W` (Aux18), the remainder bounds `sa6_remainder_L1` / `sa6_remainder_L2`
and the covariance bound; `Λ_T := 1`.  The statements are those of `HRS.Whole.AppendixA.rd_field_wasserstein_one/_two`
with the extra hypothesis `1 ≤ Λ`, which `Aux20` removes by the `Λ`-normalisation.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem HRS.MH.DualityRd

variable {d : ℕ}

theorem sa6_w1_core (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad : ℝ) (hΛ : 1 ≤ Λ) :
        ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 3) (fd.Gamma + 3) C₀ 𝔈 →
        FieldAdjointInputRd fd S Kad →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
        ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
          TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        ∀ εf1 : ℕ → ℝ, (∀ N : ℕ, 1 ≤ N → 0 ≤ εf1 N) →
          (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
            wassersteinE 1 (law (R N).P (Iemp N t)) (law (R N).P (I N t)) ≤ ENNReal.ofReal (εf1 N)) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ N : ℕ, C ≤ (N : ℝ) →
          ∀ νG : Measure (HNeg d (fd.Gamma : ℝ)),
            IsLinearFieldNoiseRd (S.coeff N) (S.qN N) t fd.Gamma νG →
            ∀ Ξ : (R N).Ω → HNeg d (fd.Gamma : ℝ), Measurable Ξ →
              IsFluctFieldRepr S R N fd.Gamma t Ξ →
              wassersteinE 1 (law (R N).P Ξ) (linearFieldLawRd (R N).P (I N t) νG) ≤
                ENNReal.ofReal (C * Real.exp (ΛT * t) *
                  (εf1 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + S.sigma N * (𝔈 N + fd.eN N))) := by
  classical
  obtain ⟨C₀m, hin⟩ := sa6_inputs s fd ν₀ MB Λ ΛV G₀ νbar T m20 χ hχ Kad hΛ
  refine ⟨C₀m, fun C₀ hC₀ => ?_⟩
  obtain ⟨K', Cp, Ck, hCk0, hall⟩ := hin C₀ hC₀
  set Cp' : ℝ := max Cp 0 with hCp'
  set c1 : ℝ := max K' 0 / 2 * T with hc1
  set c2 : ℝ := Real.sqrt (2 * T * Cp' * Ck) with hc2
  set Cc : ℝ := max 2 (max c1 c2) with hCc
  have hCc2 : 2 ≤ Cc := le_max_left _ _
  refine ⟨Cc, 1, by linarith, one_pos, ?_⟩
  intro S hs hT hinv hH R 𝔈 hS hFA m₂ hm₂ hm2 m₀ ε hinit0 εf Iemp I hinit εf1 hεf1 hW t ht N hNC νG hνG Ξ hΞm hΞ
  subst hs
  subst hT
  obtain ⟨hsel, hCpf, KF, hKF, hcN⟩ := hall S rfl rfl hinv hH R 𝔈 hS hFA
  have ht' : t ∈ Set.Icc (0 : ℝ) S.T := ht
  have hT0 : 0 ≤ S.T := S.hT.le
  have he : ∀ N, 0 ≤ fd.eN N := mrr_eN_nonneg fd
  have hN2 : 2 ≤ N := by exact_mod_cast (le_trans hCc2 hNC)
  have hN1 : 1 ≤ N := by omega
  obtain ⟨Rr, D, hD0, hD, hpath, hW1, hW2⟩ := sa6_core_W (Kad := Kad) (Cp := Cp) (χ := χ) hS hΛ hFA.deriv he hsel
    hCk0 hCpf hm₂ hm2 hinit hN2 ht' (sa6_inj_N hS hN1) (hKF N hN1) (hcN N hN1 t ht') hνG hΞm hΞ
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  have hc0 : 0 ≤ S.sigma N / 2 * max K' 0 := mul_nonneg (by have := mrr_sigma_nonneg S N; positivity) (le_max_right _ _)
  have hL := sa6_remainder_L1 hS he hN1 hc0 Rr hpath hF
  have hq0 := sa6_qN_nonneg S N
  have hw := sa6_wN_nonneg (d := d) (N := N) (hS.energy.pos N hN1).le hm₂
  have hσ := mrr_sigma_nonneg S N
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
  have hε1 := hεf1 N hN1
  have hqw : 0 ≤ S.qN N * wN d N (𝔈 N) m₂ := mul_nonneg hq0 hw
  have hCp0 : 0 ≤ 2 * S.T * Cp' * Ck := by positivity
  have hDle : D ≤ (2 * S.T * Cp' * Ck) * (S.qN N * wN d N (𝔈 N) m₂) := by
    refine hD.trans ?_
    have : t * (2 * S.qN N * max Cp 0 * Ck * wN d N (𝔈 N) m₂) =
        t * (2 * Cp' * Ck) * (S.qN N * wN d N (𝔈 N) m₂) := by rw [hCp']; ring
    rw [this]
    have h2' : 0 ≤ 2 * Cp' * Ck := by positivity
    calc t * (2 * Cp' * Ck) * (S.qN N * wN d N (𝔈 N) m₂) ≤ S.T * (2 * Cp' * Ck) * (S.qN N * wN d N (𝔈 N) m₂) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht'.2 h2') hqw
      _ = _ := by ring
  have hsD : Real.sqrt D ≤ c2 * Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) := by
    calc Real.sqrt D ≤ Real.sqrt ((2 * S.T * Cp' * Ck) * (S.qN N * wN d N (𝔈 N) m₂)) := Real.sqrt_le_sqrt hDle
      _ = _ := Real.sqrt_mul hCp0 _
  have hc2n : 0 ≤ c2 := Real.sqrt_nonneg _
  have hX : 0 ≤ S.sigma N * (𝔈 N + fd.eN N) := mul_nonneg hσ (add_nonneg h𝔈 (he N))
  have hsq := Real.sqrt_nonneg (S.qN N * wN d N (𝔈 N) m₂)
  have hfin : ENNReal.ofReal (εf1 N) + ENNReal.ofReal (Real.sqrt D) +
      ENNReal.ofReal (S.sigma N / 2 * max K' 0 * S.T * (𝔈 N + fd.eN N)) ≤
      ENNReal.ofReal (Cc * Real.exp (1 * t) * (εf1 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) +
        S.sigma N * (𝔈 N + fd.eN N))) := by
    rw [← ENNReal.ofReal_add hε1 (Real.sqrt_nonneg _), ← ENNReal.ofReal_add (by positivity)
      (by have : 0 ≤ S.sigma N / 2 * max K' 0 * S.T * (𝔈 N + fd.eN N) := by
            have := add_nonneg h𝔈 (he N)
            positivity
          exact this)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hexp : 1 ≤ Real.exp (1 * t) := Real.one_le_exp (by have := ht'.1; linarith)
    have e1 : S.sigma N / 2 * max K' 0 * S.T * (𝔈 N + fd.eN N) = c1 * (S.sigma N * (𝔈 N + fd.eN N)) := by
      rw [hc1]; ring
    have hc1C : c1 ≤ Cc := le_trans (le_max_left _ _) (le_max_right _ _)
    have hc2C : c2 ≤ Cc := le_trans (le_max_right _ _) (le_max_right _ _)
    have hsum : 0 ≤ εf1 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + S.sigma N * (𝔈 N + fd.eN N) := by positivity
    rw [e1]
    have h1 : εf1 N + c2 * Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + c1 * (S.sigma N * (𝔈 N + fd.eN N)) ≤
        Cc * (εf1 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + S.sigma N * (𝔈 N + fd.eN N)) := by
      have a1 : c2 * Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) ≤ Cc * Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) :=
        mul_le_mul_of_nonneg_right hc2C hsq
      have a2 : c1 * (S.sigma N * (𝔈 N + fd.eN N)) ≤ Cc * (S.sigma N * (𝔈 N + fd.eN N)) :=
        mul_le_mul_of_nonneg_right hc1C hX
      have a3 : εf1 N ≤ Cc * εf1 N := by nlinarith
      linarith
    have h2'' : Cc * (εf1 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + S.sigma N * (𝔈 N + fd.eN N)) ≤
        Cc * Real.exp (1 * t) * (εf1 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + S.sigma N * (𝔈 N + fd.eN N)) := by
      have : Cc * 1 ≤ Cc * Real.exp (1 * t) := mul_le_mul_of_nonneg_left hexp (by linarith)
      nlinarith
    have hmono : εf1 N + Real.sqrt D + c1 * (S.sigma N * (𝔈 N + fd.eN N)) ≤
        εf1 N + c2 * Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + c1 * (S.sigma N * (𝔈 N + fd.eN N)) := by linarith
    linarith
  exact (hW1.trans (by
    calc _ ≤ ENNReal.ofReal (εf1 N) + ENNReal.ofReal (Real.sqrt D) + ENNReal.ofReal (S.sigma N / 2 * max K' 0 * S.T * (𝔈 N + fd.eN N)) := by
          gcongr
          exact hW N hN1 t ht'
      _ ≤ _ := hfin))

theorem sa6_w2_core (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad : ℝ) (hΛ : 1 ≤ Λ) :
        ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 3) (fd.Gamma + 3) C₀ 𝔈 →
        FieldAdjointInputRd fd S Kad →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
        ∀ (𝔈' ε2 : ℕ → ℝ), EnergySmallness2Rd S R C₀ Λ χ m₀ (fun _ => ∅) 𝔈' ε2 →
        ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
          TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        ∀ εf1 : ℕ → ℝ, (∀ N : ℕ, 1 ≤ N → 0 ≤ εf1 N) →
          (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
            wassersteinE 2 (law (R N).P (Iemp N t)) (law (R N).P (I N t)) ≤ ENNReal.ofReal (εf1 N)) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ N : ℕ, C ≤ (N : ℝ) →
          ∀ νG : Measure (HNeg d (fd.Gamma : ℝ)),
            IsLinearFieldNoiseRd (S.coeff N) (S.qN N) t fd.Gamma νG →
            ∀ Ξ : (R N).Ω → HNeg d (fd.Gamma : ℝ), Measurable Ξ →
              IsFluctFieldRepr S R N fd.Gamma t Ξ →
              wassersteinE 2 (law (R N).P Ξ) (linearFieldLawRd (R N).P (I N t) νG) ≤
                ENNReal.ofReal (C * Real.exp (ΛT * t) *
                  (εf1 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + S.sigma N * (𝔈' N + fd.eN N))) := by
  classical
  obtain ⟨C₀m, hin⟩ := sa6_inputs s fd ν₀ MB Λ ΛV G₀ νbar T m20 χ hχ Kad hΛ
  refine ⟨C₀m, fun C₀ hC₀ => ?_⟩
  obtain ⟨K', Cp, Ck, hCk0, hall⟩ := hin C₀ hC₀
  set Cp' : ℝ := max Cp 0 with hCp'
  set c1 : ℝ := max K' 0 / 2 * T with hc1
  set c2 : ℝ := Real.sqrt (2 * T * Cp' * Ck) with hc2
  set Cc : ℝ := max 2 (max c1 c2) with hCc
  have hCc2 : 2 ≤ Cc := le_max_left _ _
  refine ⟨Cc, 1, by linarith, one_pos, ?_⟩
  intro S hs hT hinv hH R 𝔈 hS hFA m₂ hm₂ hm2 m₀ ε hinit0 𝔈' ε2 h2 εf Iemp I hinit εf1 hεf1 hW t ht N hNC νG hνG Ξ hΞm hΞ
  subst hs
  subst hT
  obtain ⟨hsel, hCpf, KF, hKF, hcN⟩ := hall S rfl rfl hinv hH R 𝔈 hS hFA
  have ht' : t ∈ Set.Icc (0 : ℝ) S.T := ht
  have hT0 : 0 ≤ S.T := S.hT.le
  have he : ∀ N, 0 ≤ fd.eN N := mrr_eN_nonneg fd
  have hN2 : 2 ≤ N := by exact_mod_cast (le_trans hCc2 hNC)
  have hN1 : 1 ≤ N := by omega
  obtain ⟨Rr, D, hD0, hD, hpath, hW1, hW2⟩ := sa6_core_W (Kad := Kad) (Cp := Cp) (χ := χ) hS hΛ hFA.deriv he hsel
    hCk0 hCpf hm₂ hm2 hinit hN2 ht' (sa6_inj_N hS hN1) (hKF N hN1) (hcN N hN1 t ht') hνG hΞm hΞ
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  have hc0 : 0 ≤ S.sigma N / 2 * max K' 0 := mul_nonneg (by have := mrr_sigma_nonneg S N; positivity) (le_max_right _ _)
  have hL := sa6_remainder_L2 hS he hN1 hc0 Rr hpath hF h2
  have hq0 := sa6_qN_nonneg S N
  have hw := sa6_wN_nonneg (d := d) (N := N) (hS.energy.pos N hN1).le hm₂
  have hσ := mrr_sigma_nonneg S N
  have h𝔈 : 0 ≤ 𝔈' N := h2.𝔈'_nonneg N hN1
  have hε1 := hεf1 N hN1
  have hqw : 0 ≤ S.qN N * wN d N (𝔈 N) m₂ := mul_nonneg hq0 hw
  have hCp0 : 0 ≤ 2 * S.T * Cp' * Ck := by positivity
  have hDle : D ≤ (2 * S.T * Cp' * Ck) * (S.qN N * wN d N (𝔈 N) m₂) := by
    refine hD.trans ?_
    have : t * (2 * S.qN N * max Cp 0 * Ck * wN d N (𝔈 N) m₂) =
        t * (2 * Cp' * Ck) * (S.qN N * wN d N (𝔈 N) m₂) := by rw [hCp']; ring
    rw [this]
    have h2' : 0 ≤ 2 * Cp' * Ck := by positivity
    calc t * (2 * Cp' * Ck) * (S.qN N * wN d N (𝔈 N) m₂) ≤ S.T * (2 * Cp' * Ck) * (S.qN N * wN d N (𝔈 N) m₂) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht'.2 h2') hqw
      _ = _ := by ring
  have hsD : Real.sqrt D ≤ c2 * Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) := by
    calc Real.sqrt D ≤ Real.sqrt ((2 * S.T * Cp' * Ck) * (S.qN N * wN d N (𝔈 N) m₂)) := Real.sqrt_le_sqrt hDle
      _ = _ := Real.sqrt_mul hCp0 _
  have hc2n : 0 ≤ c2 := Real.sqrt_nonneg _
  have hX : 0 ≤ S.sigma N * (𝔈' N + fd.eN N) := mul_nonneg hσ (add_nonneg h𝔈 (he N))
  have hsq := Real.sqrt_nonneg (S.qN N * wN d N (𝔈 N) m₂)
  have hfin : ENNReal.ofReal (εf1 N) + ENNReal.ofReal (Real.sqrt D) +
      ENNReal.ofReal (S.sigma N / 2 * max K' 0 * S.T * (𝔈' N + fd.eN N)) ≤
      ENNReal.ofReal (Cc * Real.exp (1 * t) * (εf1 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) +
        S.sigma N * (𝔈' N + fd.eN N))) := by
    rw [← ENNReal.ofReal_add hε1 (Real.sqrt_nonneg _), ← ENNReal.ofReal_add (by positivity)
      (by have : 0 ≤ S.sigma N / 2 * max K' 0 * S.T * (𝔈' N + fd.eN N) := by
            have := add_nonneg h𝔈 (he N)
            positivity
          exact this)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hexp : 1 ≤ Real.exp (1 * t) := Real.one_le_exp (by have := ht'.1; linarith)
    have e1 : S.sigma N / 2 * max K' 0 * S.T * (𝔈' N + fd.eN N) = c1 * (S.sigma N * (𝔈' N + fd.eN N)) := by
      rw [hc1]; ring
    have hc1C : c1 ≤ Cc := le_trans (le_max_left _ _) (le_max_right _ _)
    have hc2C : c2 ≤ Cc := le_trans (le_max_right _ _) (le_max_right _ _)
    have hsum : 0 ≤ εf1 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + S.sigma N * (𝔈' N + fd.eN N) := by positivity
    rw [e1]
    have h1 : εf1 N + c2 * Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + c1 * (S.sigma N * (𝔈' N + fd.eN N)) ≤
        Cc * (εf1 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + S.sigma N * (𝔈' N + fd.eN N)) := by
      have a1 : c2 * Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) ≤ Cc * Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) :=
        mul_le_mul_of_nonneg_right hc2C hsq
      have a2 : c1 * (S.sigma N * (𝔈' N + fd.eN N)) ≤ Cc * (S.sigma N * (𝔈' N + fd.eN N)) :=
        mul_le_mul_of_nonneg_right hc1C hX
      have a3 : εf1 N ≤ Cc * εf1 N := by nlinarith
      linarith
    have h2'' : Cc * (εf1 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + S.sigma N * (𝔈' N + fd.eN N)) ≤
        Cc * Real.exp (1 * t) * (εf1 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + S.sigma N * (𝔈' N + fd.eN N)) := by
      have : Cc * 1 ≤ Cc * Real.exp (1 * t) := mul_le_mul_of_nonneg_left hexp (by linarith)
      nlinarith
    have hmono : εf1 N + Real.sqrt D + c1 * (S.sigma N * (𝔈' N + fd.eN N)) ≤
        εf1 N + c2 * Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + c1 * (S.sigma N * (𝔈' N + fd.eN N)) := by linarith
    linarith
  exact (hW2.trans (by
    calc _ ≤ ENNReal.ofReal (εf1 N) + ENNReal.ofReal (Real.sqrt D) + ENNReal.ofReal (S.sigma N / 2 * max K' 0 * S.T * (𝔈' N + fd.eN N)) := by
          gcongr
          exact hW N hN1 t ht'
      _ ≤ _ := hfin))

end HRS.MS.MainRdField
