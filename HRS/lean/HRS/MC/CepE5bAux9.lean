import HRS.MC.CepE5bAux7
import HRS.MC.CepE4Aux6
import HRS.Stochastic.Ito

/-!
# Packet CEPE5B, auxiliary 9: the Itô integrand along the chamber solution is `L²`

For `g ∈ C²` with `‖Dg(x)‖ ≤ c₀ + c₁‖x‖` and a path with `‖Z_s‖ ≤ A + |σ'| ‖w_s‖`, `A ∈ L²`, the Itô integrand
`1_{[0,T]}(s) Dg(Z_s)[σ_k]` is in `IsProgressiveL2`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepE5b

open HRS HRS.MC.Cepa HRS.MC.CepE4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem e5b_ito_abs_le {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {T : ℝ}
    {f : ℝ → E → ℝ} {X : ℝ → Ω → E} {Φ : ℝ → Ω → ι → E} (s : ℝ) (ω : Ω) (k : ι) :
    |itoIntegrand T Set.univ f X Φ s ω k| ≤
      Set.indicator (Icc 0 T) (fun s => ‖fderiv ℝ (f s) (X s ω)‖ * ‖Φ s ω k‖) s := by
  by_cases hs : s ∈ Icc 0 T
  · rw [Set.indicator_of_mem hs]
    have : itoIntegrand T Set.univ f X Φ s ω k = fderiv ℝ (f s) (X s ω) (Φ s ω k) := by
      simp [itoIntegrand, Set.indicator, hs]
    rw [this, ← Real.norm_eq_abs]
    exact ContinuousLinearMap.le_opNorm _ _
  · rw [Set.indicator_of_notMem hs]
    simp [itoIntegrand, Set.indicator, hs]

theorem e5b_real_dom {cσ cg0 cg1 σ' A wn x : ℝ} (hcσ : 0 ≤ cσ) (hcg0 : 0 ≤ cg0) (hcg1 : 0 ≤ cg1)
    (hx : 0 ≤ x) (hxsq : x ^ 2 ≤ 2 * A ^ 2 + 2 * σ' ^ 2 * wn ^ 2) :
    cσ * (cg0 + cg1 * x) ^ 2 ≤ (2 * cσ * (cg0 ^ 2 + 2 * cg1 ^ 2 * (1 + σ' ^ 2))) * (1 + A ^ 2 + wn ^ 2) := by
  have h1 : (cg0 + cg1 * x) ^ 2 ≤ 2 * cg0 ^ 2 + 2 * (cg1 ^ 2 * x ^ 2) := by
    nlinarith [sq_nonneg (cg0 - cg1 * x)]
  have h2 : cg1 ^ 2 * x ^ 2 ≤ cg1 ^ 2 * (2 * A ^ 2 + 2 * σ' ^ 2 * wn ^ 2) :=
    mul_le_mul_of_nonneg_left hxsq (sq_nonneg _)
  have h3 : (cg0 + cg1 * x) ^ 2 ≤ 2 * (cg0 ^ 2 + 2 * cg1 ^ 2 * (1 + σ' ^ 2)) * (1 + A ^ 2 + wn ^ 2) := by
    have hA := sq_nonneg A
    have hw := sq_nonneg wn
    have hσ := sq_nonneg σ'
    have hc := sq_nonneg cg0
    have hc1 := sq_nonneg cg1
    nlinarith [mul_nonneg hc1 hA, mul_nonneg hc1 hw, mul_nonneg (mul_nonneg hc1 hσ) hw, mul_nonneg hc1 hσ]
  calc cσ * (cg0 + cg1 * x) ^ 2 ≤ cσ * (2 * (cg0 ^ 2 + 2 * cg1 ^ 2 * (1 + σ' ^ 2)) * (1 + A ^ 2 + wn ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 hcσ
    _ = _ := by ring

theorem e5b_progL2 [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {T σ' : ℝ} {w Z : ℝ → Ω → Ch N}
    {A : Ω → ℝ} (S : E4Setup P ℱ N T σ' w Z A) (hT : 0 ≤ T) {g : Ch N → ℝ} (hg : ContDiff ℝ 2 g)
    {cg0 cg1 : ℝ} (hcg0 : 0 ≤ cg0) (hcg1 : 0 ≤ cg1) (hgrad : ∀ x, ‖fderiv ℝ g x‖ ≤ cg0 + cg1 * ‖x‖)
    {ι : Type*} [Fintype ι] (σ : ι → Ch N) {ℱ' : Filtration ℝ mΩ}
    (hprog : IsProgressive ℱ' (ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => Z (u : ℝ) ω))) :
    IsProgressiveL2 P ℱ' (itoIntegrand T Set.univ (fun _ x => g x)
      (ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => Z (u : ℝ) ω)) (fun _ _ => σ)) := by
  set cσ : ℝ := ∑ k, ‖σ k‖ ^ 2 with hcσ
  have hcσ0 : 0 ≤ cσ := Finset.sum_nonneg fun _ _ => by positivity
  set c : ℝ := 2 * cσ * (cg0 ^ 2 + 2 * cg1 ^ 2 * (1 + σ' ^ 2)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hXZ : ∀ s ω, ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => Z (u : ℝ) ω) s ω = Z (max s 0) ω := by
    intro s ω
    simp [ofNNRealTime, Real.coe_toNNReal']
  refine ⟨isProgressive_itoIntegrand (isC12On_of_contDiff T Set.univ g hg) isClosed_univ
    (Set.Subset.refl _) hprog (isProgressive_const ℱ' σ), fun T' => ?_⟩
  unfold sqIntegralOn
  set D : ℝ × Ω → ℝ := e4_D A w T with hD
  have hDint : Integrable D ((e4_mu T).prod P) := e4_D_integrable S.hw S.hA T
  have hcD : Integrable (fun p => c * D p) ((e4_mu T).prod P) := hDint.const_mul c
  have hlt : ∫⁻ p, ENNReal.ofReal (c * D p) ∂((e4_mu T).prod P) < ⊤ := hcD.lintegral_lt_top
  have hmeas : AEMeasurable (fun p => ENNReal.ofReal (c * D p)) ((e4_mu T).prod P) :=
    hcD.aemeasurable.ennreal_ofReal
  rw [lintegral_prod_symm _ hmeas] at hlt
  refine lt_of_le_of_lt ?_ hlt
  refine lintegral_mono_ae ?_
  filter_upwards [S.hAb] with ω hω
  have hIcc : ∫⁻ s in Icc 0 T, ENNReal.ofReal (c * D (s, ω)) = ∫⁻ s in Ioc 0 T, ENNReal.ofReal (c * D (s, ω)) :=
    (setLIntegral_congr Ioc_ae_eq_Icc).symm
  calc ∫⁻ s in Icc 0 T', ∑ k, ‖itoIntegrand T Set.univ (fun _ x => g x)
          (ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => Z (u : ℝ) ω)) (fun _ _ => σ) s ω k‖ₑ ^ 2
      ≤ ∫⁻ s in Icc 0 T', Set.indicator (Icc 0 T) (fun s => ENNReal.ofReal (c * D (s, ω))) s := by
        refine lintegral_mono fun s => ?_
        rw [sum_enorm_sq_eq_ofReal]
        by_cases hs : s ∈ Icc 0 T
        · rw [Set.indicator_of_mem hs]
          refine ENNReal.ofReal_le_ofReal ?_
          have hpt : ∀ k, itoIntegrand T Set.univ (fun _ x => g x)
              (ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => Z (u : ℝ) ω)) (fun _ _ => σ) s ω k ^ 2 ≤
              ‖fderiv ℝ g (Z s ω)‖ ^ 2 * ‖σ k‖ ^ 2 := by
            intro k
            have h := e5b_ito_abs_le (T := T) (f := fun _ x => g x)
              (X := ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => Z (u : ℝ) ω)) (Φ := fun _ _ => σ) s ω k
            rw [Set.indicator_of_mem hs, hXZ, max_eq_left hs.1] at h
            have h' := pow_le_pow_left₀ (abs_nonneg _) h 2
            rw [sq_abs] at h'
            simpa [mul_pow] using h'
          calc ∑ k, itoIntegrand T Set.univ (fun _ x => g x)
                (ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => Z (u : ℝ) ω)) (fun _ _ => σ) s ω k ^ 2
              ≤ ∑ k, ‖fderiv ℝ g (Z s ω)‖ ^ 2 * ‖σ k‖ ^ 2 := Finset.sum_le_sum fun k _ => hpt k
            _ = cσ * ‖fderiv ℝ g (Z s ω)‖ ^ 2 := by
                rw [hcσ, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
            _ ≤ cσ * (cg0 + cg1 * ‖Z s ω‖) ^ 2 := by
                refine mul_le_mul_of_nonneg_left ?_ hcσ0
                exact pow_le_pow_left₀ (norm_nonneg _) (hgrad _) 2
            _ ≤ c * D (s, ω) := by
                have h1 := hω s hs
                have h2 := e4_Zsq_le h1 (norm_nonneg _) (norm_nonneg _)
                have h3 := e5b_real_dom (cσ := cσ) (cg0 := cg0) (cg1 := cg1) (σ' := σ') (A := A ω)
                  (wn := ‖w s ω‖) hcσ0 hcg0 hcg1 (norm_nonneg _) h2
                refine h3.trans (mul_le_mul_of_nonneg_left ?_ hc0)
                simp only [hD, e4_D]
                nlinarith [sq_nonneg ‖w T ω‖]
        · rw [Set.indicator_of_notMem hs]
          have : ∀ k, itoIntegrand T Set.univ (fun _ x => g x)
              (ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => Z (u : ℝ) ω)) (fun _ _ => σ) s ω k = 0 := by
            intro k
            simp [itoIntegrand, Set.indicator, hs]
          simp [this]
    _ ≤ ∫⁻ s, Set.indicator (Icc 0 T) (fun s => ENNReal.ofReal (c * D (s, ω))) s :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ s in Icc 0 T, ENNReal.ofReal (c * D (s, ω)) := lintegral_indicator measurableSet_Icc _
    _ = _ := hIcc

end HRS.MC.CepE5b
