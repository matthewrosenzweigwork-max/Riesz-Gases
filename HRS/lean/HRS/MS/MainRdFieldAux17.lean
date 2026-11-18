import HRS.MS.MainRdFieldAux16
import HRS.MS.MainRdFieldAux13
import HRS.MP.RdLimitGauss

/-!
# S.A.7, packet P9a: the `L²` remainder bound and the `W₁` estimate for one `N`

* `sa6_remainder_L2`: `(E‖R‖²)^{1/2} ≤ c T (𝔈'_N + e_N)` from the pathwise bound and `EnergySmallness2Rd.bound`
  (Cauchy-Schwarz in time, Minkowski in `L²(P)` for `F + o + e`);
* `sa6_core_W1`: `W₁(Law Ξ, Law(I) ∗ ν_G) ≤ ε^f_1 + (2 t q C_p C_k 𝔴_N)^{1/2} + ½ K' σ T (𝔈 + e)`
  from `hilbert_polar_coupling` and `sa6_assembly_w1`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem HRS.MH.DualityRd

variable {d : ℕ}

lemma sa6_rpow_half_sq (x : ℝ≥0∞) : (x ^ 2) ^ ((1 : ℝ) / 2) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma sa6_half_rpow_sq' (x : ℝ≥0∞) : (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma sa6_sq_of_rpow_half {X Y : ℝ≥0∞} (h : X ^ ((1 : ℝ) / 2) ≤ Y) : X ≤ Y ^ 2 := by
  have h2 := pow_le_pow_left' h 2
  rwa [sa6_half_rpow_sq'] at h2

section L2

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}
  {Γ : ℕ} {χ : Euc d → ℝ} {m₀ : ℕ} {Ψ : ℕ → Set (Euc d → ℝ)} {𝔈' ε2 : ℕ → ℝ}

theorem sa6_uncurry_ofReal {α : Type*} [MeasurableSpace α] (G : ℝ → α → ℝ)
    (h : Measurable fun p : ℝ × α => G p.1 p.2) :
    Measurable (Function.uncurry fun (ζ : α) (r : ℝ) => ENNReal.ofReal (G r ζ)) := by
  have h1 : Measurable fun p : α × ℝ => G p.2 p.1 := h.comp measurable_swap
  exact h1.ennreal_ofReal

theorem sa6_slice_meas {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (F : α → β → ℝ≥0∞)
    (h : Measurable (Function.uncurry F)) (a : α) : Measurable fun b => F a b :=
  h.comp (measurable_const.prodMk measurable_id)

theorem sa6_remainder_L2
    (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 3) (Γ + 3) C₀ 𝔈) {e : ℕ → ℝ} (he : ∀ N, 0 ≤ e N)
    {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (Rr : (R N).Ω → HNeg d (Γ : ℝ))
    (hpath : ∀ᵐ ζ ∂(R N).P, ‖Rr ζ‖ₑ ≤ ENNReal.ofReal c *
      ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (sa6_Gc S R N C₀ Λ e r ζ))
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    (h2 : EnergySmallness2Rd S R C₀ Λ χ m₀ Ψ 𝔈' ε2) :
    (∫⁻ ζ, ‖Rr ζ‖ₑ ^ 2 ∂(R N).P) ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal (c * S.T * (𝔈' N + e N)) := by
  classical
  have hT : 0 ≤ S.T := S.hT.le
  have hXm := mrr_prog_meas ℱ (R N).X hF.progressive hT
  have hGm : Measurable fun p : ℝ × (R N).Ω => sa6_Gc S R N C₀ Λ e p.1 p.2 :=
    ((mrr_energy_meas hS hN).comp (measurable_fst.prodMk hXm)).add measurable_const
  have h𝔈' := h2.𝔈'_nonneg N hN
  set g : ℝ → (R N).Ω → ℝ≥0∞ := fun r ζ => ENNReal.ofReal (sa6_Gc S R N C₀ Λ e r ζ) with hg
  have hgm : Measurable (Function.uncurry fun (ζ : (R N).Ω) (r : ℝ) => g r ζ) :=
    sa6_uncurry_ofReal (G := sa6_Gc S R N C₀ Λ e) hGm
  -- per time: Minkowski
  have hr' : ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∫⁻ ζ, g r ζ ^ 2 ∂(R N).P ≤
      ENNReal.ofReal (𝔈' N + e N) ^ 2 := by
    intro r hr
    set corr : (R N).Ω → ℝ := fun ζ => correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal r) ζ) r with hcorr
    have hcm : Measurable corr := by
      have h0 := ((mrr_energy_meas hS hN).comp
        ((measurable_const (a := r)).prodMk (Q09A.selectedFlow_measurable (hS.flow N hN) (Real.toNNReal r))))
      convert h0 using 1
      funext ζ
      simp only [hcorr, Function.comp, correctedEnergyRd, mrrClamp_of_mem hr]
    set f : (R N).Ω → ℝ≥0∞ := fun ζ => ENNReal.ofReal (corr ζ) with hf
    set g0 : (R N).Ω → ℝ≥0∞ := fun _ => ENNReal.ofReal (e N) with hg0
    have hfm : Measurable f := ENNReal.measurable_ofReal.comp hcm
    have hpt : ∀ ζ, g r ζ ≤ (f + g0) ζ := fun ζ => by
      simp only [hg, sa6_Gc, Pi.add_apply, hf, hg0, hcorr, correctedEnergyRd, mrrClamp_of_mem hr]
      exact ENNReal.ofReal_add_le
    have hmink := ENNReal.lintegral_Lp_add_le (μ := (R N).P) (p := 2) hfm.aemeasurable
      (measurable_const (a := ENNReal.ofReal (e N))).aemeasurable one_le_two
    simp only [ENNReal.rpow_two] at hmink
    have hf2 : ∫⁻ ζ, f ζ ^ 2 ∂(R N).P ≤ ENNReal.ofReal (𝔈' N) ^ 2 := by
      refine le_trans (lintegral_mono fun ζ => ?_) (h2.bound N hN r hr |>.trans (le_of_eq ?_))
      · show ENNReal.ofReal (corr ζ) ^ 2 ≤ ENNReal.ofReal ((correctedEnergyRd S C₀ Λ N
          ((R N).X (Real.toNNReal r) ζ) r) ^ 2)
        by_cases h0 : 0 ≤ corr ζ
        · rw [← ENNReal.ofReal_pow h0]
        · push Not at h0
          simp [ENNReal.ofReal_of_nonpos h0.le]
      · rw [ENNReal.ofReal_pow h𝔈']
    have hg2 : ∫⁻ ζ, g0 ζ ^ 2 ∂(R N).P = ENNReal.ofReal (e N) ^ 2 := by simp [hg0]
    have h3 : (∫⁻ ζ, (f + g0) ζ ^ 2 ∂(R N).P) ^ ((1 : ℝ) / 2) ≤
        ENNReal.ofReal (𝔈' N + e N) := by
      refine hmink.trans ?_
      rw [hg2, sa6_rpow_half_sq, ENNReal.ofReal_add h𝔈' (he N)]
      refine add_le_add ?_ le_rfl
      calc (∫⁻ ζ, f ζ ^ 2 ∂(R N).P) ^ ((1 : ℝ) / 2) ≤ (ENNReal.ofReal (𝔈' N) ^ 2) ^ ((1 : ℝ) / 2) :=
            ENNReal.rpow_le_rpow hf2 (by norm_num)
        _ = _ := sa6_rpow_half_sq _
    calc ∫⁻ ζ, g r ζ ^ 2 ∂(R N).P ≤ ∫⁻ ζ, (f + g0) ζ ^ 2 ∂(R N).P :=
          lintegral_mono fun ζ => pow_le_pow_left' (hpt ζ) 2
      _ ≤ ENNReal.ofReal (𝔈' N + e N) ^ 2 := sa6_sq_of_rpow_half h3
  -- Cauchy-Schwarz in time, pathwise
  have hcs : ∀ ζ, (∫⁻ r in Set.Icc (0 : ℝ) S.T, g r ζ) ^ 2 ≤
      ENNReal.ofReal S.T * ∫⁻ r in Set.Icc (0 : ℝ) S.T, g r ζ ^ 2 := by
    intro ζ
    have hgmζ : Measurable fun r => g r ζ :=
      sa6_slice_meas (F := fun (ζ : (R N).Ω) (r : ℝ) => g r ζ) hgm ζ
    have h := HRS.MP.RdLGS.rlg_cs_pair (P := volume.restrict (Set.Icc (0 : ℝ) S.T))
      (f := fun r => g r ζ) (g := fun _ => (1 : ℝ≥0∞)) hgmζ measurable_const
      (a := (∫⁻ r in Set.Icc (0 : ℝ) S.T, g r ζ ^ 2) ^ ((1 : ℝ) / 2))
      (b := (ENNReal.ofReal S.T) ^ ((1 : ℝ) / 2))
      (by rw [sa6_half_rpow_sq'])
      (by rw [sa6_half_rpow_sq']; simp)
    simp only [mul_one] at h
    have h' := pow_le_pow_left' h 2
    rw [mul_pow, sa6_half_rpow_sq', sa6_half_rpow_sq'] at h'
    rwa [mul_comm] at h'
  have hbd : ∀ᵐ ζ ∂(R N).P, ‖Rr ζ‖ₑ ^ 2 ≤ ENNReal.ofReal c ^ 2 *
      (ENNReal.ofReal S.T * ∫⁻ r in Set.Icc (0 : ℝ) S.T, g r ζ ^ 2) := by
    filter_upwards [hpath] with ζ h
    calc ‖Rr ζ‖ₑ ^ 2 ≤ (ENNReal.ofReal c * ∫⁻ r in Set.Icc (0 : ℝ) S.T, g r ζ) ^ 2 :=
          pow_le_pow_left' h 2
      _ = ENNReal.ofReal c ^ 2 * (∫⁻ r in Set.Icc (0 : ℝ) S.T, g r ζ) ^ 2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul' le_rfl (hcs ζ)
  have hgm2 : AEMeasurable (Function.uncurry fun (ζ : (R N).Ω) (r : ℝ) => g r ζ ^ 2) ((R N).P.prod
      (volume.restrict (Set.Icc (0 : ℝ) S.T))) := (hgm.pow_const 2).aemeasurable
  have hswap : ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) S.T, g r ζ ^ 2) ∂(R N).P ≤
      ENNReal.ofReal S.T * ENNReal.ofReal (𝔈' N + e N) ^ 2 := by
    rw [lintegral_lintegral_swap hgm2]
    calc ∫⁻ r in Set.Icc (0 : ℝ) S.T, ∫⁻ ζ, g r ζ ^ 2 ∂(R N).P
        ≤ ∫⁻ _r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (𝔈' N + e N) ^ 2 :=
          setLIntegral_mono' measurableSet_Icc fun r hr => hr' r hr
      _ = _ := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero]
          exact mul_comm _ _
  have htot : ∫⁻ ζ, ‖Rr ζ‖ₑ ^ 2 ∂(R N).P ≤ ENNReal.ofReal (c * S.T * (𝔈' N + e N)) ^ 2 := by
    calc ∫⁻ ζ, ‖Rr ζ‖ₑ ^ 2 ∂(R N).P ≤ ∫⁻ ζ, ENNReal.ofReal c ^ 2 *
          (ENNReal.ofReal S.T * ∫⁻ r in Set.Icc (0 : ℝ) S.T, g r ζ ^ 2) ∂(R N).P :=
          lintegral_mono_ae hbd
      _ = ENNReal.ofReal c ^ 2 * (ENNReal.ofReal S.T * ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
            g r ζ ^ 2) ∂(R N).P) := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
      _ ≤ ENNReal.ofReal c ^ 2 * (ENNReal.ofReal S.T *
            (ENNReal.ofReal S.T * ENNReal.ofReal (𝔈' N + e N) ^ 2)) := by gcongr
      _ = ENNReal.ofReal (c * S.T * (𝔈' N + e N)) ^ 2 := by
          have h2' : 0 ≤ 𝔈' N + e N := add_nonneg h𝔈' (he N)
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hc0]
          ring
  calc (∫⁻ ζ, ‖Rr ζ‖ₑ ^ 2 ∂(R N).P) ^ ((1 : ℝ) / 2) ≤
        (ENNReal.ofReal (c * S.T * (𝔈' N + e N)) ^ 2) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow htot (by norm_num)
    _ = _ := sa6_rpow_half_sq _

end L2

end HRS.MS.MainRdField
