import HRS.MS.ZeroTempAux14

/-!
# SA11, packet D2: the per-`N` conclusion of S.A.11

`sa11_main_N`: existence of measurable representatives `Ξ`, `Z` of the particle field and of the transported linear
approximation (both defined for every `ζ`), and the `W₁` bound
`W₁(Law Ξ, Law Z) ≤ K_T ε^f + (σ_N/2) K_c T (𝔈_N + c₂ e_N)` for every pair of measurable representatives.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal NNReal ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace HRS.MS.ZeroTemp

variable {d : ℕ} {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa11_dual_decomp (T : WmpSpace d m p →L[ℝ] WmpSpace d m p) (a ψ η : WmpSpace d m p →L[ℝ] ℝ) :
    ‖a - sa11_precomp T η‖ ≤ ‖a - sa11_precomp T ψ‖ + ‖T‖ * ‖ψ - η‖ := by
  have e : a - sa11_precomp T η = (a - sa11_precomp T ψ) + sa11_precomp T (ψ - η) := by
    ext F
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, sa11_precomp_apply]
    ring
  rw [e]
  have h1 := norm_add_le (a - sa11_precomp T ψ) (sa11_precomp T (ψ - η))
  have h2 := sa11_precomp_norm_le T (ψ - η)
  exact h1.trans (add_le_add le_rfl h2)

theorem sa11_integral_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Δ : Ω → ℝ) (B Ec : Ω → ℝ≥0∞)
    (KT : ℝ) (b : ℝ≥0∞) (ε : ℝ) (hB : Measurable B)
    (hpt : ∀ᵐ ζ ∂P, ENNReal.ofReal (Δ ζ) ≤ B ζ + ENNReal.ofReal KT * Ec ζ)
    (hBint : ∫⁻ ζ, B ζ ∂P ≤ b) (hEint : ∫⁻ ζ, Ec ζ ∂P ≤ ENNReal.ofReal ε) :
    ∫⁻ ζ, ENNReal.ofReal (Δ ζ) ∂P ≤ b + ENNReal.ofReal KT * ENNReal.ofReal ε := by
  calc ∫⁻ ζ, ENNReal.ofReal (Δ ζ) ∂P ≤ ∫⁻ ζ, (B ζ + ENNReal.ofReal KT * Ec ζ) ∂P := lintegral_mono_ae hpt
    _ = ∫⁻ ζ, B ζ ∂P + ∫⁻ ζ, ENNReal.ofReal KT * Ec ζ ∂P := lintegral_add_left hB _
    _ = ∫⁻ ζ, B ζ ∂P + ENNReal.ofReal KT * ∫⁻ ζ, Ec ζ ∂P := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ b + ENNReal.ofReal KT * ENNReal.ofReal ε := by gcongr

theorem sa11_lintegral_meas {Ω : Type*} [MeasurableSpace Ω] (T : ℝ) (G : ℝ → Ω → ℝ)
    (hG : Measurable fun q : ℝ × Ω => G q.1 q.2) :
    Measurable fun ζ : Ω => ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (G r ζ) := by
  have hm1 : Measurable (Function.uncurry fun (ζ : Ω) (r : ℝ) => ENNReal.ofReal (G r ζ)) :=
    ENNReal.measurable_ofReal.comp (hG.comp measurable_swap)
  exact hm1.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))

section MainN

variable (hd : 1 ≤ d) (hm : mStar d + ⌊(d : ℝ) / p⌋₊ + 1 ≤ m)

include hd hm

theorem sa11_main_N {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {Γ : ℕ}
    (hΓ : 1 ≤ Γ) {𝔈 : ℕ → ℝ} (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 3) (Γ + 3) C₀ 𝔈)
    {N : ℕ} (hN : 2 ≤ N) (hinv : S.invβ N = 0) {νbar ν₀ : ℝ} (hν : S.invβ N ≤ νbar)
    (hRg : RdRegimeHolds PDE.Regime.R1 d S.s S.M (S.invβ N) ν₀ ∨ HRS.MS.Star.UlocStarRegime d S.s S.M)
    {Kad : ℝ} (hA : AdjointInputRd (wClass m p) (wWeakClass m p) (mStar d) (S.coeff N) S.T Kad)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T)
    {Kc c₂ : ℝ} (hKc : 0 ≤ Kc) (hc₂ : 0 ≤ c₂) {e : ℕ → ℝ} (he : ∀ N, 0 ≤ e N)
    (hcomm : ∀ X : EucConfig d N, Function.Injective X → ∀ r₀ t' : ℝ, 0 ≤ r₀ → r₀ ≤ t' → t' ≤ S.T →
      ∀ φ : sa11_V d,
        |commN d S.s (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r₀ t' φ.1) x)) X
            (HRS.Whole.withDensityReal (S.ρ N r₀))| ≤
          Kc * ‖sa11_J (m := m) (p := p) φ‖ *
            (rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N r₀)) + oNΛ d S.s C₀ Λ N + c₂ * e N))
    (ηW Ξ0 : (R N).Ω → WNeg d m p) (hη : Measurable ηW)
    (hΞ0 : WNegRepr (R N).P Ξ0 fun φ ζ =>
      S.κ N * (HRS.Whole.pair (HRS.Whole.empirical ((R N).X₀ ζ)) φ - HRS.Whole.pair S.μ0 φ))
    {εfX : ℝ} (hε : 0 ≤ εfX) (hbd : ∫⁻ ζ, ‖Ξ0 ζ - ηW ζ‖ₑ ∂(R N).P ≤ ENNReal.ofReal εfX) :
    (∃ Ξ : (R N).Ω → WNeg d m p, Measurable Ξ ∧ IsFluctWRepr S R N m p t Ξ) ∧
    (∃ Z : (R N).Ω → WNeg d m p, Measurable Z ∧ IsTransportedWRepr S R N m p t ηW Z) ∧
    ∀ Ξ Z : (R N).Ω → WNeg d m p, Measurable Ξ → Measurable Z → IsFluctWRepr S R N m p t Ξ →
      IsTransportedWRepr S R N m p t ηW Z →
      wassersteinE 1 (law (R N).P Ξ) (law (R N).P Z) ≤
        ENNReal.ofReal (max Kad 0 * sa11_cJ d m * εfX + S.sigma N / 2 * Kc * S.T * (𝔈 N + c₂ * e N)) := by
  have hN1 : 1 ≤ N := by omega
  have hT : 0 ≤ S.T := S.hT.le
  haveI := (R N).isProb
  have hσ0 : 0 ≤ S.sigma N := HRS.MP.RdRem.mrr_sigma_nonneg S N
  have hAN : S.AN N = 1 := by simp [WholeMainData.AN, Ascale, hinv]
  have hσκ : S.sigma N = S.κ N := by simp [WholeMainData.sigma, sigmaScale, hinv]
  have hT0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) S.T := ⟨le_rfl, hT⟩
  have hρt := sa11_density_prob hS hN1 ht
  have hρ0 := sa11_density_prob hS hN1 hT0
  have hflow := sa11_flow_strong hN1 (hS.flow N hN1) hinv
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  have hXm := HRS.MP.RdRem.mrr_prog_meas ℱ (R N).X hF.progressive hT
  -- the transport data
  have hlin : ∀ (φ ψ : Euc d → ℝ) (c : ℝ), IsCcInfty φ → IsCcInfty ψ →
      propagatorW (S.coeff N) 0 t (fun x => φ x + c * ψ x) =
        fun x => propagatorW (S.coeff N) 0 t φ x + c * propagatorW (S.coeff N) 0 t ψ x := by
    intro φ ψ c hφ hψ
    exact sa11_propagatorW_lin hΓ hS hN1 hν hRg ht c
      (hA 0 t le_rfl ht.1 ht.2 φ (sa11_cd2 hφ) (sa11_wClass_mem ⟨φ, hφ⟩)).1
      (hA 0 t le_rfl ht.1 ht.2 ψ (sa11_cd2 hψ) (sa11_wClass_mem ⟨ψ, hψ⟩)).1 ⟨le_rfl, ht.1⟩
  have h : Sa11TransportData m p (S.coeff N) S.T Kad (mStar d) t := ⟨ht, hA, hlin⟩
  -- the particle field
  set Ξo : (R N).Ω → WNeg d m p := fun ζ =>
    (sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X (Real.toNNReal t) ζ) (S.ρ N t) hρt : WNeg d m p) with hΞo
  have hΞmeas : Measurable Ξo :=
    sa11_Xi_measurable (m := m) (p := p) hd hm (S.sigma N) (S.ρ N t) hρt _ (hflow.adapted (Real.toNNReal t))
  have hΞrep : IsFluctWRepr S R N m p t Ξo := by
    refine sa11_isFluct_of_apply Ξo fun φ ζ => ?_
    show (sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X (Real.toNNReal t) ζ) (S.ρ N t) hρt)
      (sa11_J (m := m) (p := p) φ) = _
    rw [sa11_Xi_apply hd hm, ← HRS.Whole.pair_empirical (by omega : 0 < N)]
  -- the transported field
  set Zo : (R N).Ω → WNeg d m p := fun ζ =>
    (sa11_precomp (sa11_Top h) (sa11_dual (ηW ζ)) : WNeg d m p) with hZo
  have hZmeas : Measurable Zo := sa11_Z_measurable (sa11_Top h) ηW hη
  have hZrep : IsTransportedWRepr S R N m p t ηW Zo := sa11_isTransported hAN h ηW
  refine ⟨⟨Ξo, hΞmeas, hΞrep⟩, ⟨Zo, hZmeas, hZrep⟩, fun Ξ' Z' hΞ'm hZ'm hΞ' hZ' => ?_⟩
  -- uniqueness of the representatives
  have hΞae : ∀ᵐ ζ ∂(R N).P, sa11_dual (Ξ' ζ) = sa11_dual (Ξo ζ) := by
    refine sa11_ae_eq_of_repr (R N).P (fun ζ => sa11_dual (Ξ' ζ)) (fun ζ => sa11_dual (Ξo ζ)) fun φ => ?_
    filter_upwards [hΞ' φ.1 φ.2 (sa11_J (m := m) (p := p) φ) (sa11_J_coe φ)] with ζ hζ
    rw [show sa11_dual (Ξ' ζ) (sa11_J (m := m) (p := p) φ) = (Ξ' ζ).eval (sa11_J φ) from rfl, hζ]
    show _ = (sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X (Real.toNNReal t) ζ) (S.ρ N t) hρt)
      (sa11_J (m := m) (p := p) φ)
    rw [sa11_Xi_apply hd hm, ← HRS.Whole.pair_empirical (by omega : 0 < N)]
  have hZae : ∀ᵐ ζ ∂(R N).P, sa11_dual (Z' ζ) = sa11_dual (Zo ζ) := by
    refine sa11_ae_eq_of_repr (R N).P (fun ζ => sa11_dual (Z' ζ)) (fun ζ => sa11_dual (Zo ζ)) fun φ => ?_
    filter_upwards [hZ' φ.1 φ.2 (sa11_J (m := m) (p := p) φ) (sa11_Phi0 h φ) (sa11_J_coe φ)
      (sa11_Phi0_spec h φ)] with ζ hζ
    rw [show sa11_dual (Z' ζ) (sa11_J (m := m) (p := p) φ) = (Z' ζ).eval (sa11_J φ) from rfl, hζ, hAN, one_mul]
    show _ = (sa11_precomp (sa11_Top h) (sa11_dual (ηW ζ))) (sa11_J (m := m) (p := p) φ)
    rw [sa11_precomp_apply, sa11_Top_apply]
    rfl
  have hlawΞ : law (R N).P Ξ' = law (R N).P Ξo := Measure.map_congr hΞae
  have hlawZ : law (R N).P Z' = law (R N).P Zo := Measure.map_congr hZae
  rw [hlawΞ, hlawZ]
  refine (HRS.wassersteinE_le_of_coupling (R N).P 1 le_rfl Ξo Zo hΞmeas.aemeasurable hZmeas.aemeasurable).trans ?_
  simp only [Real.rpow_one, div_one, ENNReal.rpow_one]
  -- the main estimate
  set KT : ℝ := max Kad 0 * sa11_cJ d m with hKT
  have hKT0 : 0 ≤ KT := mul_nonneg (le_max_right _ _) (sa11_cJ_nonneg d m)
  set Zint : (R N).Ω → ℝ≥0∞ := fun ζ => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
    (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) +
      oNΛ d S.s C₀ Λ N + c₂ * e N) with hZint
  have hL := sa11_L_enorm hd hm hΓ hS hN hinv hν hRg hA ht h hKc hcomm
  -- initial datum
  set Ψ0 : (R N).Ω → WmpSpace d m p →L[ℝ] ℝ := fun ζ =>
    sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X₀ ζ) (S.ρ N 0) hρ0 with hΨ0
  have hΨae : ∀ᵐ ζ ∂(R N).P, Ψ0 ζ = sa11_dual (Ξ0 ζ) := by
    refine sa11_ae_eq_of_repr (R N).P Ψ0 (fun ζ => sa11_dual (Ξ0 ζ)) fun φ => ?_
    filter_upwards [hΞ0 φ.1 φ.2 (sa11_J (m := m) (p := p) φ) (sa11_J_coe φ)] with ζ hζ
    rw [show sa11_dual (Ξ0 ζ) (sa11_J (m := m) (p := p) φ) = (Ξ0 ζ).eval (sa11_J φ) from rfl, hζ]
    show (sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X₀ ζ) (S.ρ N 0) hρ0) (sa11_J (m := m) (p := p) φ) = _
    rw [sa11_Xi_apply hd hm, ← HRS.Whole.pair_empirical (by omega : 0 < N), hσκ,
      ← hS.mean_field.datum N hN1]
  -- pointwise decomposition
  have hpt : ∀ᵐ ζ ∂(R N).P, ENNReal.ofReal ‖Ξo ζ - Zo ζ‖ ≤
      ENNReal.ofReal (S.sigma N / 2 * Kc) * Zint ζ + ENNReal.ofReal KT * ‖Ξ0 ζ - ηW ζ‖ₑ := by
    filter_upwards [hL, hΨae] with ζ hLζ hΨζ
    have hd1 := sa11_dual_decomp (sa11_Top h)
      (sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X (Real.toNNReal t) ζ) (S.ρ N t) hρt) (Ψ0 ζ)
      (sa11_dual (ηW ζ))
    have h2 : ‖sa11_Top h‖ ≤ KT := sa11_Top_norm h
    have h4 : ‖Ψ0 ζ - sa11_dual (ηW ζ)‖ = ‖Ξ0 ζ - ηW ζ‖ := by rw [hΨζ]; rfl
    have h5 : ‖Ξo ζ - Zo ζ‖ ≤ ‖(sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X (Real.toNNReal t) ζ) (S.ρ N t) hρt) -
          sa11_precomp (sa11_Top h) (Ψ0 ζ)‖ + KT * ‖Ξ0 ζ - ηW ζ‖ := by
      rw [h4] at hd1
      exact hd1.trans (add_le_add_right (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) _)
    rw [← ofReal_norm_eq_enorm] at hLζ ⊢
    calc ENNReal.ofReal ‖Ξo ζ - Zo ζ‖
        ≤ ENNReal.ofReal (‖(sa11_Xi (m := m) (p := p) (S.sigma N) ((R N).X (Real.toNNReal t) ζ) (S.ρ N t) hρt) -
          sa11_precomp (sa11_Top h) (Ψ0 ζ)‖ + KT * ‖Ξ0 ζ - ηW ζ‖) := ENNReal.ofReal_le_ofReal h5
      _ ≤ _ := by
          refine ENNReal.ofReal_add_le.trans ?_
          rw [ENNReal.ofReal_mul hKT0]
          exact add_le_add hLζ le_rfl
  -- measurability of the energy integral
  have hZm : Measurable Zint := by
    have hGm : Measurable fun q : ℝ × (R N).Ω =>
        rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T q.1)) q.2)
          (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T q.1))) + oNΛ d S.s C₀ Λ N + c₂ * e N :=
      ((HRS.MP.RdRem.mrr_energy_meas hS hN1).comp (measurable_fst.prodMk hXm)).add measurable_const
    have := sa11_lintegral_meas S.T (fun (r : ℝ) (ζ : (R N).Ω) =>
      rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T r)) ζ)
        (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T r))) + oNΛ d S.s C₀ Λ N + c₂ * e N) hGm
    convert this using 1
    funext ζ
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    simp only [HRS.MP.RdRem.mrrClamp_of_mem hr]
  have hmom := sa11_energy_moment hS hN1 hc₂ he hXm
  have hBint : ∫⁻ ζ, ENNReal.ofReal (S.sigma N / 2 * Kc) * Zint ζ ∂(R N).P ≤
      ENNReal.ofReal (S.sigma N / 2 * Kc) * (ENNReal.ofReal S.T * ENNReal.ofReal (𝔈 N + c₂ * e N)) := by
    rw [lintegral_const_mul _ hZm]
    exact mul_le_mul_of_nonneg_left hmom bot_le
  have hfin := sa11_integral_bound (R N).P (fun ζ => ‖Ξo ζ - Zo ζ‖)
    (fun ζ => ENNReal.ofReal (S.sigma N / 2 * Kc) * Zint ζ) (fun ζ => ‖Ξ0 ζ - ηW ζ‖ₑ) KT
    (ENNReal.ofReal (S.sigma N / 2 * Kc) * (ENNReal.ofReal S.T * ENNReal.ofReal (𝔈 N + c₂ * e N))) εfX
    (hZm.const_mul _) hpt hBint hbd
  refine hfin.trans (le_of_eq ?_)
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
  have hce : 0 ≤ c₂ * e N := mul_nonneg hc₂ (he N)
  have hs2 : 0 ≤ S.sigma N / 2 := by positivity
  rw [← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_mul (mul_nonneg hs2 hKc), ← ENNReal.ofReal_mul hKT0,
    ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hs2 hKc) (mul_nonneg hT (add_nonneg h𝔈 hce)))
      (mul_nonneg hKT0 hε)]
  congr 1
  ring

end MainN

end HRS.MS.ZeroTemp
