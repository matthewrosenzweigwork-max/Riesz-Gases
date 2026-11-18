import HRS.ME.CritSpec
import HRS.ME.Asm417A
import HRS.MD.EQGaussLyapDet
import HRS.MD.EQRemBridge
import HRS.Sections.Q40bAux11
import HRS.PDE.MeanFieldPairSeries

/-!
# B1: `CritForcing` from `Uniform417`

The pointwise identification `statForcingCoord = - ⟨k⟩^m * integratedCenteredForcing` along a stationary Gibbs flow
(for every `ω`, every `t ∈ [0, H]`), then the sup/sum bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.CritForcingBridge

open HRS HRS.LZ HRS.MD.EQ29 HRS.MD.EQRem HRS.ME

variable {d : ℕ}

/-- `statRemainder φ = - forcingStat φ` at every configuration (the everywhere form of
`eq_statRemainder_eq_neg_forcing_proof`). -/
theorem cfb_statRemainder_eq_neg_forcingStat (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) {N : ℕ} (hN : 2 ≤ N)
    (φ : Torus d → ℝ) (hφ : Torus.IsCk 2 φ) (X : Config d N) :
    statRemainder d s V β ρβ (N := N) φ X = -forcingStat s V β ρβ φ X := by
  obtain ⟨hprob, hμm, hmm, ⟨B, hB⟩, hqint⟩ := eqrem_context hd hs0 hsd V hV hβ hρβ hN hφ
  obtain ⟨hρs, Λ, hΛ0, hΛ, hP⟩ := eqrem_setup hd hs0 hsd V hV hβ hρβ
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  set G := canonicalGibbs (periodicRiesz d s) V N β with hG
  set μ := withDensityReal ρβ with hμdef
  set m := firstMarginal G with hmdef
  set h := pairKernel d s φ with hh
  set ψ : Torus d → ℝ := fun x => kernelField h μ x - kernelField h m x with hψ
  have hψm : Measurable ψ := hμm.sub hmm
  have hψint : ∀ i : Fin N, Integrable (fun X : Config d N => ψ (X i)) G := fun i =>
    Integrable.of_bound (hψm.comp (measurable_pi_apply i)).aestronglyMeasurable B
      (ae_of_all _ fun X => by simpa using hB (X i))
  have hmi : ∀ i : Fin N, G.map (fun X : Config d N => X i) = m := by
    intro i
    have := eqrem_marginal_eq hN0 (periodicRiesz d s) (fun x => periodicRiesz_neg x) β μ i
    rw [← hP N] at this
    exact this
  have hA : ∫ X, (1 / (N : ℝ)) * ∑ i, ψ (X i) ∂G = ∫ x, ψ x ∂m := by
    rw [integral_const_mul, integral_finset_sum _ (fun i _ => hψint i)]
    have : ∀ i : Fin N, ∫ X, ψ (X i) ∂G = ∫ x, ψ x ∂m := fun i => by
      rw [← hmi i]
      exact (integral_map (measurable_pi_apply i).aemeasurable hψm.aestronglyMeasurable).symm
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hAint : Integrable (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, ψ (X i)) G :=
    (integrable_finset_sum _ fun i _ => hψint i).const_mul _
  set c0 : ℝ := (∫ x, ∫ y, h x y ∂μ ∂μ) - ∫ x, ∫ y, h x y ∂m ∂m with hc0
  have hE : ∀ X : Config d N, modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad φ)) X μ =
      (1 / 2) * (quadStat h m X - 2 * ((1 / (N : ℝ)) * ∑ i, ψ (X i)) + c0) := by
    intro X
    rw [show commKernel (periodicRieszGrad d s) (Torus.grad φ) = h from rfl,
      eqrem_modulatedEnergy_eq, eqrem_quadStat_split h μ m X]
  have hEint : ∫ X, modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad φ)) X μ ∂G =
      (1 / 2) * (∫ X, quadStat h m X ∂G - 2 * ∫ x, ψ x ∂m + c0) := by
    simp_rw [hE]
    have i2 : Integrable (fun X : Config d N => 2 * ((1 / (N : ℝ)) * ∑ i, ψ (X i))) G := hAint.const_mul 2
    have i1 : Integrable (fun X : Config d N => quadStat h m X - 2 * ((1 / (N : ℝ)) * ∑ i, ψ (X i))) G :=
      hqint.sub i2
    rw [integral_const_mul, integral_add i1 (integrable_const c0), integral_sub hqint i2,
      integral_const_mul, hA, integral_const]
    simp
  have e1 : ∫ x, (kernelField h μ x - kernelField h m x) ∂(empirical X) =
      (1 / (N : ℝ)) * ∑ i, ψ (X i) := by
    have := pair_empirical hN0 X ψ
    unfold pair at this
    rw [one_div]
    exact this
  have hmain : statRemainder d s V β ρβ (N := N) φ X =
    -(Real.sqrt N * (modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad φ)) X μ -
      ∫ ω', modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad φ)) ω' μ ∂G)) := by
    rw [hEint, hE X]
    unfold statRemainder
    rw [e1]
    ring
  rw [hmain]
  have hcomm : commKernel (periodicRieszGrad d s) (Torus.grad φ) = hTransport d s φ := by
    funext x y
    unfold commKernel hTransport
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [if_neg hxy]
  have hFun : ∀ Y : Config d N, modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad φ)) Y μ =
      (1 / 2 : ℝ) * quadStat (hTransport d s φ) μ Y := by
    intro Y
    rw [hcomm, eqrem_modulatedEnergy_eq]
  simp only [hFun, integral_const_mul]
  unfold forcingStat centeredUnder
  ring


/-- Both sides of the integrand identity at one time `r ∈ (0,t)`:
`𝓡_stat(U^{r,t} e_k)(X_r) = - ⟨k⟩^m 𝓡_N(S_{t-r}(⟨k⟩^{-m} e_k))(X_r)`. -/
theorem cfb_integrand_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (H : ℝ)
    (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ H X₀ W X) (m : ℝ) (k : NonzeroLattice d)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r < t) (htH : t ≤ H) (ω : Ω) :
    statRemainder d s V β ρβ (N := N)
        (propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) r t (Torus.realMode k))
        (X r.toNNReal ω) =
      -(Lattice.jp k.1 ^ m) *
        centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X
          (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (t - r)
            (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) r ω := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hprob : IsProbDensity ρβ := hρβ.1
  have hek : Torus.IsSmooth (Torus.realMode k) := HRS.FieldSingAux.isSmooth_realMode k
  set D := PDE.mfData d s hs0 hsd V β hβ with hD
  set φ := propagator D (fun _ => ρβ) r t (Torus.realMode k) with hφdef
  have hφs : Torus.IsSmooth φ :=
    HRS.MD.EQGaussLyapDet.eqgld_prop_smooth hd1 hs0 hsd V hV hβ ρβ hprob hρS hρpos _ hek r t hr hrt.le
  have hφ2 : Torus.IsCk 2 φ := PDE.MFSemigroup.isCk_nat_of_isSmooth hφs 2
  -- homogeneity
  have hhom : φ = propagator D (fun _ => ρβ) 0 (t - r) (Torus.realMode k) :=
    HRS.MD.EQGaussLyapDet.eqgld_homog hd1 hs0 hsd V hV hβ ρβ hprob hρS hρpos _ hek hr hrt
  obtain ⟨hpos, hsm, c₀, Λ₀, ⟨Hz⟩⟩ := HRS.MD.EQGaussLyapDet.eqgld_frozen hd hs0 hsd V hV hβ ρβ hρβ
  have hsmul : PDE.equilibriumSemigroup D ρβ (t - r) (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x) =
      fun y => Lattice.jp k.1 ^ (-m) * PDE.equilibriumSemigroup D ρβ (t - r) (Torus.realMode k) y :=
    PDE.MFPair.S_smul_ps hd1 Hz (PDE.MFSemigroup.isCk_nat_of_isSmooth hek (PDE.mStar d + 4))
      (Lattice.jp k.1 ^ (-m)) (by linarith)
  have hgrad : Torus.grad (PDE.equilibriumSemigroup D ρβ (t - r) (Torus.realMode k)) = Torus.grad φ := by
    funext x
    rw [hhom]
    unfold PDE.equilibriumSemigroup projMean
    exact PDE.MFLinear.grad_sub_const _ _ x
  have hccf : centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X
        (PDE.equilibriumSemigroup D ρβ (t - r) (Torus.realMode k)) r ω =
      centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X φ r ω := by
    unfold centeredCommutatorForcing
    rw [hgrad]
  have hjp : 0 < Lattice.jp k.1 := Torus.jp_pos _
  have hcne : Lattice.jp k.1 ^ (-m) ≠ 0 := (Real.rpow_pos_of_pos hjp _).ne'
  have hcs : centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X
      (fun y => Lattice.jp k.1 ^ (-m) * PDE.equilibriumSemigroup D ρβ (t - r) (Torus.realMode k) y) r ω =
      Lattice.jp k.1 ^ (-m) * centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X
        (PDE.equilibriumSemigroup D ρβ (t - r) (Torus.realMode k)) r ω :=
    Q40b.q40b_ccf_smul D hcne P (fun _ => withDensityReal ρβ) X _ r ω
  rw [hsmul, hcs, hccf,
    forcing_eq_forcingStat_proof hd hs0 hsd V hV β hβ ρβ hN P X₀ W X H hflow φ hφs r hr
      (by linarith) ω,
    cfb_statRemainder_eq_neg_forcingStat hd hs0 hsd V hV β hβ ρβ hρβ hN φ hφ2]
  rw [Real.rpow_neg hjp.le]
  field_simp


/-- The `k`-th coordinate of the integrated stationary remainder is `- ⟨k⟩^m` times the integrated centered forcing,
for every `ω` and every `t ∈ [0, H]`. -/
theorem cfb_coord_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (H : ℝ)
    (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ H X₀ W X) (m : ℝ) (k : NonzeroLattice d)
    {t : ℝ} (ht0 : 0 ≤ t) (htH : t ≤ H) (ω : Ω) :
    statForcingCoord d hs0 hsd V hβ ρβ X k t ω =
      -(Lattice.jp k.1 ^ m) *
        integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m k t ω := by
  unfold statForcingCoord integratedCenteredForcing
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ ({t} : Set ℝ) :=
    (Set.countable_singleton t).ae_notMem volume
  filter_upwards [hne] with r hrt hr
  rw [Set.uIoc_of_le ht0] at hr
  have hrt' : r < t := lt_of_le_of_ne hr.2 (by simpa using hrt)
  exact cfb_integrand_eq hd hs0 hsd V hV β hβ ρβ hρβ hρS hρpos hN P X₀ W X H hflow m k hr.1.le hrt' htH ω

theorem cfb_sq_eq (m : ℝ) (k : NonzeroLattice d) (I : ℝ) :
    Lattice.jp k.1 ^ (-2 * m) * (-(Lattice.jp k.1 ^ m) * I) ^ 2 = I ^ 2 := by
  have hjp : 0 < Lattice.jp k.1 := Torus.jp_pos _
  have : Lattice.jp k.1 ^ (-2 * m) * (Lattice.jp k.1 ^ m * Lattice.jp k.1 ^ m) = 1 := by
    rw [← Real.rpow_add hjp, ← Real.rpow_add hjp]
    ring_nf
    simp
  calc Lattice.jp k.1 ^ (-2 * m) * (-(Lattice.jp k.1 ^ m) * I) ^ 2
      = (Lattice.jp k.1 ^ (-2 * m) * (Lattice.jp k.1 ^ m * Lattice.jp k.1 ^ m)) * I ^ 2 := by ring
    _ = I ^ 2 := by rw [this]; ring

theorem crit_forcing_of_uniform417_proof {d : ℕ} :
    type_of% (@HRS.ME.Crit.crit_forcing_of_uniform417 d) := by
  intro hd hs0 hsd V hV βm βp hβm hββ m T hT hu
  obtain ⟨C, hC0, hC⟩ := hu
  refine ⟨C, hC0, ?_⟩
  intro β hβ ρβ hρ N hN Ω _ P _ X₀ W X a ha hq hflow
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  obtain ⟨hpos, hsm⟩ := HRS.Q41.q41_thermal_regular hd hs0 hsd hβ0 hV hρ
  have hu' := hC β hβ ρβ hρ hsm hpos N hN P X₀ W X a ha hflow
  refine le_trans (lintegral_mono fun ω => ?_) hu'
  obtain ⟨q0, hq0⟩ := hq
  set Y : ℝ≥0∞ := ⨆ t ∈ ratTimes 0 T, ∑' k : NonzeroLattice d,
    ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k
      (a + t) ω ^ 2) with hY
  have hle : (⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ0 ρβ X k t ω)) ^
      (1 / 2 : ℝ)) ≤ Y ^ (1 / 2 : ℝ) := by
    refine iSup₂_le fun t ht => ?_
    obtain ⟨⟨hta, htb⟩, q, hq'⟩ := ht
    have ht' : t - a ∈ ratTimes 0 T :=
      ⟨⟨by linarith, by linarith⟩, ⟨q - q0, by push_cast; rw [hq', hq0]⟩⟩
    have heq : coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ0 ρβ X k t ω) =
        ∑' k : NonzeroLattice d, ENNReal.ofReal (integratedCenteredForcing
          (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k (a + (t - a)) ω ^ 2) := by
      unfold coordEnergy
      refine tsum_congr fun k => ?_
      beta_reduce
      rw [add_sub_cancel, cfb_coord_eq hd hs0 hsd V hV β hβ0 ρβ hρ hsm hpos hN P X₀ W X (a + T) hflow m k
        (ha.trans hta) (by linarith) ω]
      rw [cfb_sq_eq]
    rw [heq]
    exact ENNReal.rpow_le_rpow (le_iSup₂ (f := fun t (_ : t ∈ ratTimes 0 T) => ∑' k : NonzeroLattice d,
      ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) ρβ P X m k
        (a + t) ω ^ 2)) (t - a) ht') (by norm_num)
  calc (⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ0 ρβ X k t ω)) ^
      (1 / 2 : ℝ)) ^ 2 ≤ (Y ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left' hle 2
    _ = Y := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num

end HRS.ME.CritForcingBridge

end
