import HRS.MD.EQStrongBase
import HRS.MD.Stat
import HRS.MD.EQ29Vocab

/-!
# EQ-STRONG (flow clause): the stationary strong moment along the Gibbs flow

`E sup_{t ∈ [u,u+T]∩ℚ} ‖ζ_N^t‖²_{E_q} ≤ C` along a stationary Gibbs flow (TeX `P:eq:stationary-strong-moment`, L4122-4132), uniformly in
`β ∈ [β₋,β₊]`, the thermal density, `N ≥ 2` and the window start `u`.

Route: the Fourier coordinates `F_k = ⟨k⟩^{-q} √N μ_N(e_k)` form a family of Lyons-Zheng test functions (`EQStrongBase`);
`lyonsZheng_maximal_family` bounds `E sup_t ∑_k (F_k(X^t) - E F_k)²` by `C ∑_k Var F_k + C β⁻¹ T ∑_k E|∇F_k|²`; the variances are
`≤ 2 C₀ ⟨k⟩^{-2q}` (`eq_static_linear_proof`), the gradients `≤ 2 ⟨k⟩^{2-2q}`, both summable for `q > d/2 + 1`.  The centering `E_{P.map X^t} = E_μ`
is the stationarity of the Gibbs flow (`md_stat_gibbs_flow_stationary_proof`).

The Lyons-Zheng inequality is taken as the hypothesis `hLZ` (the type of `HRS.LZ.lyonsZheng_maximal_family`) in this file; it is supplied by the proved
`HRS.MD.EQLZFinal.lyonsZheng_maximal_family_proof` in `EQStrongFinal`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQStrong

open HRS.LZ HRS.MD.EQ29

variable {d : ℕ}

theorem eqstrong_fourierCoeff_zeta {N : ℕ} (hN : 1 ≤ N) {m : ℝ} (hm : (d : ℝ) < 2 * m)
    (P : Measure (Config d N)) [IsProbabilityMeasure P] (X : Config d N) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (zetaE m P X) k =
      Real.sqrt N * (pair (empirical X) (Torus.realMode k) -
        ∫ Y, pair (empirical Y) (Torus.realMode k) ∂P) := by
  unfold NegSobolev.fourierCoeff
  rw [HRS.MD.EQInit.eqinit_coord_zeta hN hm P X k]
  have hj : 0 < Lattice.jp k.1 := Torus.jp_pos _
  rw [Real.rpow_neg hj.le]
  field_simp

theorem eqstrong_var_le {N : ℕ} (hN : 2 ≤ N) (μ : Measure (Config d N)) [IsProbabilityMeasure μ]
    (w : ℝ) (f : Torus d → ℝ) (hfc : Continuous f) (B C₁ : ℝ) (hB : ∀ x, |f x| ≤ B)
    (hev : evariance (fun X : Config d N => pair (empirical X) f) μ ≤
      ENNReal.ofReal (C₁ * (N : ℝ)⁻¹)) :
    ENNReal.ofReal (∫ Y, (stF N w f Y - ∫ Y', stF N w f Y' ∂μ) ^ 2 ∂μ) ≤
      ENNReal.ofReal (w ^ 2 * C₁) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set a : Config d N → ℝ := fun X => pair (empirical X) f with ha
  have hac : Continuous a := by
    have : a = fun X : Config d N => (N : ℝ)⁻¹ * ∑ i, f (X i) := by
      funext X; exact pair_empirical (by omega) X f
    rw [this]
    exact continuous_const.mul (continuous_finset_sum _ fun i _ => hfc.comp (continuous_apply i))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary _))
  have habd : ∀ X, |a X| ≤ B := by
    intro X
    rw [ha]
    simp only
    rw [pair_empirical (by omega)]
    have : |∑ i, f (X i)| ≤ N * B := by
      calc |∑ i, f (X i)| ≤ ∑ i, |f (X i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ => hB _
        _ = N * B := by simp
    rw [abs_mul, abs_of_pos (inv_pos.2 hN0)]
    calc (N : ℝ)⁻¹ * |∑ i, f (X i)| ≤ (N : ℝ)⁻¹ * (N * B) := by gcongr
      _ = B := by field_simp
  have hmem : MemLp a 2 μ :=
    MemLp.of_bound hac.aestronglyMeasurable B (Filter.Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact habd X)
  have hst : ∀ X, stF N w f X = (w * Real.sqrt N) * a X := by
    intro X
    rw [stF_eq_pair (by omega)]
    simp only [ha]
    ring
  have hint : ∫ Y', stF N w f Y' ∂μ = (w * Real.sqrt N) * ∫ Y', a Y' ∂μ := by
    simp_rw [hst]
    rw [integral_const_mul]
  have hsq : ∀ Y, (stF N w f Y - ∫ Y', stF N w f Y' ∂μ) ^ 2 =
      (w ^ 2 * N) * (a Y - ∫ Y', a Y' ∂μ) ^ 2 := by
    intro Y
    rw [hint, hst]
    have : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
    calc _ = (w * Real.sqrt N) ^ 2 * (a Y - ∫ Y', a Y' ∂μ) ^ 2 := by ring
      _ = _ := by rw [mul_pow, this]
  simp_rw [hsq]
  rw [integral_const_mul]
  have hvar : variance a μ = ∫ Y, (a Y - ∫ Y', a Y' ∂μ) ^ 2 ∂μ := by
    exact variance_eq_integral hmem.aemeasurable
  rw [← hvar]
  have hv0 : 0 ≤ variance a μ := variance_nonneg _ _
  rw [ENNReal.ofReal_mul (by positivity)]
  have hev' : ENNReal.ofReal (variance a μ) = evariance a μ := hmem.ofReal_variance_eq
  rw [hev']
  calc ENNReal.ofReal (w ^ 2 * N) * evariance a μ
      ≤ ENNReal.ofReal (w ^ 2 * N) * ENNReal.ofReal (C₁ * (N : ℝ)⁻¹) := by gcongr
    _ = ENNReal.ofReal (w ^ 2 * C₁) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp


theorem eqstrong_zero_test {N : ℕ} (μ : Measure (Config d N)) [IsFiniteMeasure μ] :
    IsLZTest μ (fun _ : Config d N => (0 : ℝ)) := by
  refine ⟨measurable_const, MemLp.zero, ?_, ?_⟩
  · exact contDiffOn_const
  · rw [configGradSq_zero]; exact integrable_zero _ _ _

theorem eqstrong_jp_rpow_sq (k : NonzeroLattice d) (q : ℝ) :
    (Lattice.jp k.1 ^ (-q)) ^ 2 = Lattice.jp k.1 ^ (-(2 * q)) := by
  have hj : 0 < Lattice.jp k.1 := Torus.jp_pos _
  rw [← Real.rpow_natCast, ← Real.rpow_mul hj.le]
  congr 1
  push_cast
  ring

theorem eqstrong_jp_rpow_mul_sq (k : NonzeroLattice d) (q : ℝ) :
    Lattice.jp k.1 ^ (-(2 * q)) * Lattice.jp k.1 ^ 2 = Lattice.jp k.1 ^ (-(2 * (q - 1))) := by
  have hj : 0 < Lattice.jp k.1 := Torus.jp_pos _
  rw [← Real.rpow_natCast, ← Real.rpow_add hj]
  congr 1
  push_cast
  ring

/-- **Flow clause of `eq_strong_moment`**, from the Lyons-Zheng family inequality `hLZ`. -/
theorem eqstrong_flow_of_lz (hLZ : type_of% @HRS.LZ.lyonsZheng_maximal_family) (hd : 2 ≤ d) {s : ℝ}
    (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (m q : ℝ) (hq : (d : ℝ) / 2 + 1 < q) (hqm : q < m) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∀ u : ℝ, 0 ≤ u → ∀ N : ℕ, 2 ≤ N →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
          IsStationaryGibbsFlow P s hs0 hsd V β (hβm.trans_le hβ.1) (u + T) X₀ W X →
          ∫⁻ ω, ⨆ t ∈ ratTimes u T, coordEnergy q (fun k => NegSobolev.fourierCoeff
              (zetaE m (P.map (X t.toNNReal)) (X t.toNNReal ω)) k) ∂P ≤ ENNReal.ofReal C := by
  classical
  obtain ⟨CL, hCL, hLZ'⟩ := hLZ
  obtain ⟨C₀, hC₀, hC⟩ := HRS.MD.EQStat.eq_static_linear_proof hd hs0 hsd V hV βm βp hβm hββ
  obtain ⟨Lam, hLam⟩ := HRS.MD.EQStat.eqstat_thermal_setup hd hs0 hsd V hV βm βp hβm hββ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hq1 : (d : ℝ) < 2 * q := by linarith
  have hq2 : (d : ℝ) < 2 * (q - 1) := by linarith
  have hm2 : (d : ℝ) < 2 * m := by linarith
  have hS1 := summable_jp_rpow (d := d) q hq1
  have hS2 := summable_jp_rpow (d := d) (q - 1) hq2
  have hjp0 : ∀ (k : NonzeroLattice d) (e : ℝ), 0 ≤ Lattice.jp k.1 ^ e := fun k e =>
    Real.rpow_nonneg (Torus.jp_pos _).le _
  set S1 : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * q)) with hS1def
  set S2 : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (q - 1))) with hS2def
  have hS1nn : 0 ≤ S1 := tsum_nonneg fun k => hjp0 k _
  have hS2nn : 0 ≤ S2 := tsum_nonneg fun k => hjp0 k _
  refine ⟨CL * (2 * C₀ * S1 + βm⁻¹ * T * (2 * S2)) + 1, by positivity, ?_⟩
  intro β hβ ρβ hρ u hu N hN Ω _ P _ X₀ W X hflow
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  obtain ⟨hρs, hΛ, hPeq⟩ := hLam β hβ ρβ hρ
  haveI hμρ : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρs.density
  haveI hPr : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [hPeq N]
    exact HRS.Q32c.q32c_Q_isProb hd hs0 hsd hβ0 (Λ := max Lam 1) (le_max_right _ _) hρs.density
      (fun x => (hΛ x).trans (le_max_left _ _)) (by omega)
  set μ := canonicalGibbs (periodicRiesz d s) V N β with hμdef
  obtain ⟨ι, hι⟩ : ∃ ι : NonzeroLattice d → ℕ, Function.Injective ι := Countable.exists_injective_nat _
  set w : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-q) with hwdef
  set G : NonzeroLattice d → Config d N → ℝ := fun k => stF N (w k) (Torus.realMode k) with hGdef
  set F : ℕ → Config d N → ℝ := fun j => if h : ∃ k, ι k = j then G h.choose else fun _ => 0 with hFdef
  have hF_ι : ∀ k, F (ι k) = G k := by
    intro k
    have h : ∃ k', ι k' = ι k := ⟨k, rfl⟩
    simp only [hFdef, dif_pos h]
    congr 1
    exact hι h.choose_spec
  have hF_off : ∀ j, (¬ ∃ k, ι k = j) → F j = fun _ => 0 := fun j hj => by
    simp only [hFdef, dif_neg hj]
  have hFtest : ∀ j, IsLZTest μ (F j) := by
    intro j
    by_cases h : ∃ k, ι k = j
    · obtain ⟨k, rfl⟩ := h
      rw [hF_ι]; exact isLZTest_stF N hN0 (w k) k μ
    · rw [hF_off j h]; exact eqstrong_zero_test μ
  have key := hLZ' d N hd hN s hs0 hsd V hV β hβ0 T u hT hu P X₀ W X hflow F hFtest
  have hstat : ∀ t ∈ ratTimes u T, P.map (X t.toNNReal) = μ := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hu ht.1.1
    exact HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ0 (u + T) hN P X₀ W X
      hflow t.toNNReal (by rw [Real.coe_toNNReal t ht0]; exact ht.1.2)
  -- sums over the range of `ι`
  have hreindex : ∀ (S : ℕ → ℝ≥0∞), (∀ j, ¬ (∃ k, ι k = j) → S j = 0) →
      ∑' j, S j = ∑' k, S (ι k) := by
    intro S hS
    refine (hι.tsum_eq (f := S) ?_).symm
    intro j hj
    by_contra hnr
    exact hj (hS j fun ⟨k, hk⟩ => hnr ⟨k, hk⟩)
  -- the centered coordinates
  have hcenter : ∀ (k : NonzeroLattice d) (Y : Config d N),
      G k Y - ∫ Y', G k Y' ∂μ = w k * NegSobolev.fourierCoeff (zetaE m μ Y) k := by
    intro k Y
    have hG : ∀ Z, G k Z = w k * (Real.sqrt N * pair (empirical Z) (Torus.realMode k)) := fun Z =>
      stF_eq_pair hN0 _ _ Z
    have hGi : ∫ Y', G k Y' ∂μ =
        w k * (Real.sqrt N * ∫ Y', pair (empirical Y') (Torus.realMode k) ∂μ) := by
      simp_rw [hG]
      rw [integral_const_mul, integral_const_mul]
    rw [hGi, hG, eqstrong_fourierCoeff_zeta hN1 hm2 μ Y k]
    ring
  have hLHS : ∀ ω, (⨆ t ∈ ratTimes u T, coordEnergy q (fun k => NegSobolev.fourierCoeff
        (zetaE m (P.map (X t.toNNReal)) (X t.toNNReal ω)) k)) =
      ⨆ t ∈ ratTimes u T, ∑' j, ENNReal.ofReal ((F j (X t.toNNReal ω) - ∫ Y, F j Y ∂μ) ^ 2) := by
    intro ω
    refine iSup_congr fun t => iSup_congr fun ht => ?_
    rw [hstat t ht]
    rw [hreindex (fun j => ENNReal.ofReal ((F j (X t.toNNReal ω) - ∫ Y, F j Y ∂μ) ^ 2))
      (fun j hj => by rw [hF_off j hj]; simp)]
    unfold coordEnergy
    refine tsum_congr fun k => ?_
    simp only
    rw [hF_ι, hcenter, mul_pow, eqstrong_jp_rpow_sq]
    congr 1
    rw [show (-2 : ℝ) * q = -(2 * q) by ring]
  -- variance and gradient bounds, coordinatewise
  have hev : ∀ k : NonzeroLattice d, evariance (fun X : Config d N => pair (empirical X) (Torus.realMode k)) μ ≤
      ENNReal.ofReal (2 * C₀ * (N : ℝ)⁻¹) := by
    intro k
    set f : Torus d → ℝ := Torus.realMode k with hf
    have hfc : Continuous f := Torus.continuous_realMode k
    have hf2 : MemLp f 2 (withDensityReal ρβ) :=
      MemLp.of_bound hfc.aestronglyMeasurable (Real.sqrt 2)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact Torus.abs_realMode_le k x)
    have hint : ∫ x, f x ^ 2 ∂(withDensityReal ρβ) ≤ 2 := by
      have hb : ∀ x, f x ^ 2 ≤ 2 := fun x => by
        have := Torus.abs_realMode_le k x
        have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        nlinarith [abs_nonneg (f x), sq_abs (f x), Real.sqrt_nonneg 2]
      have := integral_mono hf2.integrable_sq (integrable_const (2 : ℝ)) hb
      simpa using this
    refine (hC β hβ ρβ hρ N hN f hfc.measurable hf2).trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ C₀ * (N : ℝ)⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hint this]
  have hVarK : ∀ k, ENNReal.ofReal (∫ Y, (F (ι k) Y - ∫ Y', F (ι k) Y' ∂μ) ^ 2 ∂μ) ≤
      ENNReal.ofReal (2 * C₀ * Lattice.jp k.1 ^ (-(2 * q))) := by
    intro k
    rw [hF_ι]
    refine (eqstrong_var_le hN μ (w k) (Torus.realMode k) (Torus.continuous_realMode k) (Real.sqrt 2)
      (2 * C₀) (fun x => Torus.abs_realMode_le k x) (hev k)).trans (le_of_eq ?_)
    congr 1
    rw [hwdef]
    simp only
    rw [eqstrong_jp_rpow_sq]
    ring
  have hGradK : ∀ k, ENNReal.ofReal (∫ Y, configGradSq (F (ι k)) Y ∂μ) ≤
      ENNReal.ofReal (2 * Lattice.jp k.1 ^ (-(2 * (q - 1)))) := by
    intro k
    rw [hF_ι]
    refine ENNReal.ofReal_le_ofReal ((integral_configGradSq_stF_le N hN0 (w k) k μ).trans (le_of_eq ?_))
    rw [hwdef]
    simp only
    rw [mul_assoc, eqstrong_jp_rpow_sq, eqstrong_jp_rpow_mul_sq]
  have hsumVar : ∑' j, ENNReal.ofReal (∫ Y, (F j Y - ∫ Y', F j Y' ∂μ) ^ 2 ∂μ) ≤
      ENNReal.ofReal (2 * C₀ * S1) := by
    rw [hreindex _ (fun j hj => by rw [hF_off j hj]; simp)]
    calc ∑' k, ENNReal.ofReal (∫ Y, (F (ι k) Y - ∫ Y', F (ι k) Y' ∂μ) ^ 2 ∂μ)
        ≤ ∑' k : NonzeroLattice d, ENNReal.ofReal (2 * C₀ * Lattice.jp k.1 ^ (-(2 * q))) :=
          ENNReal.tsum_le_tsum hVarK
      _ = ENNReal.ofReal (∑' k : NonzeroLattice d, 2 * C₀ * Lattice.jp k.1 ^ (-(2 * q))) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (by positivity) (hjp0 k _))
            (hS1.mul_left (2 * C₀))).symm
      _ = _ := by rw [tsum_mul_left]
  have hsumGrad : ∑' j, ENNReal.ofReal (∫ Y, configGradSq (F j) Y ∂μ) ≤ ENNReal.ofReal (2 * S2) := by
    rw [hreindex _ (fun j hj => by rw [hF_off j hj, configGradSq_zero]; simp)]
    calc ∑' k, ENNReal.ofReal (∫ Y, configGradSq (F (ι k)) Y ∂μ)
        ≤ ∑' k : NonzeroLattice d, ENNReal.ofReal (2 * Lattice.jp k.1 ^ (-(2 * (q - 1)))) :=
          ENNReal.tsum_le_tsum hGradK
      _ = ENNReal.ofReal (∑' k : NonzeroLattice d, 2 * Lattice.jp k.1 ^ (-(2 * (q - 1)))) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (by norm_num) (hjp0 k _))
            (hS2.mul_left 2)).symm
      _ = _ := by rw [tsum_mul_left]
  calc ∫⁻ ω, (⨆ t ∈ ratTimes u T, coordEnergy q (fun k => NegSobolev.fourierCoeff
        (zetaE m (P.map (X t.toNNReal)) (X t.toNNReal ω)) k)) ∂P
      = ∫⁻ ω, ⨆ t ∈ ratTimes u T, ∑' j, ENNReal.ofReal
          ((F j (X t.toNNReal ω) - ∫ Y, F j Y ∂μ) ^ 2) ∂P := lintegral_congr hLHS
    _ ≤ ENNReal.ofReal CL * (∑' j, ENNReal.ofReal (∫ Y, (F j Y - ∫ Y', F j Y' ∂μ) ^ 2 ∂μ) +
          ENNReal.ofReal (β⁻¹ * T) * ∑' j, ENNReal.ofReal (∫ Y, configGradSq (F j) Y ∂μ)) := key
    _ ≤ ENNReal.ofReal CL * (ENNReal.ofReal (2 * C₀ * S1) +
          ENNReal.ofReal (β⁻¹ * T) * ENNReal.ofReal (2 * S2)) := by gcongr
    _ = ENNReal.ofReal (CL * (2 * C₀ * S1 + β⁻¹ * T * (2 * S2))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul hCL.le]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hinv : β⁻¹ ≤ βm⁻¹ := inv_anti₀ hβm hβ.1
        have : β⁻¹ * T * (2 * S2) ≤ βm⁻¹ * T * (2 * S2) := by gcongr
        nlinarith [mul_le_mul_of_nonneg_left (add_le_add_left this (2 * C₀ * S1)) hCL.le]

end HRS.MD.EQStrong
