import HRS.MS.ProClosureS111PhysicalFeatures

/-!
Summed Hermite bounds for the actual paired feature map. The direct-sum
geometry adds the initial and noise squared norms exactly. The increment
constant is finite on every finite horizon, including the time-zero
endpoint; it is used only for continuous-path existence.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1 HRS.MS.S111X2

variable {d : ℕ} {s a beta gamma : ℝ} {rho : Euc d → ℝ}
variable [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
variable {K : Lp ℝ 2 (HRS.Whole.withDensityReal rho) →L[ℝ] Lp ℝ 2 (HRS.Whole.withDensityReal rho)} {Mg : ℝ}
variable (hX : X1Input d s a beta 0 rho)
variable (hK : KRep (rieszKernel d s) (HRS.Whole.withDensityReal rho) K Mg)
variable (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)

theorem physicalLinear_norm_sq (i : Fin 2) {t : ℝ} (ht : 0 ≤ t)
    (phi : oscSub d (wholeSpaceIndex d)) :
    ‖physicalLinear hX hK hbeta hgamma i t phi‖ ^ 2 =
      (if i = 0 then
        ‖initialGaussianFeature hK hgamma (x1C d s a beta rho) t (phi : Euc d → ℝ)‖ ^ 2
      else ‖initialGaussianFeature hK hbeta (x1C d s a beta rho) t (phi : Euc d → ℝ)‖ ^ 2) +
        ‖scaledNoiseClass (x1C d s a beta rho) (HRS.Whole.withDensityReal rho) beta⁻¹ t
          (phi : Euc d → ℝ)‖ ^ 2 := by
  rw [physicalLinear_apply hX hK hbeta hgamma i ht]
  by_cases hi : i = 0 <;> simp only [hi, if_true, if_false,
    physicalFeatureTriple_norm_sq, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_add, add_zero]

theorem physicalLinear_sub_norm_sq (i : Fin 2) {t v : ℝ} (ht : 0 ≤ t) (hv : 0 ≤ v)
    (phi : oscSub d (wholeSpaceIndex d)) :
    ‖physicalLinear hX hK hbeta hgamma i t phi -
      physicalLinear hX hK hbeta hgamma i v phi‖ ^ 2 =
      (if i = 0 then
        ‖initialGaussianFeature hK hgamma (x1C d s a beta rho) t (phi : Euc d → ℝ) -
          initialGaussianFeature hK hgamma (x1C d s a beta rho) v (phi : Euc d → ℝ)‖ ^ 2
      else ‖initialGaussianFeature hK hbeta (x1C d s a beta rho) t (phi : Euc d → ℝ) -
        initialGaussianFeature hK hbeta (x1C d s a beta rho) v (phi : Euc d → ℝ)‖ ^ 2) +
        ‖scaledNoiseClass (x1C d s a beta rho) (HRS.Whole.withDensityReal rho) beta⁻¹ t
            (phi : Euc d → ℝ) -
          scaledNoiseClass (x1C d s a beta rho) (HRS.Whole.withDensityReal rho) beta⁻¹ v
            (phi : Euc d → ℝ)‖ ^ 2 := by
  rw [physicalLinear_apply hX hK hbeta hgamma i ht,
    physicalLinear_apply hX hK hbeta hgamma i hv]
  by_cases hi : i = 0 <;> simp only [hi, if_true, if_false,
    physicalFeatureTriple_sub, physicalFeatureTriple_norm_sq, sub_zero, zero_sub,
    sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, add_zero]

theorem physicalLinear_summed_bounds (hd : 2 ≤ d)
    (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hbeta' : 0 < beta)
    (hrho : IsThermalEquilibrium d s a beta rho) (H : ℝ) (hH : 0 ≤ H) :
    (∀ i : Fin 2, ∀ t ∈ Icc (0 : ℝ) H,
      Summable (fun alpha : MultiIndex d =>
        ‖physicalLinear hX hK hbeta hgamma i t
          (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2)) ∧
    ∃ L : ℝ, 0 ≤ L ∧ ∀ i : Fin 2, ∀ t v : ℝ,
      t ∈ Icc (0 : ℝ) H → v ∈ Icc (0 : ℝ) H →
      Summable (fun alpha : MultiIndex d =>
        ‖physicalLinear hX hK hbeta hgamma i t (initialTestBasis (wholeSpaceIndex d) alpha) -
          physicalLinear hX hK hbeta hgamma i v (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2) ∧
      (∑' alpha : MultiIndex d,
        ‖physicalLinear hX hK hbeta hgamma i t (initialTestBasis (wholeSpaceIndex d) alpha) -
          physicalLinear hX hK hbeta hgamma i v (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2)
        ≤ L * |t - v| := by
  have hsd : s < (d : ℝ) := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  let Ag := fun t (alpha : MultiIndex d) =>
    initialGaussianFeature hK hgamma (x1C d s a beta rho) t
      (initialTestBasis (wholeSpaceIndex d) alpha : Euc d → ℝ)
  let Ab := fun t (alpha : MultiIndex d) =>
    initialGaussianFeature hK hbeta (x1C d s a beta rho) t
      (initialTestBasis (wholeSpaceIndex d) alpha : Euc d → ℝ)
  let N := fun t (alpha : MultiIndex d) =>
    scaledNoiseClass (x1C d s a beta rho) (HRS.Whole.withDensityReal rho) beta⁻¹ t
      (initialTestBasis (wholeSpaceIndex d) alpha : Euc d → ℝ)
  have hg := physical_initial_gaussian_features_summable hd hs0 hsd ha hbeta'
    hgamma hrho hK H hH
  have hb := physical_initial_gaussian_features_summable hd hs0 hsd ha hbeta'
    hbeta hrho hK H hH
  have hn := physical_noise_features_summable hd hs0 hsd ha hbeta' hrho H hH
  change (∀ t ∈ Icc (0 : ℝ) H, Summable (fun alpha => ‖Ag t alpha‖ ^ 2)) ∧
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t v, t ∈ Icc (0 : ℝ) H → v ∈ Icc (0 : ℝ) H →
      Summable (fun alpha => ‖Ag t alpha - Ag v alpha‖ ^ 2) ∧
      (∑' alpha, ‖Ag t alpha - Ag v alpha‖ ^ 2) ≤ L * |t - v| at hg
  change (∀ t ∈ Icc (0 : ℝ) H, Summable (fun alpha => ‖Ab t alpha‖ ^ 2)) ∧
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t v, t ∈ Icc (0 : ℝ) H → v ∈ Icc (0 : ℝ) H →
      Summable (fun alpha => ‖Ab t alpha - Ab v alpha‖ ^ 2) ∧
      (∑' alpha, ‖Ab t alpha - Ab v alpha‖ ^ 2) ≤ L * |t - v| at hb
  change (∀ t ∈ Icc (0 : ℝ) H, Summable (fun alpha => ‖N t alpha‖ ^ 2)) ∧
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t v, t ∈ Icc (0 : ℝ) H → v ∈ Icc (0 : ℝ) H →
      Summable (fun alpha => ‖N t alpha - N v alpha‖ ^ 2) ∧
      (∑' alpha, ‖N t alpha - N v alpha‖ ^ 2) ≤ L * |t - v| at hn
  obtain ⟨hgmag, Lg, hLg, hginc⟩ := hg
  obtain ⟨hbmag, Lb, hLb, hbinc⟩ := hb
  obtain ⟨hnmag, Ln, hLn, hninc⟩ := hn
  refine ⟨?_, Lg + Lb + Ln, by positivity, ?_⟩
  · intro i t ht
    have he : ∀ alpha : MultiIndex d,
        ‖physicalLinear hX hK hbeta hgamma i t
          (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2 =
        (if i = 0 then ‖Ag t alpha‖ ^ 2 else ‖Ab t alpha‖ ^ 2) + ‖N t alpha‖ ^ 2 :=
      fun alpha => physicalLinear_norm_sq hX hK hbeta hgamma i ht.1 _
    simp_rw [he]
    by_cases hi : i = 0
    · simpa only [if_pos hi] using (hgmag t ht).add (hnmag t ht)
    · simpa only [if_neg hi] using (hbmag t ht).add (hnmag t ht)
  · intro i t v ht hv
    obtain ⟨hgs, hgb⟩ := hginc t v ht hv
    obtain ⟨hbs, hbb⟩ := hbinc t v ht hv
    obtain ⟨hns, hnb⟩ := hninc t v ht hv
    have he : ∀ alpha : MultiIndex d,
        ‖physicalLinear hX hK hbeta hgamma i t
            (initialTestBasis (wholeSpaceIndex d) alpha) -
          physicalLinear hX hK hbeta hgamma i v
            (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2 =
        (if i = 0 then ‖Ag t alpha - Ag v alpha‖ ^ 2
        else ‖Ab t alpha - Ab v alpha‖ ^ 2) + ‖N t alpha - N v alpha‖ ^ 2 :=
      fun alpha => physicalLinear_sub_norm_sq hX hK hbeta hgamma i ht.1 hv.1 _
    simp_rw [he]
    by_cases hi : i = 0
    · simp only [if_pos hi]
      refine ⟨hgs.add hns, ?_⟩
      rw [hgs.tsum_add hns]
      have hextra : 0 ≤ Lb * |t - v| := mul_nonneg hLb (abs_nonneg _)
      nlinarith
    · simp only [if_neg hi]
      refine ⟨hbs.add hns, ?_⟩
      rw [hbs.tsum_add hns]
      have hextra : 0 ≤ Lg * |t - v| := mul_nonneg hLg (abs_nonneg _)
      nlinarith

#print axioms physicalLinear_summed_bounds

end HRS.MS.ProClosureS111
