import HRS.Energy.Commutator.RenormStjEnergy

/-!
# Route S, packet STJ: Fubini for the modulated energy (`F_N = c ∫ l^{-β} F_l dl`)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.Stj

open HRS.Commutator.Renorm

/-- copy of `SliceAux.offDiag_stieltjes` that also returns the integrability of the slice integrand -/
theorem offDiag_stieltjes_int {d N : ℕ} {β c : ℝ} (kS : ℝ → Torus d → Torus d → ℝ)
    (kI : Torus d → Torus d → ℝ) (X : Config d N) (μ : Measure (Torus d)) [SFinite μ]
    (hmeas : Measurable fun p : ℝ × (Torus d × Torus d) => kS p.1 p.2.1 p.2.2)
    (h1 : ∀ x y, IntegrableOn (fun l => l ^ (-β) * kS l x y) (Ioi 0))
    (h1' : ∀ x y, kI x y = c * ∫ l in Ioi (0 : ℝ), l ^ (-β) * kS l x y)
    (Θ : Torus d → ℝ)
    (h2 : ∀ x y, ∫ l in Ioi (0 : ℝ), ‖l ^ (-β) * kS l x y‖ ≤ Θ (x - y))
    (hΘ1 : ∀ x, Integrable (fun y => Θ (x - y)) μ)
    (hΘ2 : Integrable (fun p : Torus d × Torus d => Θ (p.1 - p.2)) (μ.prod μ)) :
    (offDiagPairing kI X μ = c * ∫ l in Ioi (0 : ℝ), l ^ (-β) * offDiagPairing (kS l) X μ) ∧
    Integrable (fun l : ℝ => l ^ (-β) * offDiagPairing (kS l) X μ) (volume.restrict (Ioi (0 : ℝ))) := by
  set ν₀ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hν₀
  -- the B-terms
  have hB : ∀ x0 : Torus d,
      Integrable (fun l => l ^ (-β) * ∫ y, kS l x0 y ∂μ) ν₀ ∧
      ∫ y, kI x0 y ∂μ = c * ∫ l in Ioi (0 : ℝ), l ^ (-β) * ∫ y, kS l x0 y ∂μ := by
    intro x0
    have hm : Measurable fun p : ℝ × Torus d => p.1 ^ (-β) * kS p.1 x0 p.2 := by
      have h := hmeas.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd) :
        Measurable fun p : ℝ × Torus d => (p.1, (x0, p.2)))
      exact (measurable_fst.pow_const _).mul h
    obtain ⟨-, hb, -, -, hd⟩ := SliceAux.fub_gen μ (fun l y => l ^ (-β) * kS l x0 y) hm (fun y => h1 x0 y)
      (fun y => Θ (x0 - y)) (hΘ1 x0) (fun y => h2 x0 y)
    have e1 : ∀ l, ∫ y, l ^ (-β) * kS l x0 y ∂μ = l ^ (-β) * ∫ y, kS l x0 y ∂μ := fun l => integral_const_mul _ _
    simp only [e1] at hb hd
    refine ⟨hb, ?_⟩
    rw [← hd, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => h1' x0 y)
  -- the C-term
  have hC : Integrable (fun l => l ^ (-β) * ∫ x, ∫ y, kS l x y ∂μ ∂μ) ν₀ ∧
      ∫ x, ∫ y, kI x y ∂μ ∂μ = c * ∫ l in Ioi (0 : ℝ), l ^ (-β) * ∫ x, ∫ y, kS l x y ∂μ ∂μ := by
    have hm : Measurable fun p : ℝ × (Torus d × Torus d) => p.1 ^ (-β) * kS p.1 p.2.1 p.2.2 :=
      (measurable_fst.pow_const _).mul hmeas
    obtain ⟨-, hb, hc, hr, hd⟩ := SliceAux.fub_gen (μ.prod μ) (fun l p => l ^ (-β) * kS l p.1 p.2) hm
      (fun p => h1 p.1 p.2) (fun p => Θ (p.1 - p.2)) hΘ2 (fun p => h2 p.1 p.2)
    have e2 : ∀ᵐ l ∂ν₀, ∫ p, l ^ (-β) * kS l p.1 p.2 ∂(μ.prod μ) = l ^ (-β) * ∫ x, ∫ y, kS l x y ∂μ ∂μ := by
      filter_upwards [hc] with l hl
      rw [integral_prod _ hl]
      simp only [integral_const_mul]
    refine ⟨hb.congr e2, ?_⟩
    have e3 : ∫ x, ∫ y, kI x y ∂μ ∂μ = ∫ p, kI p.1 p.2 ∂(μ.prod μ) := by
      refine (integral_prod (fun p : Torus d × Torus d => kI p.1 p.2) ?_).symm
      have := hr.const_mul c
      exact this.congr (Filter.Eventually.of_forall fun p => (h1' p.1 p.2).symm)
    have e4 : ∫ p, kI p.1 p.2 ∂(μ.prod μ) =
        c * ∫ p, (∫ l in Ioi (0 : ℝ), l ^ (-β) * kS l p.1 p.2) ∂(μ.prod μ) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => h1' p.1 p.2)
    rw [e3, e4, hd]
    congr 1
    exact integral_congr_ae e2
  -- the A-terms
  have hA : Integrable (fun l => l ^ (-β) * ∑ i, ∑ j ∈ Finset.univ.erase i, kS l (X i) (X j)) ν₀ ∧
      ∑ i, ∑ j ∈ Finset.univ.erase i, kI (X i) (X j) =
        c * ∫ l in Ioi (0 : ℝ), l ^ (-β) * ∑ i, ∑ j ∈ Finset.univ.erase i, kS l (X i) (X j) := by
    have hint : ∀ i j, Integrable (fun l => l ^ (-β) * kS l (X i) (X j)) ν₀ := fun i j => h1 (X i) (X j)
    have e : ∀ l, l ^ (-β) * ∑ i, ∑ j ∈ Finset.univ.erase i, kS l (X i) (X j) =
        ∑ i, ∑ j ∈ Finset.univ.erase i, l ^ (-β) * kS l (X i) (X j) := by
      intro l
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    simp only [e]
    refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j, ?_⟩
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hint i j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact h1' (X i) (X j)
  -- the B-sum
  have hBs : Integrable (fun l => l ^ (-β) * ∑ i, ∫ y, kS l (X i) y ∂μ) ν₀ ∧
      ∑ i, ∫ y, kI (X i) y ∂μ = c * ∫ l in Ioi (0 : ℝ), l ^ (-β) * ∑ i, ∫ y, kS l (X i) y ∂μ := by
    have e : ∀ l, l ^ (-β) * ∑ i, ∫ y, kS l (X i) y ∂μ = ∑ i, l ^ (-β) * ∫ y, kS l (X i) y ∂μ := fun l => by
      rw [Finset.mul_sum]
    simp only [e]
    refine ⟨integrable_finsetSum _ fun i _ => (hB (X i)).1, ?_⟩
    rw [integral_finsetSum _ fun i _ => (hB (X i)).1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (hB (X i)).2
  -- assemble
  unfold offDiagPairing
  have eA := hA.2
  have eB := hBs.2
  have eC := hC.2
  have key : ∀ l, l ^ (-β) * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, kS l (X i) (X j)
      - (2 / (N : ℝ)) * ∑ i, ∫ y, kS l (X i) y ∂μ + ∫ x, ∫ y, kS l x y ∂μ ∂μ) =
      (1 / (N : ℝ) ^ 2) * (l ^ (-β) * ∑ i, ∑ j ∈ Finset.univ.erase i, kS l (X i) (X j))
      - (2 / (N : ℝ)) * (l ^ (-β) * ∑ i, ∫ y, kS l (X i) y ∂μ) + l ^ (-β) * ∫ x, ∫ y, kS l x y ∂μ ∂μ := by
    intro l; ring
  simp only [key]
  have i1 : Integrable (fun l : ℝ => 1 / (N : ℝ) ^ 2 *
      (l ^ (-β) * ∑ i, ∑ j ∈ Finset.univ.erase i, kS l (X i) (X j))) ν₀ := hA.1.const_mul _
  have i2 : Integrable (fun l : ℝ => 2 / (N : ℝ) *
      (l ^ (-β) * ∑ i, ∫ y, kS l (X i) y ∂μ)) ν₀ := hBs.1.const_mul _
  have i12 : Integrable (fun l : ℝ => 1 / (N : ℝ) ^ 2 *
      (l ^ (-β) * ∑ i, ∑ j ∈ Finset.univ.erase i, kS l (X i) (X j)) -
      2 / (N : ℝ) * (l ^ (-β) * ∑ i, ∫ y, kS l (X i) y ∂μ)) ν₀ := i1.sub i2
  refine ⟨?_, i12.add hC.1⟩
  rw [integral_add i12 hC.1, integral_sub i1 i2, integral_const_mul, integral_const_mul]
  rw [eA, eB, eC]
  ring


theorem modulatedEnergy_eq_half {d N : ℕ} (h : Torus d → Torus d → ℝ) (X : Config d N) (μ : Measure (Torus d)) :
    modulatedEnergy h X μ = (1 / 2) * offDiagPairing h X μ := by
  unfold modulatedEnergy offDiagPairing
  ring

theorem offDiag_congr_ae {d N : ℕ} (k1 k2 : Torus d → Torus d → ℝ) (X : Config d N) (μ : Measure (Torus d))
    (hX : ∀ i j, i ≠ j → X i ≠ X j) (hμ0 : ∀ x, μ {x} = 0)
    (h : ∀ x y, x ≠ y → k1 x y = k2 x y) :
    offDiagPairing k1 X μ = offDiagPairing k2 X μ := by
  have hin : ∀ x, ∫ y, k1 x y ∂μ = ∫ y, k2 x y ∂μ := by
    intro x
    refine integral_congr_ae ?_
    have : ∀ᵐ y ∂μ, y ≠ x := by rw [ae_iff]; simpa using hμ0 x
    filter_upwards [this] with y hy
    exact h x y hy.symm
  unfold offDiagPairing
  have e1 : ∀ i, ∀ j ∈ Finset.univ.erase i, k1 (X i) (X j) = k2 (X i) (X j) := fun i j hj =>
    h _ _ (hX i j (Finset.ne_of_mem_erase hj).symm)
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl (e1 i)]
  simp_rw [hin]

theorem riesz_energy_fubini {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d)
    {c : ℝ}
    (hker : ∀ x : Torus d, x ≠ 0 →
      periodicRiesz d s x = c * ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * sliceG d l x)
    {Θ : Torus d → ℝ} (hΘm : Measurable Θ) (hΘi : Integrable Θ) (hΘ0 : ∀ z, 0 ≤ Θ z)
    (hΘ : ∀ z : Torus d, z ≠ 0 → ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * |sliceG d l z| ≤ Θ z)
    {N : ℕ} (X : Config d N) (hX : ∀ i j, i ≠ j → X i ≠ X j) {ρ : Torus d → ℝ} {Λ : ℝ}
    (hΛ : ∀ x, ρ x ≤ Λ) (hΛ0 : 0 ≤ Λ) :
    rieszEnergy d s X (withDensityReal ρ) =
        c * ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * modulatedEnergyKernel (sliceG d l) X (withDensityReal ρ) ∧
    Integrable (fun l : ℝ => l ^ (-bexp d s) * modulatedEnergyKernel (sliceG d l) X (withDensityReal ρ))
      (volume.restrict (Ioi (0 : ℝ))) := by
  set μ := withDensityReal ρ with hμdef
  haveI : SFinite μ := by rw [hμdef]; unfold withDensityReal; infer_instance
  have hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) := withDensityReal_le_smul' hΛ
  have hμ0 : ∀ x, μ {x} = 0 := atomless_of_le_vol hd ENNReal.ofReal_ne_top hμ
  set kS : ℝ → Torus d → Torus d → ℝ := fun l x y => if x = y then 0 else sliceG d l (x - y) with hkS
  set kI : Torus d → Torus d → ℝ := fun x y => if x = y then 0 else periodicRiesz d s (x - y) with hkI
  have hmeas : Measurable fun p : ℝ × (Torus d × Torus d) => kS p.1 p.2.1 p.2.2 := by
    simp only [hkS]
    refine Measurable.ite (measurableSet_eq_fun measurable_snd.fst measurable_snd.snd) measurable_const ?_
    exact (measurable_sliceG_uncurry d).comp (measurable_fst.prodMk (measurable_snd.fst.sub measurable_snd.snd))
  have h1 : ∀ x y, IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * kS l x y) (Ioi 0) := by
    intro x y
    by_cases hxy : x = y
    · simp only [hkS, if_pos hxy, mul_zero]; exact integrableOn_zero
    · simp only [hkS, if_neg hxy]
      exact sliceG_stieltjes_int hd hs0 hs hsd (sub_ne_zero.mpr hxy)
  have h1' : ∀ x y, kI x y = c * ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * kS l x y := by
    intro x y
    by_cases hxy : x = y
    · simp [hkI, hkS, hxy]
    · simp only [hkI, hkS, if_neg hxy]
      exact hker _ (sub_ne_zero.mpr hxy)
  have h2 : ∀ x y, ∫ l in Ioi (0 : ℝ), ‖l ^ (-bexp d s) * kS l x y‖ ≤ Θ (x - y) := by
    intro x y
    by_cases hxy : x = y
    · simp only [hkS, if_pos hxy, mul_zero, norm_zero, integral_zero]
      exact hΘ0 _
    · simp only [hkS, if_neg hxy]
      have hz := sub_ne_zero.mpr hxy
      refine le_trans (le_of_eq ?_) (hΘ _ hz)
      refine setIntegral_congr_fun measurableSet_Ioi fun l hl => ?_
      have hl' : (0 : ℝ) < l := hl
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hl' _)]
  have hΘ1 : ∀ x, Integrable (fun y => Θ (x - y)) μ := fun x =>
    CoercAux.integrable_conv_density hΛ hΘm hΘi x
  have hΘ2 := SliceAux.integrable_conv_prod hΛ hΘm hΘi
  obtain ⟨hEq, hInt⟩ := offDiag_stieltjes_int (β := bexp d s) (c := c) kS kI X μ hmeas h1 h1' Θ h2 hΘ1 hΘ2
  have hS : ∀ l : ℝ, offDiagPairing (kS l) X μ = 2 * modulatedEnergyKernel (sliceG d l) X μ := by
    intro l
    have := offDiag_congr_ae (kS l) (fun x y => sliceG d l (x - y)) X μ hX hμ0
      (fun x y hxy => by simp only [hkS, if_neg hxy])
    rw [this]
    unfold modulatedEnergyKernel
    rw [modulatedEnergy_eq_half]; ring
  have hI : offDiagPairing kI X μ = 2 * rieszEnergy d s X μ := by
    have := offDiag_congr_ae kI (fun x y => periodicRiesz d s (x - y)) X μ hX hμ0
      (fun x y hxy => by simp only [hkI, if_neg hxy])
    rw [this]
    unfold rieszEnergy modulatedEnergyKernel
    rw [modulatedEnergy_eq_half]; ring
  simp_rw [hS] at hEq hInt
  rw [hI] at hEq
  refine ⟨?_, ?_⟩
  · have e : ∀ l : ℝ, l ^ (-bexp d s) * (2 * modulatedEnergyKernel (sliceG d l) X μ) =
        2 * (l ^ (-bexp d s) * modulatedEnergyKernel (sliceG d l) X μ) := fun l => by ring
    simp_rw [e] at hEq
    rw [integral_const_mul] at hEq
    linarith
  · have e : ∀ l : ℝ, l ^ (-bexp d s) * (2 * modulatedEnergyKernel (sliceG d l) X μ) =
        2 * (l ^ (-bexp d s) * modulatedEnergyKernel (sliceG d l) X μ) := fun l => by ring
    simp_rw [e] at hInt
    exact (hInt.const_mul (1 / 2)).congr (Filter.Eventually.of_forall fun l => by simp only []; ring)

end HRS.Commutator.Stj
