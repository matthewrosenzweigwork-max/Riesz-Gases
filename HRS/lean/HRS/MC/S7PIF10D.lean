import HRS.MC.S7PIF10C

/-!
# Packet piF10, part D: measurability and integrability of `A(ω) = ∫_{(0,T]} cylA_r(ω) dr`

* `S7PIF10_cylA_bound`: `|cylA ω r| ≤ C ‖ℬ_N^r(ω)‖` for `r > 0` (bounded `∂_iF` and `|ℬ(U^{r,t_i}φ_i)| ≤ C_i ‖ℬ‖`, `F5A`);
* `S7PIF10_A_aesm`: `A` is a.e. strongly measurable.  A.s. and for `r ∈ (0,T]`, `cylA ω r` is the Borel function
  `∑_i D_i(r, Z_r(ω)) · (-√N · b^i_r(ω))` of `(ω, r)`, where `Z` is the progressive Itô process of `F5` equal to the observation
  vector of the predicted continuation, `b` the progressive drift of `F5`, and `D_i` the jointly continuous (`H3`) partial derivative;
* `S7PIF10_A_int`: `A` is integrable (`M1`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF10

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3 HRS.MC.Sec7.S7PIF5

variable {d : ℕ}

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

/-- the drift density is bounded by the `E_m` norm of `ℬ_N^r` -/
theorem S7PIF10_cylA_bound {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i))
    (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 1 G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ω : Ω) (r : ℝ), 0 < r →
      |cylA R m T P X t φ G ω r| ≤
        C * ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X r ω‖ := by
  classical
  have hg : ∀ i : Fin q, ∃ C : ℝ, 0 ≤ C ∧ ∀ r (F : NegSobolev d m), 0 < r →
      |S7PIF5_g R.D R.ρ t φ i (r, F)| ≤ C * ‖F‖ :=
    fun i => S7PIF5_g_bound R m hm T hT N hN P X₀ W X hreal t φ ht hφ i
  choose Cg hCg0 hCg using hg
  set B : ℝ := ⨆ z, ‖iteratedFDeriv ℝ 1 G z‖ with hB
  have hB0 : 0 ≤ B := Real.iSup_nonneg fun z => norm_nonneg _
  refine ⟨∑ i, B * Cg i, Finset.sum_nonneg fun i _ => mul_nonneg hB0 (hCg0 i), fun ω r hr => ?_⟩
  unfold cylA
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have h1 := S7PIF10_fderiv_bound (obsCov R.D R.ρ t φ) hG r
    (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) r)) i
  have h2 := hCg i r (quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X r ω) hr
  rw [S7PIF5_g_pos _ _ _ _ _ hr.le] at h2
  calc _ ≤ B * (Cg i * ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X r ω‖) :=
        mul_le_mul h1 h2 (abs_nonneg _) hB0
    _ = _ := by ring

end Prob

/-- the jointly continuous tag coefficient (time clamped to `[0,T]`) -/
def S7PIF10_Dc {q : ℕ} (T : ℝ) (S : ℝ → Matrix (Fin q) (Fin q) ℝ) (G : EuclideanSpace ℝ (Fin q) → ℝ)
    (i : Fin q) (p : ℝ × EuclideanSpace ℝ (Fin q)) : ℝ :=
  iteratedFDeriv ℝ 1 (gaussHeat S G (max 0 (min p.1 T))) p.2 (fun _ => EuclideanSpace.single i 1)

/-- the integrand of `A` is Borel in `(ω, r)` -/
theorem S7PIF10_At_meas {q : ℕ} (T : ℝ) (N : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (Dc : Fin q → ℝ × EuclideanSpace ℝ (Fin q) → ℝ) (hDc : ∀ i, Continuous (Dc i))
    (Z b : ℝ → Ω → EuclideanSpace ℝ (Fin q))
    (hZ : Measurable fun x : ℝ × Ω => Z (min x.1 T) x.2) (hb : Measurable fun x : ℝ × Ω => b (min x.1 T) x.2) :
    Measurable (fun p : Ω × ℝ => ∑ i, Dc i (p.2, Z (min p.2 T) p.1) * (-(Real.sqrt N) * b (min p.2 T) p.1 i)) := by
  refine Finset.measurable_sum _ (fun i _ => ?_)
  have h1 : Measurable (fun p : Ω × ℝ => (p.2, Z (min p.2 T) p.1)) :=
    measurable_snd.prodMk (hZ.comp (measurable_snd.prodMk measurable_fst))
  have h2 : Measurable (fun p : Ω × ℝ => b (min p.2 T) p.1 i) :=
    ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ).continuous.measurable.comp hb).comp
      (measurable_snd.prodMk measurable_fst)
  exact ((hDc i).measurable.comp h1).mul (h2.const_mul _)

section Prob2

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

/-- pointwise, the density is the Borel function -/
theorem S7PIF10_cylA_eq {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (G : EuclideanSpace ℝ (Fin q) → ℝ) (ω : Ω) {r : ℝ} (hr : r ∈ Set.Ioc 0 T)
    (Z : ℝ → Ω → EuclideanSpace ℝ (Fin q))
    (hZr : Z r ω = obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) r)) :
    cylA R m T P X t φ G ω r =
      ∑ i, S7PIF10_Dc T (obsCov R.D R.ρ t φ) G i (r, Z (min r T) ω) *
        (-(Real.sqrt N) * S7PIF5_b R m P X t φ (min r T) ω i) := by
  have hr' : min r T = r := min_eq_left hr.2
  have hcr : max 0 r = r := max_eq_right hr.1.le
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  rw [hr', hZr]
  unfold cylA
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hbi : S7PIF5_b R m P X t φ r ω i = -(Real.sqrt N)⁻¹ * NegSobolev.eval
      (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω) (obsTest R.D R.ρ t φ i r) := by
    show (if 0 ≤ r then -(Real.sqrt N)⁻¹ * NegSobolev.eval
      (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω) (obsTest R.D R.ρ t φ i r) else 0) = _
    rw [if_pos hr.1.le]
  have hD : S7PIF10_Dc T (obsCov R.D R.ρ t φ) G i
      (r, obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) r)) =
      fderiv ℝ (gaussHeat (obsCov R.D R.ρ t φ) G r)
        (obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) r)) (EuclideanSpace.single i 1) := by
    unfold S7PIF10_Dc
    rw [hr', hcr, iteratedFDeriv_one_apply]
  rw [hD, hbi]
  congr 1
  field_simp

/-- `A` is a.e. strongly measurable -/
theorem S7PIF10_A_aesm {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X)
    (γ : ℝ → Measure (PathSpace d m T))
    (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i))
    (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 4 G) :
    AEStronglyMeasurable (fun ω => ∫ r in Set.Ioc 0 T, cylA R m T P X t φ G ω r) P := by
  classical
  have law := HRS.MC.Sec7.S7PIS3.s7_PIS_obs_law_proof R m T hT γ hγ t φ ht hφ
  have hcov := HRS.MC.Sec7.S7PIS3.s7_PIS_cov_struct_proof' R T hT t φ ht hφ
  have hS : ∀ i j, ContinuousOn (fun u => obsCov R.D R.ρ t φ u i j) (Set.Icc 0 T) := hcov.2.2.2.2
  have hpsd : ∀ u ∈ Set.Icc (0 : ℝ) T, (obsCov R.D R.ρ t φ u).PosSemidef := fun u hu => (law u hu).1
  have H3 := HRS.MC.Sec7.S7PIS3.s7_PIH_heat_cont_proof T (obsCov R.D R.ρ t φ) hS hpsd G 4 hG 1 (by norm_num)
  have hclc : Continuous (fun τ : ℝ => max 0 (min τ T)) := continuous_const.max (continuous_id.min continuous_const)
  have hclm : ∀ τ : ℝ, max 0 (min τ T) ∈ Set.Icc (0 : ℝ) T :=
    fun τ => ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hDc : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin q) =>
      iteratedFDeriv ℝ 1 (gaussHeat (obsCov R.D R.ρ t φ) G (max 0 (min p.1 T))) p.2) :=
    H3.comp_continuous (f := fun p : ℝ × EuclideanSpace ℝ (Fin q) => (max 0 (min p.1 T), p.2))
      ((hclc.comp continuous_fst).prodMk continuous_snd) (fun p => ⟨hclm p.1, Set.mem_univ _⟩)
  have hDci : ∀ i : Fin q, Continuous (S7PIF10_Dc T (obsCov R.D R.ρ t φ) G i) :=
    fun i => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => EuclideanSpace ℝ (Fin q)) ℝ
      (fun _ => EuclideanSpace.single i 1)).continuous.comp hDc
  have hbprog : IsProgressive ℱ (S7PIF5_b R m P X t φ) :=
    S7PIF5_b_prog R m hm T hT N hN P X₀ W X hreal hF.progressive t φ ht hφ
  have hinit := S7PIF5_init_meas R m hm T hT N hN P X₀ W X hreal hF t φ ht hφ
  have hZ : IsProgressive ℱ (itoProcess P ℱ W' (fun ω => obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω)))
      (S7PIF5_b R m P X t φ) (S7PIF5_Phi R X t φ)) :=
    isProgressive_itoProcess (P := P) (W := W') _ hinit _ hbprog _
  have hid := S7PIF5_identity R m hm T hT N hN P X₀ W X hreal hF t φ ht hφ
  have hAtm := S7PIF10_At_meas T N (S7PIF10_Dc T (obsCov R.D R.ρ t φ) G) hDci _ _
    (measurable_progressive_min_gen hZ T) (measurable_progressive_min_gen hbprog T)
  have hA' := hAtm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioc 0 T))
  refine hA'.aestronglyMeasurable.congr ?_
  filter_upwards [hid] with ω hω
  refine setIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
  exact (S7PIF10_cylA_eq R m hm T hT N hN P X₀ W X hreal t φ G ω hr _ (hω r ⟨hr.1.le, hr.2⟩).symm).symm

/-- `A` is integrable -/
theorem S7PIF10_A_int {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X)
    (γ : ℝ → Measure (PathSpace d m T))
    (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i))
    (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 4 G) :
    Integrable (fun ω => ∫ r in Set.Ioc 0 T, cylA R m T P X t φ G ω r) P := by
  obtain ⟨C, hC0, hC⟩ := S7PIF10_cylA_bound R m hm T hT N hN P X₀ W X hreal t φ ht hφ G
    (S7PIF10_memCb_mono hG (by norm_num))
  have hM1 := HRS.MC.Sec7.S7PIM.s7_PIM_B_integrable_proof R m hm T hT N hN P X₀ W X hreal
  refine Integrable.mono' (hM1.2.2.const_mul C)
    (S7PIF10_A_aesm R m hm T hT N hN P X₀ W X hreal hF γ hγ t φ ht hφ G hG) ?_
  filter_upwards [hM1.1] with ω hω
  have hint : Integrable (fun u => quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := hω.integrable le_rfl
  have hint' : Integrable (fun r => C * ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X r ω‖)
      (volume.restrict (Set.Ioc (0 : ℝ) T)) :=
    (hint.norm.const_mul C).mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
  calc ‖∫ r in Set.Ioc 0 T, cylA R m T P X t φ G ω r‖
      ≤ ∫ r in Set.Ioc 0 T, C * ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X r ω‖ := by
        refine norm_integral_le_of_norm_le hint' ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun r hr => ?_)
        rw [Real.norm_eq_abs]
        exact hC ω r hr.1
    _ ≤ ∫ r in Set.Icc 0 T, C * ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X r ω‖ := by
        refine setIntegral_mono_set (hint.norm.const_mul C) ?_ (ae_of_all _ Set.Ioc_subset_Icc_self)
        exact Filter.Eventually.of_forall fun r => mul_nonneg hC0 (norm_nonneg _)
    _ = C * ∫ u in Set.Icc 0 T, ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω‖ :=
        integral_const_mul _ _

end Prob2

end HRS.MC.Sec7.S7PIF10

end
