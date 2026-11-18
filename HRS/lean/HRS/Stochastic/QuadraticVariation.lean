import HRS.Stochastic.Integral

/-!
# Quadratic variation and covariation of Itô integrals; bridge to `HRS/Prob/CLT.lean`

Package SI-01, part 4.  For `M = ∫ Φ · dW` and `M' = ∫ Φ' · dW` in the `L²` class:
* `M_t² - ∫_0^t ∑_k (Φ^k_s)² ds` and `M_t M'_t - ∫_0^t ∑_k Φ^k_s Φ'^k_s ds` are martingales
  (`martingale_itoIntegral_sq_sub`, `martingale_itoIntegral_mul_sub`); these are the formulas
  `B:eq:qv-formula`/`B:eq:qv-cross` (M L1665-1672) and `P:eq:bracket` (M L6574-6575),
  `N:eq:bracket` (M L6494-6498);
* the constructed integrals satisfy the predicates of `HRS/Prob/CLT.lean` *exactly as typed there*:
  `IsContSqMartingale`, `IsQuadraticVariation` (`itoIntegral_isContSqMartingale`,
  `itoIntegral_isQuadraticVariation`) and, for finitely many integrals assembled into an
  `ℝ^p`-valued process, `IsVectorMartingaleWithCovariation` with the Gram-matrix covariation
  density `Σ^{ab}_s = ∑_k Φ^{a,k}_s Φ^{b,k}_s` (`vectorItoIntegral_isVectorMartingaleWithCovariation`).
  Every field of those predicates is met by the construction (the fields `sigma_pathint`,
  `sigma_entry_int` follow from the pathwise `L²` bound); the field `sigma_int` (integrability
  of the trace norm `s1Norm = traceNormMatrix`) needs the identity `traceNormMatrix Q = trace Q`
  for positive semidefinite `Q` (ISSUES §C.5, package METR-03), restated here as
  `traceNormMatrix_eq_trace_of_posSemidef`;
* quadratic variation along partitions in probability (`tendstoInMeasure_sumIncrements_sq`),
  the pathwise input of Itô's formula.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]

/-- The quadratic variation process `A_t = ∫_0^t ∑_k (Φ^k_s)² ds` (`0` for `t < 0`). -/
def qvProcess (Φ : ℝ → Ω → ι → ℝ) : ℝ → Ω → ℝ :=
  fun t ω => ∫ s in Set.Icc 0 t, ∑ k, Φ s ω k ^ 2

/-- The covariation process `∫_0^t ∑_k Φ^k_s Φ'^k_s ds`. -/
def covProcess (Φ Φ' : ℝ → Ω → ι → ℝ) : ℝ → Ω → ℝ :=
  fun t ω => ∫ s in Set.Icc 0 t, ∑ k, Φ s ω k * Φ' s ω k

/-! ### Helper lemmas: joint measurability and pathwise integrability -/

/-- Integrating a jointly measurable function over a fixed interval gives a measurable function. -/
theorem measurable_setIntegral_Icc {Ω' : Type*} [MeasurableSpace Ω'] (H : ℝ × Ω' → ℝ)
    (hH : Measurable H) (a b : ℝ) : Measurable fun ω => ∫ s in Set.Icc a b, H (s, ω) :=
  (hH.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Set.Icc a b))).measurable

theorem measurable_min_progressive {ℱ : Filtration ℝ mΩ} {F : ℝ → Ω → ℝ}
    (hF : IsProgressive ℱ F) (t : ℝ) :
    Measurable[(inferInstance : MeasurableSpace ℝ).prod (ℱ t)]
      (fun p : ℝ × Ω => F (min p.1 t) p.2) := by
  letI : MeasurableSpace Ω := ℱ t
  have hψ : Measurable (fun p : ℝ × Ω => ((⟨min p.1 t, Set.mem_Iic.2 (min_le_right _ _)⟩ :
      Set.Iic t), p.2)) := by
    refine Measurable.prodMk ?_ measurable_snd
    exact Measurable.subtype_mk (measurable_fst.min measurable_const)
  exact (hF t).comp hψ

theorem measurable_uncurry_progressive {ℱ : Filtration ℝ mΩ} {F : ℝ → Ω → ℝ}
    (hF : IsProgressive ℱ F) : Measurable (fun p : ℝ × Ω => F p.1 p.2) := by
  have h : ∀ n : ℕ, Measurable (fun p : ℝ × Ω => F (min p.1 n) p.2) := fun n =>
    (measurable_min_progressive hF n).mono
      (sup_le_sup_left (MeasurableSpace.comap_mono (ℱ.le n)) _) le_rfl
  refine measurable_of_tendsto_metrizable h (tendsto_pi_nhds.2 fun p => ?_)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈p.1⌉₊] with n hn
  have : p.1 ≤ n := (Nat.ceil_le.1 hn)
  simp [min_eq_left this]

theorem measurable_setIntegral_progressive {ℱ : Filtration ℝ mΩ} {F : ℝ → Ω → ℝ}
    (hF : IsProgressive ℱ F) (t : ℝ) : Measurable[ℱ t] fun ω => ∫ s in Set.Icc 0 t, F s ω := by
  have := @measurable_setIntegral_Icc Ω (ℱ t) (fun p => F (min p.1 t) p.2)
    (measurable_min_progressive hF t) 0 t
  convert this using 2 with ω
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  simp [min_eq_left hs.2]


theorem isProgressive_coord {ℱ : Filtration ℝ mΩ} {Φ : ℝ → Ω → ι → ℝ} (hΦ : IsProgressive ℱ Φ)
    (k : ι) : IsProgressive ℱ (fun s ω => Φ s ω k) := fun i => (measurable_pi_apply k).comp (hΦ i)

theorem isProgressive_sum_mul {ℱ : Filtration ℝ mΩ} {Φ Φ' : ℝ → Ω → ι → ℝ}
    (hΦ : IsProgressive ℱ Φ) (hΦ' : IsProgressive ℱ Φ') :
    IsProgressive ℱ (fun s ω => ∑ k, Φ s ω k * Φ' s ω k) := fun i =>
  Finset.measurable_sum _ fun k _ =>
    ((isProgressive_coord hΦ k) i).mul ((isProgressive_coord hΦ' k) i)

theorem isProgressive_sum_sq {ℱ : Filtration ℝ mΩ} {Φ : ℝ → Ω → ι → ℝ}
    (hΦ : IsProgressive ℱ Φ) : IsProgressive ℱ (fun s ω => ∑ k, Φ s ω k ^ 2) := by
  simpa only [sq] using isProgressive_sum_mul hΦ hΦ

theorem measurable_slice {ℱ : Filtration ℝ mΩ} {F : ℝ → Ω → ℝ} (hF : IsProgressive ℱ F) (ω : Ω) :
    Measurable fun s => F s ω :=
  (measurable_uncurry_progressive hF).comp measurable_prodMk_right

theorem enorm_sum_sq (x : ι → ℝ) : ‖∑ k, x k ^ 2‖ₑ = ∑ k, ‖x k‖ₑ ^ 2 := by
  rw [Real.enorm_eq_ofReal (Finset.sum_nonneg fun k _ => sq_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← Real.enorm_eq_ofReal_abs]

section
variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {Φ Φ' : ℝ → Ω → ι → ℝ}

theorem ae_integrableOn_sq (hΦ : IsProgressiveLocL2 P ℱ Φ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, IntegrableOn (fun s => ∑ k, Φ s ω k ^ 2) (Set.Icc 0 T) := by
  filter_upwards [ae_all_iff.2 fun n : ℕ => hΦ.sq n] with ω hω T
  obtain ⟨n, hn⟩ := exists_nat_ge T
  refine IntegrableOn.mono_set ?_ (Set.Icc_subset_Icc_right hn)
  refine ⟨((measurable_slice (isProgressive_sum_sq hΦ.prog) ω).aestronglyMeasurable), ?_⟩
  have := hω n
  simp only [HasFiniteIntegral, enorm_sum_sq]
  exact this

theorem ae_integrableOn_mul (hΦ : IsProgressiveLocL2 P ℱ Φ) (hΦ' : IsProgressiveLocL2 P ℱ Φ') :
    ∀ᵐ ω ∂P, ∀ T : ℝ, IntegrableOn (fun s => ∑ k, Φ s ω k * Φ' s ω k) (Set.Icc 0 T) := by
  filter_upwards [ae_integrableOn_sq hΦ, ae_integrableOn_sq hΦ'] with ω h1 h2 T
  refine Integrable.mono' ((h1 T).add (h2 T)) 
    (measurable_slice (isProgressive_sum_mul hΦ.prog hΦ'.prog) ω).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  calc |∑ k, Φ s ω k * Φ' s ω k| ≤ ∑ k, |Φ s ω k * Φ' s ω k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (Φ s ω k ^ 2 + Φ' s ω k ^ 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        nlinarith [sq_abs (Φ s ω k), sq_abs (Φ' s ω k), sq_nonneg (|Φ s ω k| - |Φ' s ω k|)]
    _ = _ := by rw [Finset.sum_add_distrib]

end

/-- Deterministic: the running integral over `[0, t]` of a locally integrable function is
continuous in `t` (and `0` for `t ≤ 0`). -/
theorem continuous_setIntegral_Icc {f : ℝ → ℝ} (hf : ∀ T : ℝ, IntegrableOn f (Set.Icc 0 T)) :
    Continuous fun t => ∫ s in Set.Icc 0 t, f s := by
  set f' : ℝ → ℝ := Set.indicator (Set.Ici 0) f with hf'
  have hint : ∀ a b : ℝ, IntervalIntegrable f' volume a b := by
    intro a b
    have key : ∀ c d : ℝ, IntegrableOn f' (Set.Ioc c d) := by
      intro c d
      set T := max c d with hT
      have hg : Integrable (Set.indicator (Set.Icc 0 T) f) := (hf T).integrable_indicator measurableSet_Icc
      refine (hg.integrableOn (s := Set.Ioc c d)).congr_fun ?_ measurableSet_Ioc
      intro x hx
      have hxT : x ≤ T := hx.2.trans (le_max_right _ _)
      by_cases h0 : 0 ≤ x
      · simp [hf', Set.indicator, h0, hxT]
      · simp [hf', Set.indicator, h0]
    exact ⟨key a b, key b a⟩
  have heq : ∀ t, ∫ s in Set.Icc 0 t, f s = ∫ s in (0 : ℝ)..t, f' s := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · rw [intervalIntegral.integral_of_le ht, integral_Icc_eq_integral_Ioc]
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      simp [hf', hx.1.le]
    · rw [Set.Icc_eq_empty (not_le.2 ht), Measure.restrict_empty, integral_zero_measure,
        intervalIntegral.integral_symm, intervalIntegral.integral_of_le ht.le,
        integral_Ioc_eq_integral_Ioo]
      rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))]
      · simp
      · intro x hx
        simp [hf', hx.2]
  simp_rw [heq]
  exact intervalIntegral.continuous_primitive hint 0

theorem monotone_setIntegral_Icc {f : ℝ → ℝ} (hf : ∀ T : ℝ, IntegrableOn f (Set.Icc 0 T))
    (hnn : ∀ s, 0 ≤ f s) : Monotone fun t => ∫ s in Set.Icc 0 t, f s := by
  intro a b hab
  exact setIntegral_mono_set (hf b) (Filter.Eventually.of_forall hnn)
    (Filter.Eventually.of_forall (Set.Icc_subset_Icc_right hab))

theorem integral_Icc_sub_eq_Ioc {f : ℝ → ℝ} {s t : ℝ} (hf : IntegrableOn f (Set.Icc 0 t))
    (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ r in Set.Icc 0 t, f r) - ∫ r in Set.Icc 0 s, f r = ∫ r in Set.Ioc s t, f r := by
  rw [← Set.Icc_union_Ioc_eq_Icc hs hst, setIntegral_union _ measurableSet_Ioc
    (hf.mono_set (Set.Icc_subset_Icc_right hst)) (hf.mono_set _)]
  · ring
  · exact Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'.1)
  · exact fun x hx => ⟨hs.trans hx.1.le, hx.2.trans' le_rfl⟩

theorem setIntegral_Icc_of_nonpos (f : ℝ → ℝ) {t : ℝ} (ht : t ≤ 0) :
    ∫ s in Set.Icc 0 t, f s = 0 := by
  have : volume (Set.Icc (0 : ℝ) t) = 0 := by simp [Real.volume_Icc, ht]
  rw [Measure.restrict_eq_zero.2 this, integral_zero_measure]


section MartingaleAux

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {Φ Φ' : ℝ → Ω → ι → ℝ}

theorem martingale_of_nonneg_times [IsProbabilityMeasure P] {f : ℝ → Ω → ℝ}
    (hf : StronglyAdapted ℱ f) (hzero : ∀ t ≤ 0, ∀ ω, f t ω = 0)
    (h : ∀ s t, 0 ≤ s → s ≤ t → P[f t | ℱ s] =ᵐ[P] f s) : Martingale f ℱ P := by
  refine ⟨hf, fun s t hst => ?_⟩
  rcases le_or_gt 0 s with hs | hs
  · exact h s t hs hst
  · have hfs : f s = 0 := funext (hzero s hs.le)
    rcases le_or_gt t 0 with ht | ht
    · have : f t = 0 := funext (hzero t ht)
      rw [this, hfs]; simp
    · have h0 := h 0 t le_rfl ht.le
      have h00 : f 0 = 0 := funext (hzero 0 le_rfl)
      calc P[f t | ℱ s] =ᵐ[P] P[P[f t | ℱ 0] | ℱ s] :=
            (condExp_condExp_of_le (ℱ.mono hs.le) (ℱ.le 0)).symm
        _ =ᵐ[P] P[f 0 | ℱ s] := condExp_congr_ae h0
        _ = f s := by rw [h00, hfs]; simp

theorem martingale_congr_ae {f g : ℝ → Ω → ℝ} (hf : Martingale f ℱ P)
    (hg : StronglyAdapted ℱ g) (h : ∀ t, g t =ᵐ[P] f t) : Martingale g ℱ P :=
  ⟨hg, fun i j hij => (condExp_congr_ae (h j)).trans ((hf.2 i j hij).trans (h i).symm)⟩

theorem martingale_sq_sub_aux [IsProbabilityMeasure P] {M A : ℝ → Ω → ℝ}
    (hM : Martingale M ℱ P) (hM2 : ∀ t, MemLp (M t) 2 P) (hA : Adapted ℱ A)
    (hAint : ∀ t, Integrable (A t) P) (hzero : ∀ t ≤ 0, ∀ ω, M t ω ^ 2 - A t ω = 0)
    (hcond : ∀ s t, 0 ≤ s → s ≤ t →
      P[fun ω => (M t ω - M s ω) ^ 2 | ℱ s] =ᵐ[P] P[fun ω => A t ω - A s ω | ℱ s]) :
    Martingale (fun t ω => M t ω ^ 2 - A t ω) ℱ P := by
  have hMsm : ∀ t, StronglyMeasurable[ℱ t] (M t) := hM.stronglyMeasurable
  refine martingale_of_nonneg_times (fun t => ((hMsm t).pow 2).sub (hA t).stronglyMeasurable)
    hzero ?_
  intro s t hs hst
  have hAts : Integrable (fun ω => A t ω - A s ω) P := (hAint t).sub (hAint s)
  have hD : Integrable (fun ω => (M t ω - M s ω) ^ 2) P := ((hM2 t).sub (hM2 s)).integrable_sq
  have hMM : Integrable (M s * M t) P := (hM2 s).integrable_mul (hM2 t)
  have hT3m : StronglyMeasurable[ℱ s] (fun ω => -(M s ω ^ 2 + A s ω)) :=
    (((hMsm s).pow 2).add (hA s).stronglyMeasurable).neg
  have hT3 : Integrable (fun ω => -(M s ω ^ 2 + A s ω)) P :=
    (((hM2 s).integrable_sq).add (hAint s)).neg
  set T1 : Ω → ℝ := fun ω => (M t ω - M s ω) ^ 2 - (A t ω - A s ω) with hT1def
  set T2 : Ω → ℝ := fun ω => M s ω * M t ω with hT2def
  set T3 : Ω → ℝ := fun ω => -(M s ω ^ 2 + A s ω) with hT3def
  have hT1 : Integrable T1 P := hD.sub hAts
  have hT2 : Integrable T2 P := hMM
  have e : (fun ω => M t ω ^ 2 - A t ω) = T1 + T2 + T2 + T3 := by
    funext ω; simp only [hT1def, hT2def, hT3def, Pi.add_apply]; ring
  rw [e]
  have h1 := condExp_add ((hT1.add hT2).add hT2) hT3 (ℱ s) (μ := P)
  have h2 := condExp_add (hT1.add hT2) hT2 (ℱ s) (μ := P)
  have h2' := condExp_add hT1 hT2 (ℱ s) (μ := P)
  have h3 : P[T1 | ℱ s] =ᵐ[P] P[fun ω => (M t ω - M s ω) ^ 2 | ℱ s] - P[fun ω => A t ω - A s ω | ℱ s] :=
    condExp_sub hD hAts (ℱ s)
  have h5 : P[T2 | ℱ s] =ᵐ[P] M s * P[M t | ℱ s] :=
    condExp_mul_of_stronglyMeasurable_left (hMsm s) hMM (hM.integrable t)
  have h6 : P[T3 | ℱ s] = T3 := condExp_of_stronglyMeasurable (ℱ.le s) hT3m hT3
  have h7 := hM.2 s t hst
  have h8 := hcond s t hs hst
  filter_upwards [h1, h2, h2', h3, h5, h7, h8] with ω a1 a2 a2' a3 a5 a7 a8
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at a1 a2 a2' a3 a5 a7 a8
  rw [a1, a2, a2', a3, a5, a7, h6, a8]
  simp only [hT3def]
  ring

theorem qvProcess_sub_ae [IsProbabilityMeasure P] (hΦ : IsProgressiveL2 P ℱ Φ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    (fun ω => qvProcess Φ t ω - qvProcess Φ s ω) =ᵐ[P]
      fun ω => ∫ r in Set.Ioc s t, ∑ k, Φ r ω k ^ 2 := by
  filter_upwards [ae_integrableOn_sq hΦ.locL2] with ω hω
  exact integral_Icc_sub_eq_Ioc (hω t) hs hst

theorem qvProcess_add_sub_ae [IsProbabilityMeasure P] (hΦ : IsProgressiveL2 P ℱ Φ)
    (hΦ' : IsProgressiveL2 P ℱ Φ') (u : ℝ) :
    ∀ᵐ ω ∂P, qvProcess (fun s ω => Φ s ω + Φ' s ω) u ω -
      qvProcess (fun s ω => Φ s ω + (-1 : ℝ) • Φ' s ω) u ω = 4 * covProcess Φ Φ' u ω := by
  filter_upwards [ae_integrableOn_sq (hΦ.add hΦ').locL2,
    ae_integrableOn_sq (hΦ.add (hΦ'.smul (-1))).locL2,
    ae_integrableOn_mul hΦ.locL2 hΦ'.locL2] with ω h1 h2 h3
  unfold qvProcess covProcess
  rw [← integral_sub (h1 u) (h2 u), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  beta_reduce
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

end MartingaleAux

section Scalar

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ} {Φ Φ' : ℝ → Ω → ι → ℝ}

theorem qvProcess_zero (Φ : ℝ → Ω → ι → ℝ) (ω : Ω) : qvProcess Φ 0 ω = 0 :=
  setIntegral_Icc_of_nonpos _ le_rfl

theorem qvProcess_of_nonpos (Φ : ℝ → Ω → ι → ℝ) {t : ℝ} (ht : t ≤ 0) (ω : Ω) :
    qvProcess Φ t ω = 0 :=
  setIntegral_Icc_of_nonpos _ ht

theorem covProcess_of_nonpos (Φ Φ' : ℝ → Ω → ι → ℝ) {t : ℝ} (ht : t ≤ 0) (ω : Ω) :
    covProcess Φ Φ' t ω = 0 :=
  setIntegral_Icc_of_nonpos _ ht

theorem adapted_qvProcess (hΦ : IsProgressive ℱ Φ) : Adapted ℱ (qvProcess Φ) := fun t =>
  measurable_setIntegral_progressive (isProgressive_sum_sq hΦ) t

theorem adapted_covProcess (hΦ : IsProgressive ℱ Φ) (hΦ' : IsProgressive ℱ Φ') :
    Adapted ℱ (covProcess Φ Φ') := fun t =>
  measurable_setIntegral_progressive (isProgressive_sum_mul hΦ hΦ') t

/-- For locally square-integrable integrands the quadratic variation has a.s. continuous
nondecreasing paths. -/
theorem continuous_qvProcess (hΦ : IsProgressiveLocL2 P ℱ Φ) :
    ∀ᵐ ω ∂P, Continuous fun t => qvProcess Φ t ω := by
  filter_upwards [ae_integrableOn_sq hΦ] with ω hω
  exact continuous_setIntegral_Icc hω

theorem monotone_qvProcess (hΦ : IsProgressiveLocL2 P ℱ Φ) :
    ∀ᵐ ω ∂P, Monotone fun t => qvProcess Φ t ω := by
  filter_upwards [ae_integrableOn_sq hΦ] with ω hω
  exact monotone_setIntegral_Icc hω fun s => Finset.sum_nonneg fun k _ => sq_nonneg _

theorem integrable_qvProcess [IsProbabilityMeasure P] (hΦ : IsProgressiveL2 P ℱ Φ) (t : ℝ) :
    Integrable (qvProcess Φ t) P :=
  (integrable_sq_of_isProgressiveL2 hΦ t).2.1

/-- `M² - [M]` is a martingale: `[∫ Φ dW]_t = ∫_0^t ∑_k |Φ^k|²` (`B:eq:qv-formula`). -/
theorem martingale_itoIntegral_sq_sub [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) :
    Martingale (fun t ω => itoIntegral P ℱ W Φ t ω ^ 2 - qvProcess Φ t ω) ℱ P := by
  refine martingale_sq_sub_aux (martingale_itoIntegral hW hΦ) (memLp_two_itoIntegral hW hΦ)
    (adapted_qvProcess hΦ.prog) (integrable_qvProcess hΦ) ?_ ?_
  · intro t ht ω
    simp [itoIntegral_of_nonpos P ℱ W Φ ht, qvProcess_of_nonpos Φ ht]
  · intro s t hs hst
    exact (condExp_itoIntegral_sub_sq hW hΦ hs hst).trans
      (condExp_congr_ae (qvProcess_sub_ae hΦ hs hst).symm)


/-- `M M' - [M, M']` is a martingale: `[∫ Φ dW, ∫ Φ' dW]_t = ∫_0^t ∑_k Φ^k Φ'^k`
(`B:eq:qv-cross`). -/
theorem martingale_itoIntegral_mul_sub [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) (hΦ' : IsProgressiveL2 P ℱ Φ') :
    Martingale (fun t ω => itoIntegral P ℱ W Φ t ω * itoIntegral P ℱ W Φ' t ω -
      covProcess Φ Φ' t ω) ℱ P := by
  have hp := martingale_itoIntegral_sq_sub hW (hΦ.add hΦ')
  have hm := martingale_itoIntegral_sq_sub hW (hΦ.add (hΦ'.smul (-1)))
  refine martingale_congr_ae ((hp.smul (1/4 : ℝ)).sub (hm.smul (1/4 : ℝ))) ?_ ?_
  · intro t
    exact (((adapted_itoIntegral P ℱ W Φ t).mul (adapted_itoIntegral P ℱ W Φ' t)).sub
      (adapted_covProcess hΦ.prog hΦ'.prog t)).stronglyMeasurable
  · intro t
    filter_upwards [itoIntegral_add hW hΦ (hΦ'.smul (-1)), itoIntegral_add hW hΦ hΦ',
      itoIntegral_smul hW hΦ' (-1), qvProcess_add_sub_ae hΦ hΦ' t] with ω a1 a2 a3 a4
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [a1 t, a2 t, a3 t]
    linear_combination (1/4 : ℝ) * a4


/-- The Itô integral is a continuous square-integrable martingale on `[0, T]` in the sense of
`HRS/Prob/CLT.lean`. -/
theorem itoIntegral_isContSqMartingale [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) (T : ℝ) : IsContSqMartingale P ℱ T (itoIntegral P ℱ W Φ) :=
  ⟨martingale_itoIntegral hW hΦ,
    Filter.Eventually.of_forall fun ω => itoIntegral_of_nonpos P ℱ W Φ le_rfl ω,
    Filter.Eventually.of_forall fun ω => (continuous_itoIntegral P ℱ W Φ ω).continuousOn,
    fun τ _ => memLp_two_itoIntegral hW hΦ τ⟩

/-- `qvProcess Φ` is the quadratic variation of `∫ Φ dW` in the sense of `HRS/Prob/CLT.lean`
(ISSUES §C1: "`IsQuadraticVariation` must be proved for `∫ Φ dW`, never assumed"). -/
theorem itoIntegral_isQuadraticVariation [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) (T : ℝ) :
    IsQuadraticVariation P ℱ T (itoIntegral P ℱ W Φ) (qvProcess Φ) := by
  refine ⟨adapted_qvProcess hΦ.prog, Filter.Eventually.of_forall fun ω => qvProcess_zero Φ ω,
    ?_, ?_, martingale_itoIntegral_sq_sub hW hΦ⟩
  · filter_upwards [continuous_qvProcess hΦ.locL2] with ω h
    exact h.continuousOn
  · filter_upwards [monotone_qvProcess hΦ.locL2] with ω h
    exact h.monotoneOn _

/-! ### Auxiliary results for quadratic variation along partitions -/

theorem integral_mul_eq_of_martingale [IsProbabilityMeasure P] {M : ℝ → Ω → ℝ}
    (hM : Martingale M ℱ P) (hM2 : ∀ t, MemLp (M t) 2 P) {s t : ℝ} (hst : s ≤ t) :
    ∫ ω, M s ω * M t ω ∂P = ∫ ω, M s ω ^ 2 ∂P := by
  have hMM : Integrable (M s * M t) P := (hM2 s).integrable_mul (hM2 t)
  have h : P[M s * M t | ℱ s] =ᵐ[P] M s * P[M t | ℱ s] :=
    condExp_mul_of_stronglyMeasurable_left (hM.stronglyMeasurable s) hMM (hM.integrable t)
  calc ∫ ω, M s ω * M t ω ∂P = ∫ ω, P[M s * M t | ℱ s] ω ∂P := (integral_condExp (ℱ.le s)).symm
    _ = ∫ ω, M s ω ^ 2 ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [h, hM.2 s t hst] with ω h1 h2
      rw [h1, Pi.mul_apply, h2, sq]

theorem integral_incr_sq_of_martingale [IsProbabilityMeasure P] {M : ℝ → Ω → ℝ}
    (hM : Martingale M ℱ P) (hM2 : ∀ t, MemLp (M t) 2 P) {s t : ℝ} (hst : s ≤ t) :
    ∫ ω, (M t ω - M s ω) ^ 2 ∂P = ∫ ω, M t ω ^ 2 ∂P - ∫ ω, M s ω ^ 2 ∂P := by
  have h1 : Integrable (fun ω => M t ω ^ 2) P := (hM2 t).integrable_sq
  have h2 : Integrable (fun ω => M s ω ^ 2) P := (hM2 s).integrable_sq
  have h3 : Integrable (fun ω => M s ω * M t ω) P := (hM2 s).integrable_mul (hM2 t)
  have e : (fun ω => (M t ω - M s ω) ^ 2) =
      fun ω => (M t ω ^ 2 + M s ω ^ 2) - 2 * (M s ω * M t ω) := by
    funext ω; ring
  have hA : Integrable (fun ω => M t ω ^ 2 + M s ω ^ 2) P := h1.add h2
  have hB : Integrable (fun ω => 2 * (M s ω * M t ω)) P := h3.const_mul 2
  rw [e, integral_sub hA hB, integral_add h1 h2, integral_const_mul,
    integral_mul_eq_of_martingale hM hM2 hst]
  ring

/-- Sum of squared increments of a martingale along a partition has expectation
`E M_b² - E M_a²`. -/
theorem integral_sum_incr_sq_of_martingale [IsProbabilityMeasure P] {M : ℝ → Ω → ℝ}
    (hM : Martingale M ℱ P) (hM2 : ∀ t, MemLp (M t) 2 P) {a b : ℝ} (π : Partition a b) :
    ∫ ω, π.sumIncrements (fun s t => (M t ω - M s ω) ^ 2) ∂P =
      ∫ ω, M b ω ^ 2 ∂P - ∫ ω, M a ω ^ 2 ∂P := by
  unfold Partition.sumIncrements
  beta_reduce
  have hi : ∀ i : Fin π.n, Integrable
      (fun ω => (M (π.pt i.succ) ω - M (π.pt i.castSucc) ω) ^ 2) P := fun i =>
    ((hM2 _).sub (hM2 _)).integrable_sq
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_incr_sq_of_martingale hM hM2 (π.pt_le _)]
  rw [Partition.sum_telescope π.n (fun i => ∫ ω, M (π.pt i) ω ^ 2 ∂P), π.first, π.last]


theorem condExp_incr_sq_sub_zero [IsProbabilityMeasure P] {M A : ℝ → Ω → ℝ}
    (hM : Martingale M ℱ P) (hM2 : ∀ t, MemLp (M t) 2 P) (hAint : ∀ t, Integrable (A t) P)
    (hY : Martingale (fun t ω => M t ω ^ 2 - A t ω) ℱ P) {s t : ℝ} (hst : s ≤ t) :
    P[fun ω => (M t ω - M s ω) ^ 2 - (A t ω - A s ω) | ℱ s] =ᵐ[P] 0 := by
  have hMsm : StronglyMeasurable[ℱ s] (M s) := hM.stronglyMeasurable s
  set Ta : Ω → ℝ := fun ω => M s ω * M t ω with hTa
  set Tb : Ω → ℝ := fun ω => M s ω ^ 2 with hTb
  set T1 : Ω → ℝ := fun ω => (M t ω ^ 2 - A t ω) - (M s ω ^ 2 - A s ω) with hT1
  have hTa_i : Integrable Ta P := (hM2 s).integrable_mul (hM2 t)
  have hTb_i : Integrable Tb P := (hM2 s).integrable_sq
  have hTb_m : StronglyMeasurable[ℱ s] Tb := hMsm.pow 2
  have hT1_i : Integrable T1 P := (hY.integrable t).sub (hY.integrable s)
  have e : (fun ω => (M t ω - M s ω) ^ 2 - (A t ω - A s ω)) =
      T1 - (2:ℝ) • Ta + (2:ℝ) • Tb := by
    funext ω; simp only [hT1, hTa, hTb, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  have h1 := condExp_add (hT1_i.sub (hTa_i.smul (2:ℝ))) (hTb_i.smul (2:ℝ)) (ℱ s) (μ := P)
  have h2 := condExp_sub hT1_i (hTa_i.smul (2:ℝ)) (ℱ s) (μ := P)
  have h3 : P[T1 | ℱ s] =ᵐ[P] P[fun ω => M t ω ^ 2 - A t ω | ℱ s] -
      P[fun ω => M s ω ^ 2 - A s ω | ℱ s] := condExp_sub (hY.integrable t) (hY.integrable s) (ℱ s)
  have h4 := condExp_smul (μ := P) (2:ℝ) Ta (ℱ s)
  have h5 := condExp_smul (μ := P) (2:ℝ) Tb (ℱ s)
  have h6 : P[Ta | ℱ s] =ᵐ[P] M s * P[M t | ℱ s] :=
    condExp_mul_of_stronglyMeasurable_left hMsm ((hM2 s).integrable_mul (hM2 t)) (hM.integrable t)
  have h7 : P[Tb | ℱ s] = Tb := condExp_of_stronglyMeasurable (ℱ.le s) hTb_m hTb_i
  have h8 : P[fun ω => M s ω ^ 2 - A s ω | ℱ s] = fun ω => M s ω ^ 2 - A s ω :=
    condExp_of_stronglyMeasurable (ℱ.le s) (hY.stronglyMeasurable s) (hY.integrable s)
  have h9 := hM.2 s t hst
  have h10 := hY.2 s t hst
  filter_upwards [h1, h2, h3, h4, h5, h6, h9, h10] with ω a1 a2 a3 a4 a5 a6 a9 a10
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at a1 a2 a3 a4 a5 a6 a9 a10
  have h7' : P[Tb | ℱ s] ω = M s ω ^ 2 := by rw [h7]
  have h8' : P[fun ω => M s ω ^ 2 - A s ω | ℱ s] ω = M s ω ^ 2 - A s ω := by rw [h8]
  simp only [Pi.zero_apply]
  rw [a1, a2, a4, a5, h7']
  have a3' : P[T1 | ℱ s] ω = 0 := by
    rw [a3, a10, h8']; ring
  rw [a3', a6, a9]
  ring


/-- The centred squared increments `N_i = (ΔM_i)² - ΔA_i` along a partition. -/
def qvIncr (M A : ℝ → Ω → ℝ) {a b : ℝ} (π : Partition a b) (i : Fin π.n) (ω : Ω) : ℝ :=
  (M (π.pt i.succ) ω - M (π.pt i.castSucc) ω) ^ 2 - (A (π.pt i.succ) ω - A (π.pt i.castSucc) ω)

theorem integral_qvIncr_mul_of_lt [IsProbabilityMeasure P] {M A : ℝ → Ω → ℝ}
    (hM : Martingale M ℱ P) (hM2 : ∀ t, MemLp (M t) 2 P) (hA : Adapted ℱ A)
    (hAint : ∀ t, Integrable (A t) P)
    (hY : Martingale (fun t ω => M t ω ^ 2 - A t ω) ℱ P) {a b : ℝ} (π : Partition a b)
    (hN : ∀ i : Fin π.n, MemLp (qvIncr M A π i) 2 P) {i j : Fin π.n} (hij : i < j) :
    ∫ ω, qvIncr M A π i ω * qvIncr M A π j ω ∂P = 0 := by
  have hle : π.pt i.succ ≤ π.pt j.castSucc := by
    apply π.mono
    rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]
    exact hij
  set u := π.pt j.castSucc
  have hNi : StronglyMeasurable[ℱ u] (qvIncr M A π i) := by
    unfold qvIncr
    have h1 : StronglyMeasurable[ℱ u] (M (π.pt i.succ)) :=
      (hM.stronglyMeasurable _).mono (ℱ.mono hle)
    have h2 : StronglyMeasurable[ℱ u] (M (π.pt i.castSucc)) :=
      (hM.stronglyMeasurable _).mono (ℱ.mono ((π.pt_le i).trans hle))
    have h3 : StronglyMeasurable[ℱ u] (A (π.pt i.succ)) :=
      (hA _).stronglyMeasurable.mono (ℱ.mono hle)
    have h4 : StronglyMeasurable[ℱ u] (A (π.pt i.castSucc)) :=
      (hA _).stronglyMeasurable.mono (ℱ.mono ((π.pt_le i).trans hle))
    exact ((h1.sub h2).pow 2).sub (h3.sub h4)
  have hint : Integrable (qvIncr M A π i * qvIncr M A π j) P := (hN i).integrable_mul (hN j)
  have hcond : P[qvIncr M A π j | ℱ u] =ᵐ[P] 0 :=
    condExp_incr_sq_sub_zero hM hM2 hAint hY (π.pt_le j)
  have h : P[qvIncr M A π i * qvIncr M A π j | ℱ u] =ᵐ[P]
      qvIncr M A π i * P[qvIncr M A π j | ℱ u] :=
    condExp_mul_of_stronglyMeasurable_left hNi hint ((hN j).integrable one_le_two)
  calc ∫ ω, qvIncr M A π i ω * qvIncr M A π j ω ∂P
      = ∫ ω, P[qvIncr M A π i * qvIncr M A π j | ℱ u] ω ∂P := (integral_condExp (ℱ.le u)).symm
    _ = 0 := by
      have : ∀ᵐ ω ∂P, P[qvIncr M A π i * qvIncr M A π j | ℱ u] ω = 0 := by
        filter_upwards [h, hcond] with ω h1 h2
        rw [h1, Pi.mul_apply, h2]; simp
      rw [integral_congr_ae this]; simp

theorem integral_sq_sum_qvIncr [IsProbabilityMeasure P] {M A : ℝ → Ω → ℝ}
    (hM : Martingale M ℱ P) (hM2 : ∀ t, MemLp (M t) 2 P) (hA : Adapted ℱ A)
    (hAint : ∀ t, Integrable (A t) P)
    (hY : Martingale (fun t ω => M t ω ^ 2 - A t ω) ℱ P) {a b : ℝ} (π : Partition a b)
    (hN : ∀ i : Fin π.n, MemLp (qvIncr M A π i) 2 P) :
    ∫ ω, (∑ i, qvIncr M A π i ω) ^ 2 ∂P = ∑ i, ∫ ω, qvIncr M A π i ω ^ 2 ∂P := by
  have hcross : ∀ i j : Fin π.n, i ≠ j →
      ∫ ω, qvIncr M A π i ω * qvIncr M A π j ω ∂P = 0 := by
    intro i j hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact integral_qvIncr_mul_of_lt hM hM2 hA hAint hY π hN h
    · have := integral_qvIncr_mul_of_lt hM hM2 hA hAint hY π hN h
      simpa only [mul_comm] using this
  have hexp : ∀ ω, (∑ i, qvIncr M A π i ω) ^ 2 =
      ∑ i, ∑ j, qvIncr M A π i ω * qvIncr M A π j ω := by
    intro ω; rw [sq, Finset.sum_mul_sum]
  simp_rw [hexp]
  have hI : ∀ i j : Fin π.n, Integrable (fun ω => qvIncr M A π i ω * qvIncr M A π j ω) P :=
    fun i j => (hN i).integrable_mul (hN j)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hI i j)]
  rw [Finset.sum_eq_single i (fun j _ hj => hcross i j (Ne.symm hj)) (by simp)]
  simp [sq]


theorem sum_pow_four_le {α : Type*} (s : Finset α) (f : α → ℝ) :
    (∑ i ∈ s, f i) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, f i ^ 4 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := s) (f := f)
  have h2 := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => f i ^ 2)
  calc (∑ i ∈ s, f i) ^ 4 = ((∑ i ∈ s, f i) ^ 2) ^ 2 := by ring
    _ ≤ ((s.card : ℝ) * ∑ i ∈ s, f i ^ 2) ^ 2 := by gcongr
    _ = (s.card : ℝ) ^ 2 * (∑ i ∈ s, f i ^ 2) ^ 2 := by ring
    _ ≤ (s.card : ℝ) ^ 2 * ((s.card : ℝ) * ∑ i ∈ s, (f i ^ 2) ^ 2) := by gcongr
    _ = _ := by simp_rw [← pow_mul]; ring

theorem integral_incr_pow_four_elemIntegral [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W) (Ψ : SimpleIntegrand ℱ ι) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ∫ ω, (Ψ.elemIntegral W b ω - Ψ.elemIntegral W a ω) ^ 4 ∂P ≤ K * (b - a) ^ 2 := by
  obtain ⟨C₀, hC₀⟩ := Ψ.bdd
  set C : ℝ := |C₀| with hCdef
  have hC : ∀ i ω k, |Ψ.ξ i ω k| ≤ C := fun i ω k => (hC₀ i ω k).trans (le_abs_self _)
  have hC0 : 0 ≤ C := abs_nonneg _
  set r : ℝ := (Fintype.card (Fin Ψ.n × ι) : ℝ) with hr
  refine ⟨48 * r ^ 4 * C ^ 4, by positivity, fun a b ha hab => ?_⟩
  have ht0 : ∀ j : Fin (Ψ.n + 1), 0 ≤ Ψ.t j := fun j => Ψ.nonneg.trans (Ψ.mono (Fin.zero_le j))
  -- the increments of the clamped Brownian motions
  let D : Fin (Ψ.n + 1) → ι → Ω → ℝ := fun j k ω =>
    W (Real.toNNReal (min (Ψ.t j) b)) ω k - W (Real.toNNReal (min (Ψ.t j) a)) ω k
  have hD4 : ∀ j k, ∫ ω, D j k ω ^ 4 ∂P ≤ 3 * (b - a) ^ 2 := by
    intro j k
    have hle : Real.toNNReal (min (Ψ.t j) a) ≤ Real.toNNReal (min (Ψ.t j) b) :=
      Real.toNNReal_le_toNNReal (min_le_min_left _ hab)
    have := IsBrownianFiltration.integral_incr_fourth hW hle k (P := P)
    simp only [D]
    rw [this]
    have e1 : ((Real.toNNReal (min (Ψ.t j) b) : ℝ≥0) : ℝ) = min (Ψ.t j) b :=
      Real.coe_toNNReal _ (le_min (ht0 j) (ha.trans hab))
    have e2 : ((Real.toNNReal (min (Ψ.t j) a) : ℝ≥0) : ℝ) = min (Ψ.t j) a :=
      Real.coe_toNNReal _ (le_min (ht0 j) ha)
    rw [e1, e2]
    have h1 : 0 ≤ min (Ψ.t j) b - min (Ψ.t j) a := sub_nonneg.2 (min_le_min_left _ hab)
    have h2 : min (Ψ.t j) b - min (Ψ.t j) a ≤ b - a := by
      rcases le_total (Ψ.t j) a with h | h
      · rw [min_eq_left h, min_eq_left (h.trans hab)]; linarith
      · rw [min_eq_right h]
        rcases le_total (Ψ.t j) b with h' | h'
        · rw [min_eq_left h']; linarith
        · rw [min_eq_right h']
    nlinarith
  have hDint : ∀ j k, Integrable (fun ω => D j k ω ^ 4) P := by
    intro j k
    have hle : Real.toNNReal (min (Ψ.t j) a) ≤ Real.toNNReal (min (Ψ.t j) b) :=
      Real.toNNReal_le_toNNReal (min_le_min_left _ hab)
    have := (IsBrownianFiltration.memLp_incr_coord hW hle k (p := (4 : ℕ)) (by simp)).integrable_norm_pow
      (by norm_num)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    show ‖D j k ω‖ ^ 4 = D j k ω ^ 4
    rw [Real.norm_eq_abs]
    exact Even.pow_abs ⟨2, by norm_num⟩ _
  have hdiff : ∀ ω, Ψ.elemIntegral W b ω - Ψ.elemIntegral W a ω =
      ∑ x : Fin Ψ.n × ι, Ψ.ξ x.1 ω x.2 * (D x.1.succ x.2 ω - D x.1.castSucc x.2 ω) := by
    intro ω
    rw [Fintype.sum_prod_type]
    unfold SimpleIntegrand.elemIntegral
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [D]; ring
  have hterm : ∀ (x y : ℝ) (c : ℝ), |c| ≤ C → (c * (x - y)) ^ 4 ≤ 8 * C ^ 4 * (x ^ 4 + y ^ 4) := by
    intro x y c hc
    have h1 : c ^ 4 ≤ C ^ 4 := by
      have : |c| ^ 4 ≤ C ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hc 4
      rwa [Even.pow_abs ⟨2, by norm_num⟩] at this
    have h2 : (x - y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
      nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x ^ 2 - y ^ 2),
        sq_nonneg (x ^ 2 + y ^ 2)]
    calc (c * (x - y)) ^ 4 = c ^ 4 * (x - y) ^ 4 := mul_pow _ _ _
      _ ≤ C ^ 4 * (8 * (x ^ 4 + y ^ 4)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by ring
  have hpt : ∀ ω, (Ψ.elemIntegral W b ω - Ψ.elemIntegral W a ω) ^ 4 ≤
      r ^ 3 * ∑ x : Fin Ψ.n × ι, 8 * C ^ 4 * (D x.1.succ x.2 ω ^ 4 + D x.1.castSucc x.2 ω ^ 4) := by
    intro ω
    rw [hdiff ω]
    refine (sum_pow_four_le Finset.univ _).trans ?_
    have hr' : ((Finset.univ : Finset (Fin Ψ.n × ι)).card : ℝ) = r := by simp [hr]
    rw [hr']
    gcongr with x _
    exact hterm _ _ _ (hC _ _ _)
  have hRint : Integrable (fun ω => r ^ 3 * ∑ x : Fin Ψ.n × ι,
      8 * C ^ 4 * (D x.1.succ x.2 ω ^ 4 + D x.1.castSucc x.2 ω ^ 4)) P := by
    refine Integrable.const_mul (integrable_finsetSum _ fun x _ => ?_) _
    exact ((hDint _ _).add (hDint _ _)).const_mul _
  calc ∫ ω, (Ψ.elemIntegral W b ω - Ψ.elemIntegral W a ω) ^ 4 ∂P
      ≤ ∫ ω, r ^ 3 * ∑ x : Fin Ψ.n × ι,
          8 * C ^ 4 * (D x.1.succ x.2 ω ^ 4 + D x.1.castSucc x.2 ω ^ 4) ∂P :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity) hRint
          (Filter.Eventually.of_forall hpt)
    _ = r ^ 3 * ∑ x : Fin Ψ.n × ι,
          8 * C ^ 4 * (∫ ω, D x.1.succ x.2 ω ^ 4 ∂P + ∫ ω, D x.1.castSucc x.2 ω ^ 4 ∂P) := by
        have hI : ∀ x : Fin Ψ.n × ι, Integrable (fun ω =>
            8 * C ^ 4 * (D x.1.succ x.2 ω ^ 4 + D x.1.castSucc x.2 ω ^ 4)) P := fun x =>
          ((hDint _ _).add (hDint _ _)).const_mul _
        rw [integral_const_mul, integral_finsetSum _ (fun x _ => hI x)]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [integral_const_mul, integral_add (hDint _ _) (hDint _ _)]
    _ ≤ r ^ 3 * ∑ x : Fin Ψ.n × ι, 8 * C ^ 4 * (3 * (b - a) ^ 2 + 3 * (b - a) ^ 2) := by
        gcongr with x _
        · exact hD4 _ _
        · exact hD4 _ _
    _ = 48 * r ^ 4 * C ^ 4 * (b - a) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hr]
        ring


theorem abs_qvProcess_sub_le (Ψ : SimpleIntegrand ℱ ι) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (ω : Ω) (s t : ℝ), 0 ≤ s → s ≤ t →
      |qvProcess Ψ.toFun t ω - qvProcess Ψ.toFun s ω| ≤ c * (t - s) := by
  obtain ⟨C, hC⟩ := Ψ.toFun_bdd
  refine ⟨Fintype.card ι * C ^ 2, by positivity, fun ω s t hs hst => ?_⟩
  have hf : ∀ r, ∑ k, Ψ.toFun r ω k ^ 2 ≤ Fintype.card ι * C ^ 2 := by
    intro r
    calc ∑ k, Ψ.toFun r ω k ^ 2 ≤ ∑ _k : ι, C ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          exact sq_le_sq' (abs_le.1 (hC r ω k)).1 (abs_le.1 (hC r ω k)).2
      _ = _ := by simp
  have hmeas : Measurable fun r => ∑ k, Ψ.toFun r ω k ^ 2 :=
    measurable_slice (isProgressive_sum_sq Ψ.isProgressive_toFun) ω
  have hint : IntegrableOn (fun r => ∑ k, Ψ.toFun r ω k ^ 2) (Set.Icc 0 t) := by
    refine Measure.integrableOn_of_bounded (M := |Fintype.card ι * C ^ 2|) (by simp)
      hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun r => ?_
    rw [Real.norm_eq_abs]
    exact (abs_le_abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _) (hf r)) |>.trans le_rfl
  have := integral_Icc_sub_eq_Ioc hint hs hst
  change |(∫ r in Set.Icc 0 t, ∑ k, Ψ.toFun r ω k ^ 2) - ∫ r in Set.Icc 0 s, ∑ k, Ψ.toFun r ω k ^ 2| ≤ _
  rw [this]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc s t)
    (f := fun r => ∑ k, Ψ.toFun r ω k ^ 2) (C := Fintype.card ι * C ^ 2)
    (by simp) (fun r _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)]
      exact hf r)
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  simp [Real.volume_real_Ioc_of_le hst]


theorem simple_qv_L2 [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (Ψ : SimpleIntegrand ℱ ι) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ), 0 ≤ T → ∀ π : Partition 0 T,
      MemLp (fun ω => π.sumIncrements
        (fun s t => (Ψ.elemIntegral W t ω - Ψ.elemIntegral W s ω) ^ 2) -
        qvProcess Ψ.toFun T ω) 2 P ∧
      ∫ ω, (π.sumIncrements (fun s t => (Ψ.elemIntegral W t ω - Ψ.elemIntegral W s ω) ^ 2) -
        qvProcess Ψ.toFun T ω) ^ 2 ∂P ≤ K * π.mesh * T := by
  obtain ⟨K₄, hK₄, hK₄b⟩ := integral_incr_pow_four_elemIntegral hW Ψ
  obtain ⟨c, hc, hcb⟩ := abs_qvProcess_sub_le Ψ
  refine ⟨2 * K₄ + 2 * c ^ 2, by positivity, fun T hT π => ?_⟩
  set I := Ψ.elemIntegral W with hIdef
  set A := qvProcess Ψ.toFun with hAdef
  have hIm : Martingale I ℱ P := SimpleIntegrand.martingale_elemIntegral hW Ψ
  have hI2 : ∀ t, MemLp (I t) 2 P := fun t => SimpleIntegrand.memLp_elemIntegral hW Ψ t 2 (by norm_num)
  have hI4 : ∀ t, MemLp (I t) 4 P := fun t => by
    simpa using SimpleIntegrand.memLp_elemIntegral hW Ψ t 4 (by norm_num)
  have hY : Martingale (fun t ω => I t ω ^ 2 - A t ω) ℱ P :=
    SimpleIntegrand.martingale_elemIntegral_sq_sub hW Ψ
  have hA : Adapted ℱ A := adapted_qvProcess Ψ.isProgressive_toFun
  have hAint : ∀ t, Integrable (A t) P := fun t =>
    integrable_qvProcess (IsProgressiveL2.simple P Ψ) t
  have hpt0 : ∀ i : Fin (π.n + 1), 0 ≤ π.pt i := π.pt_nonneg le_rfl
  -- sum identity
  have hsum : ∀ ω, π.sumIncrements (fun s t => (I t ω - I s ω) ^ 2) - A T ω =
      ∑ i, qvIncr I A π i ω := by
    intro ω
    unfold qvIncr Partition.sumIncrements
    rw [Finset.sum_sub_distrib,
      Partition.sum_telescope π.n (fun i => A (π.pt i) ω), π.first, π.last,
      show A 0 ω = 0 from qvProcess_zero _ ω]
    ring
  -- increments are in L⁴ and bounded
  have hΔ4 : ∀ i : Fin π.n, Integrable
      (fun ω => (I (π.pt i.succ) ω - I (π.pt i.castSucc) ω) ^ 4) P := by
    intro i
    have := ((hI4 (π.pt i.succ)).sub (hI4 (π.pt i.castSucc))).integrable_norm_pow
      (p := 4) (by norm_num)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    show ‖(I (π.pt i.succ) - I (π.pt i.castSucc)) ω‖ ^ 4 = _
    rw [Real.norm_eq_abs]
    exact Even.pow_abs ⟨2, by norm_num⟩ _
  have hΔA : ∀ i : Fin π.n, ∀ ω, |A (π.pt i.succ) ω - A (π.pt i.castSucc) ω| ≤
      c * (π.pt i.succ - π.pt i.castSucc) := fun i ω =>
    hcb ω _ _ (hpt0 _) (π.pt_le i)
  have hN : ∀ i : Fin π.n, MemLp (qvIncr I A π i) 2 P := by
    intro i
    have h1 : MemLp (fun ω => (I (π.pt i.succ) ω - I (π.pt i.castSucc) ω) ^ 2) 2 P := by
      refine (memLp_two_iff_integrable_sq ?_).2 ?_
      · exact (((hIm.stronglyMeasurable _).mono (ℱ.le _)).sub
          ((hIm.stronglyMeasurable _).mono (ℱ.le _))).pow 2 |>.aestronglyMeasurable
      · refine (hΔ4 i).congr (Filter.Eventually.of_forall fun ω => ?_)
        simp only; ring
    have h2 : MemLp (fun ω => A (π.pt i.succ) ω - A (π.pt i.castSucc) ω) 2 P := by
      refine MemLp.of_bound ?_ (c * (π.pt i.succ - π.pt i.castSucc))
        (Filter.Eventually.of_forall fun ω => ?_)
      · exact (((hA _).mono (ℱ.le _) le_rfl).sub ((hA _).mono (ℱ.le _) le_rfl)).aestronglyMeasurable
      · rw [Real.norm_eq_abs]; exact hΔA i ω
    exact h1.sub h2
  have hsq := integral_sq_sum_qvIncr hIm hI2 hA hAint hY π hN
  have hper : ∀ i : Fin π.n, ∫ ω, qvIncr I A π i ω ^ 2 ∂P ≤
      (2 * K₄ + 2 * c ^ 2) * (π.pt i.succ - π.pt i.castSucc) ^ 2 := by
    intro i
    set d := π.pt i.succ - π.pt i.castSucc with hd
    have hd0 : 0 ≤ d := sub_nonneg.2 (π.pt_le i)
    have hpw : ∀ ω, qvIncr I A π i ω ^ 2 ≤
        2 * (I (π.pt i.succ) ω - I (π.pt i.castSucc) ω) ^ 4 + 2 * (c * d) ^ 2 := by
      intro ω
      have h1 := hΔA i ω
      have h2 : (A (π.pt i.succ) ω - A (π.pt i.castSucc) ω) ^ 2 ≤ (c * d) ^ 2 :=
        sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
      unfold qvIncr
      set x := (I (π.pt i.succ) ω - I (π.pt i.castSucc) ω) with hx
      set y := A (π.pt i.succ) ω - A (π.pt i.castSucc) ω
      nlinarith [sq_nonneg (x ^ 2 + y), sq_nonneg x, sq_nonneg y]
    calc ∫ ω, qvIncr I A π i ω ^ 2 ∂P
        ≤ ∫ ω, (2 * (I (π.pt i.succ) ω - I (π.pt i.castSucc) ω) ^ 4 + 2 * (c * d) ^ 2) ∂P :=
          integral_mono (hN i).integrable_sq (((hΔ4 i).const_mul 2).add (integrable_const _))
            hpw
      _ = 2 * ∫ ω, (I (π.pt i.succ) ω - I (π.pt i.castSucc) ω) ^ 4 ∂P + 2 * (c * d) ^ 2 := by
          rw [integral_add ((hΔ4 i).const_mul 2) (integrable_const _), integral_const_mul,
            integral_const]
          simp
      _ ≤ 2 * (K₄ * d ^ 2) + 2 * (c * d) ^ 2 := by
          gcongr
          exact hK₄b _ _ (hpt0 _) (π.pt_le i)
      _ = _ := by ring
  have hfun : (fun ω => (π.sumIncrements (fun s t => (I t ω - I s ω) ^ 2) - A T ω) ^ 2) =
      fun ω => (∑ i, qvIncr I A π i ω) ^ 2 := by
    funext ω; rw [hsum ω]
  have hfun1 : (fun ω => π.sumIncrements (fun s t => (I t ω - I s ω) ^ 2) - A T ω) =
      fun ω => ∑ i, qvIncr I A π i ω := by
    funext ω; rw [hsum ω]
  refine ⟨?_, ?_⟩
  · rw [hfun1]
    exact memLp_finsetSum _ fun i _ => hN i
  show ∫ ω, (π.sumIncrements (fun s t => (I t ω - I s ω) ^ 2) - A T ω) ^ 2 ∂P ≤ _
  rw [hfun, hsq]
  calc ∑ i, ∫ ω, qvIncr I A π i ω ^ 2 ∂P
      ≤ ∑ i : Fin π.n, (2 * K₄ + 2 * c ^ 2) * (π.mesh * (π.pt i.succ - π.pt i.castSucc)) := by
        refine Finset.sum_le_sum fun i _ => (hper i).trans ?_
        have hd0 : 0 ≤ π.pt i.succ - π.pt i.castSucc := sub_nonneg.2 (π.pt_le i)
        have := π.length_le_mesh i
        have hK : 0 ≤ 2 * K₄ + 2 * c ^ 2 := by positivity
        calc (2 * K₄ + 2 * c ^ 2) * (π.pt i.succ - π.pt i.castSucc) ^ 2
            = (2 * K₄ + 2 * c ^ 2) * ((π.pt i.succ - π.pt i.castSucc) *
                (π.pt i.succ - π.pt i.castSucc)) := by ring
          _ ≤ (2 * K₄ + 2 * c ^ 2) * (π.mesh * (π.pt i.succ - π.pt i.castSucc)) := by
              gcongr
    _ = (2 * K₄ + 2 * c ^ 2) * π.mesh * T := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, π.sum_length]
        ring


theorem enorm_sq_sub_sq_le (u v : ℝ) {l : ℝ} (hl : 0 < l) :
    ‖u ^ 2 - v ^ 2‖ₑ ≤ ENNReal.ofReal (1 + l) * ‖u - v‖ₑ ^ 2 + ENNReal.ofReal l⁻¹ * ‖v‖ₑ ^ 2 := by
  have h1 : |u ^ 2 - v ^ 2| ≤ (1 + l) * (u - v) ^ 2 + l⁻¹ * v ^ 2 := by
    have e : u ^ 2 - v ^ 2 = (u - v) ^ 2 + 2 * (u - v) * v := by ring
    have h2 : 2 * |u - v| * |v| ≤ l * (u - v) ^ 2 + l⁻¹ * v ^ 2 := by
      have key : 0 ≤ (l * |u - v| - |v|) ^ 2 / l := by positivity
      have e2 : (l * |u - v| - |v|) ^ 2 / l = l * |u - v| ^ 2 - 2 * |u - v| * |v| + l⁻¹ * |v| ^ 2 := by
        field_simp
        ring
      rw [e2, sq_abs, sq_abs] at key
      linarith
    rw [e]
    calc |(u - v) ^ 2 + 2 * (u - v) * v| ≤ |(u - v) ^ 2| + |2 * (u - v) * v| := abs_add_le _ _
      _ = (u - v) ^ 2 + 2 * |u - v| * |v| := by
        rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_mul, abs_two]
      _ ≤ _ := by nlinarith [h2]
  have h3 : ‖u ^ 2 - v ^ 2‖ₑ = ENNReal.ofReal |u ^ 2 - v ^ 2| := Real.enorm_eq_ofReal_abs _
  have h4 : ∀ x : ℝ, ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [h3, h4, h4]
  calc ENNReal.ofReal |u ^ 2 - v ^ 2| ≤ ENNReal.ofReal ((1 + l) * (u - v) ^ 2 + l⁻¹ * v ^ 2) :=
        ENNReal.ofReal_le_ofReal h1
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity)]


theorem enorm_sq_eq_ofReal (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem lintegral_sum_incr_enorm_sq [IsProbabilityMeasure P] {M : ℝ → Ω → ℝ}
    (hM : Martingale M ℱ P) (hM2 : ∀ t, MemLp (M t) 2 P) {a b : ℝ} (π : Partition a b)
    (ha : ∀ ω, M a ω = 0) :
    ∫⁻ ω, ∑ i : Fin π.n, ‖M (π.pt i.succ) ω - M (π.pt i.castSucc) ω‖ₑ ^ 2 ∂P =
      ∫⁻ ω, ‖M b ω‖ₑ ^ 2 ∂P := by
  have hi : ∀ i : Fin π.n, Integrable
      (fun ω => (M (π.pt i.succ) ω - M (π.pt i.castSucc) ω) ^ 2) P := fun i =>
    ((hM2 _).sub (hM2 _)).integrable_sq
  have hint : Integrable (fun ω => ∑ i : Fin π.n,
      (M (π.pt i.succ) ω - M (π.pt i.castSucc) ω) ^ 2) P := integrable_finsetSum _ fun i _ => hi i
  have h1 : ∀ ω, ∑ i : Fin π.n, ‖M (π.pt i.succ) ω - M (π.pt i.castSucc) ω‖ₑ ^ 2 =
      ENNReal.ofReal (∑ i : Fin π.n, (M (π.pt i.succ) ω - M (π.pt i.castSucc) ω) ^ 2) := by
    intro ω
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun i _ => enorm_sq_eq_ofReal _
  simp_rw [h1, enorm_sq_eq_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω =>
      Finset.sum_nonneg fun i _ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal (hM2 b).integrable_sq
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
  congr 1
  have := integral_sum_incr_sq_of_martingale hM hM2 π
  unfold Partition.sumIncrements at this
  rw [this]
  simp [ha]


theorem measurable_slice_of_joint {β : Type*} [MeasurableSpace β] {F : ℝ × Ω → β}
    (hF : Measurable F) (ω : Ω) : Measurable fun s : ℝ => F (s, ω) :=
  hF.comp measurable_prodMk_right

theorem measurable_sum_enorm_sq {Ψ Φ : ℝ → Ω → ι → ℝ} (hΨ : IsProgressive ℱ Ψ)
    (hΦ : IsProgressive ℱ Φ) :
    Measurable fun p : ℝ × Ω => ∑ k, ‖Ψ p.1 p.2 k - Φ p.1 p.2 k‖ₑ ^ 2 :=
  Finset.measurable_sum _ fun k _ =>
    (((measurable_uncurry_progressive (isProgressive_coord hΨ k)).sub
      (measurable_uncurry_progressive (isProgressive_coord hΦ k))).enorm).pow_const 2

theorem measurable_sum_enorm_sq' {Φ : ℝ → Ω → ι → ℝ} (hΦ : IsProgressive ℱ Φ) :
    Measurable fun p : ℝ × Ω => ∑ k, ‖Φ p.1 p.2 k‖ₑ ^ 2 :=
  Finset.measurable_sum _ fun k _ =>
    ((measurable_uncurry_progressive (isProgressive_coord hΦ k)).enorm).pow_const 2

theorem lintegral_enorm_qvProcess_sub_le [IsProbabilityMeasure P] {Ψ : ℝ → Ω → ι → ℝ}
    (hΨ : IsProgressiveL2 P ℱ Ψ) (hΦ : IsProgressiveL2 P ℱ Φ) (T : ℝ) {l : ℝ} (hl : 0 < l) :
    ∫⁻ ω, ‖qvProcess Ψ T ω - qvProcess Φ T ω‖ₑ ∂P ≤
      ENNReal.ofReal (1 + l) * sqIntegralOn P (fun s ω => Ψ s ω - Φ s ω) T +
        ENNReal.ofReal l⁻¹ * sqIntegralOn P Φ T := by
  set G : Ω → ℝ≥0∞ := fun ω => ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Ψ s ω k - Φ s ω k‖ₑ ^ 2 with hG
  set H : Ω → ℝ≥0∞ := fun ω => ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2 with hH
  have hGm : Measurable G :=
    (measurable_sum_enorm_sq hΨ.prog hΦ.prog).lintegral_prod_left' (μ := volume.restrict (Set.Icc 0 T))
  have hHm : Measurable H :=
    (measurable_sum_enorm_sq' hΦ.prog).lintegral_prod_left' (μ := volume.restrict (Set.Icc 0 T))
  have hpt : ∀ᵐ ω ∂P, ‖qvProcess Ψ T ω - qvProcess Φ T ω‖ₑ ≤
      ENNReal.ofReal (1 + l) * G ω + ENNReal.ofReal l⁻¹ * H ω := by
    filter_upwards [ae_integrableOn_sq hΨ.locL2, ae_integrableOn_sq hΦ.locL2] with ω h1 h2
    have e1 : qvProcess Ψ T ω - qvProcess Φ T ω =
        ∫ s in Set.Icc 0 T, ((∑ k, Ψ s ω k ^ 2) - ∑ k, Φ s ω k ^ 2) := by
      unfold qvProcess
      rw [integral_sub (h1 T) (h2 T)]
    rw [e1]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hmG : Measurable fun s => ∑ k, ‖Ψ s ω k - Φ s ω k‖ₑ ^ 2 :=
      measurable_slice_of_joint (measurable_sum_enorm_sq hΨ.prog hΦ.prog) ω
    calc ∫⁻ s in Set.Icc 0 T, ‖(∑ k, Ψ s ω k ^ 2) - ∑ k, Φ s ω k ^ 2‖ₑ
        ≤ ∫⁻ s in Set.Icc 0 T, (ENNReal.ofReal (1 + l) * ∑ k, ‖Ψ s ω k - Φ s ω k‖ₑ ^ 2 +
            ENNReal.ofReal l⁻¹ * ∑ k, ‖Φ s ω k‖ₑ ^ 2) := by
          refine lintegral_mono fun s => ?_
          rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          exact enorm_sq_sub_sq_le _ _ hl
      _ = ENNReal.ofReal (1 + l) * G ω + ENNReal.ofReal l⁻¹ * H ω := by
          rw [lintegral_add_left (hmG.const_mul _), lintegral_const_mul _ hmG,
            lintegral_const_mul]
          exact measurable_slice_of_joint (measurable_sum_enorm_sq' hΦ.prog) ω
  calc ∫⁻ ω, ‖qvProcess Ψ T ω - qvProcess Φ T ω‖ₑ ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (1 + l) * G ω + ENNReal.ofReal l⁻¹ * H ω) ∂P :=
        lintegral_mono_ae hpt
    _ = _ := by
        rw [lintegral_add_left (hGm.const_mul _), lintegral_const_mul _ hGm,
          lintegral_const_mul _ hHm]
        rfl


theorem lintegral_enorm_le_of_integral_sq [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : Integrable (fun ω => f ω ^ 2) P) {e : ℝ} (he : 0 < e) :
    ∫⁻ ω, ‖f ω‖ₑ ∂P ≤
      ENNReal.ofReal e + ENNReal.ofReal (1 / (4 * e)) * ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P) := by
  have hpt : ∀ x : ℝ, ‖x‖ₑ ≤ ENNReal.ofReal e + ENNReal.ofReal (1 / (4 * e)) * ‖x‖ₑ ^ 2 := by
    intro x
    rw [enorm_sq_eq_ofReal, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add he.le (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have key : 0 ≤ (|x| - 2 * e) ^ 2 / (4 * e) := by positivity
    have e2 : (|x| - 2 * e) ^ 2 / (4 * e) = e + 1 / (4 * e) * x ^ 2 - |x| := by
      rw [← sq_abs x]; field_simp; ring
    linarith
  calc ∫⁻ ω, ‖f ω‖ₑ ∂P ≤ ∫⁻ ω, (ENNReal.ofReal e +
        ENNReal.ofReal (1 / (4 * e)) * ‖f ω‖ₑ ^ 2) ∂P := lintegral_mono fun ω => hpt _
    _ = ENNReal.ofReal e + ENNReal.ofReal (1 / (4 * e)) * ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 2
        simp_rw [enorm_sq_eq_ofReal]
        exact (ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall fun ω =>
          sq_nonneg _)).symm


theorem measurable_sumIncrements_sq {X : ℝ → Ω → ℝ} (hX : ∀ t, Measurable (X t)) {a b : ℝ}
    (π : Partition a b) :
    Measurable fun ω => π.sumIncrements (fun s t => (X t ω - X s ω) ^ 2) :=
  Finset.measurable_sum _ fun i _ => ((hX _).sub (hX _)).pow_const 2

theorem lintegral_tendsto_sq_main [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ) {T : ℝ} (hT : 0 ≤ T)
    (π : ℕ → Partition 0 T) (hmesh : Tendsto (fun n => (π n).mesh) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ ω, ‖(π n).sumIncrements
      (fun s t => (itoIntegral P ℱ W Φ t ω - itoIntegral P ℱ W Φ s ω) ^ 2) -
        qvProcess Φ T ω‖ₑ ∂P) atTop (𝓝 0) := by
  set M := itoIntegral P ℱ W Φ with hMdef
  have hMm : Martingale M ℱ P := martingale_itoIntegral hW hΦ
  have hM2 : ∀ t, MemLp (M t) 2 P := memLp_two_itoIntegral hW hΦ
  have hM0 : ∀ ω, M 0 ω = 0 := fun ω => itoIntegral_of_nonpos P ℱ W Φ le_rfl ω
  have hMmeas : ∀ t, Measurable (M t) := fun t => (hMm.stronglyMeasurable t).measurable.mono (ℱ.le t) le_rfl
  obtain ⟨Ψ, hΨ⟩ := exists_simple_approx P ℱ Φ hΦ.prog T (hΦ.sq T)
  have happrox := (isItoIntegral_itoIntegral hW hΦ).approx T hT Ψ hΨ
  choose K hK0 hKb using fun m => simple_qv_L2 hW (Ψ m)
  have hIm : ∀ m, Martingale ((Ψ m).elemIntegral W) ℱ P := fun m =>
    SimpleIntegrand.martingale_elemIntegral hW (Ψ m)
  have hI2 : ∀ m t, MemLp ((Ψ m).elemIntegral W t) 2 P := fun m t =>
    SimpleIntegrand.memLp_elemIntegral hW (Ψ m) t 2 (by norm_num)
  have hImeas : ∀ m t, Measurable ((Ψ m).elemIntegral W t) := fun m t =>
    ((hIm m).stronglyMeasurable t).measurable.mono (ℱ.le t) le_rfl
  have hI0 : ∀ m ω, (Ψ m).elemIntegral W 0 ω = 0 := fun m ω =>
    SimpleIntegrand.elemIntegral_of_nonpos W (Ψ m) le_rfl ω
  have hAmeas : ∀ (Θ : ℝ → Ω → ι → ℝ), IsProgressive ℱ Θ → Measurable (qvProcess Θ T) :=
    fun Θ hΘ => (adapted_qvProcess hΘ T).mono (ℱ.le T) le_rfl
  set a' : ℝ≥0∞ := sqIntegralOn P Φ T with ha'
  have ha_eq : ∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂P = a' := lintegral_itoIntegral_sq hW hΦ T
  have ha'top : a' ≠ ∞ := (hΦ.sq T).ne
  -- the key inequality
  have key : ∀ (m n : ℕ) (l e : ℝ), 0 < l → 0 < e →
      ∫⁻ ω, ‖(π n).sumIncrements (fun s t => (M t ω - M s ω) ^ 2) - qvProcess Φ T ω‖ₑ ∂P ≤
        (ENNReal.ofReal (1 + l) * (∫⁻ ω, ‖(Ψ m).elemIntegral W T ω - M T ω‖ₑ ^ 2 ∂P +
          sqIntegralOn P (fun s ω => (Ψ m).toFun s ω - Φ s ω) T) +
          ENNReal.ofReal l⁻¹ * (a' + a')) +
        (ENNReal.ofReal e + ENNReal.ofReal (1 / (4 * e)) *
          ENNReal.ofReal (K m * (π n).mesh * T)) := by
    intro m n l e hl he
    set I := (Ψ m).elemIntegral W with hIdef
    set Sn : Ω → ℝ := fun ω => (π n).sumIncrements (fun s t => (M t ω - M s ω) ^ 2) with hSn
    set SI : Ω → ℝ := fun ω => (π n).sumIncrements (fun s t => (I t ω - I s ω) ^ 2) with hSI
    set Am : Ω → ℝ := qvProcess (Ψ m).toFun T with hAmdef
    set A : Ω → ℝ := qvProcess Φ T with hAdef
    have hSnm : Measurable Sn := measurable_sumIncrements_sq hMmeas _
    have hSIm : Measurable SI := measurable_sumIncrements_sq (hImeas m) _
    have hAm : Measurable Am := hAmeas _ (Ψ m).isProgressive_toFun
    have hA : Measurable A := hAmeas _ hΦ.prog
    -- (i)
    have hDm : Martingale (fun t ω => I t ω - M t ω) ℱ P := (hIm m).sub hMm
    have hD2 : ∀ t, MemLp (fun ω => I t ω - M t ω) 2 P := fun t => (hI2 m t).sub (hM2 t)
    have h1 : ∫⁻ ω, ‖SI ω - Sn ω‖ₑ ∂P ≤
        ENNReal.ofReal (1 + l) * ∫⁻ ω, ‖I T ω - M T ω‖ₑ ^ 2 ∂P + ENNReal.ofReal l⁻¹ * a' := by
      have hpt : ∀ ω, ‖SI ω - Sn ω‖ₑ ≤
          ENNReal.ofReal (1 + l) * ∑ i : Fin (π n).n, ‖(I ((π n).pt i.succ) ω - M ((π n).pt i.succ) ω) -
            (I ((π n).pt i.castSucc) ω - M ((π n).pt i.castSucc) ω)‖ₑ ^ 2 +
          ENNReal.ofReal l⁻¹ * ∑ i : Fin (π n).n,
            ‖M ((π n).pt i.succ) ω - M ((π n).pt i.castSucc) ω‖ₑ ^ 2 := by
        intro ω
        have e1 : SI ω - Sn ω = ∑ i : Fin (π n).n,
            ((I ((π n).pt i.succ) ω - I ((π n).pt i.castSucc) ω) ^ 2 -
              (M ((π n).pt i.succ) ω - M ((π n).pt i.castSucc) ω) ^ 2) := by
          simp only [hSI, hSn, Partition.sumIncrements, Finset.sum_sub_distrib]
        rw [e1]
        refine (enorm_sum_le _ _).trans ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => (enorm_sq_sub_sq_le _ _ hl).trans (le_of_eq ?_)
        congr 3
        ring
      have hmeasD : Measurable fun ω => ∑ i : Fin (π n).n, ‖(I ((π n).pt i.succ) ω - M ((π n).pt i.succ) ω) -
            (I ((π n).pt i.castSucc) ω - M ((π n).pt i.castSucc) ω)‖ₑ ^ 2 :=
        Finset.measurable_sum _ fun i _ =>
          ((((hImeas m _).sub (hMmeas _)).sub ((hImeas m _).sub (hMmeas _))).enorm).pow_const 2
      calc ∫⁻ ω, ‖SI ω - Sn ω‖ₑ ∂P
          ≤ ∫⁻ ω, (ENNReal.ofReal (1 + l) * ∑ i : Fin (π n).n,
              ‖(I ((π n).pt i.succ) ω - M ((π n).pt i.succ) ω) -
                (I ((π n).pt i.castSucc) ω - M ((π n).pt i.castSucc) ω)‖ₑ ^ 2 +
            ENNReal.ofReal l⁻¹ * ∑ i : Fin (π n).n,
              ‖M ((π n).pt i.succ) ω - M ((π n).pt i.castSucc) ω‖ₑ ^ 2) ∂P := lintegral_mono hpt
        _ = ENNReal.ofReal (1 + l) * ∫⁻ ω, ∑ i : Fin (π n).n,
              ‖(I ((π n).pt i.succ) ω - M ((π n).pt i.succ) ω) -
                (I ((π n).pt i.castSucc) ω - M ((π n).pt i.castSucc) ω)‖ₑ ^ 2 ∂P +
            ENNReal.ofReal l⁻¹ * ∫⁻ ω, ∑ i : Fin (π n).n,
              ‖M ((π n).pt i.succ) ω - M ((π n).pt i.castSucc) ω‖ₑ ^ 2 ∂P := by
          rw [lintegral_add_left (hmeasD.const_mul _), lintegral_const_mul _ hmeasD,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = _ := by
          rw [lintegral_sum_incr_enorm_sq (M := fun t ω => I t ω - M t ω) hDm hD2 (π n)
              (fun ω => by simp only [hM0 ω, sub_zero]; exact hI0 m ω),
            lintegral_sum_incr_enorm_sq hMm hM2 (π n) hM0, ha_eq]
    -- (ii)
    have h2 : ∫⁻ ω, ‖SI ω - Am ω‖ₑ ∂P ≤ ENNReal.ofReal e +
        ENNReal.ofReal (1 / (4 * e)) * ENNReal.ofReal (K m * (π n).mesh * T) := by
      obtain ⟨hmem, hint⟩ := hKb m T hT (π n)
      refine (lintegral_enorm_le_of_integral_sq (f := fun ω => SI ω - Am ω) hmem.integrable_sq he).trans ?_
      gcongr
    -- (iii)
    have h3 : ∫⁻ ω, ‖Am ω - A ω‖ₑ ∂P ≤
        ENNReal.ofReal (1 + l) * sqIntegralOn P (fun s ω => (Ψ m).toFun s ω - Φ s ω) T +
          ENNReal.ofReal l⁻¹ * a' :=
      lintegral_enorm_qvProcess_sub_le (IsProgressiveL2.simple P (Ψ m)) hΦ T hl
    have hpt : ∀ ω, ‖Sn ω - A ω‖ₑ ≤ ‖SI ω - Sn ω‖ₑ + ‖SI ω - Am ω‖ₑ + ‖Am ω - A ω‖ₑ := by
      intro ω
      calc ‖Sn ω - A ω‖ₑ = ‖(Sn ω - SI ω) + (SI ω - Am ω) + (Am ω - A ω)‖ₑ := by congr 1; ring
        _ ≤ ‖Sn ω - SI ω‖ₑ + ‖SI ω - Am ω‖ₑ + ‖Am ω - A ω‖ₑ := by
          refine (enorm_add_le _ _).trans ?_
          gcongr
          exact enorm_add_le _ _
        _ = _ := by rw [enorm_sub_rev (Sn ω)]
    calc ∫⁻ ω, ‖Sn ω - A ω‖ₑ ∂P
        ≤ ∫⁻ ω, (‖SI ω - Sn ω‖ₑ + ‖SI ω - Am ω‖ₑ + ‖Am ω - A ω‖ₑ) ∂P := lintegral_mono hpt
      _ = ∫⁻ ω, ‖SI ω - Sn ω‖ₑ ∂P + ∫⁻ ω, ‖SI ω - Am ω‖ₑ ∂P + ∫⁻ ω, ‖Am ω - A ω‖ₑ ∂P := by
          have hm2 : Measurable fun ω => ‖SI ω - Sn ω‖ₑ := (hSIm.sub hSnm).enorm
          have hm1 : Measurable fun ω => ‖SI ω - Sn ω‖ₑ + ‖SI ω - Am ω‖ₑ :=
            hm2.add (hSIm.sub hAm).enorm
          rw [lintegral_add_left hm1, lintegral_add_left hm2]
      _ ≤ (ENNReal.ofReal (1 + l) * ∫⁻ ω, ‖I T ω - M T ω‖ₑ ^ 2 ∂P + ENNReal.ofReal l⁻¹ * a') +
          (ENNReal.ofReal e + ENNReal.ofReal (1 / (4 * e)) * ENNReal.ofReal (K m * (π n).mesh * T)) +
          (ENNReal.ofReal (1 + l) * sqIntegralOn P (fun s ω => (Ψ m).toFun s ω - Φ s ω) T +
            ENNReal.ofReal l⁻¹ * a') := by gcongr
      _ = _ := by ring
  have hd : Tendsto (fun m => ∫⁻ ω, ‖(Ψ m).elemIntegral W T ω - M T ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) :=
    happrox
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ∞ with rfl | hηtop
  · exact Filter.Eventually.of_forall fun _ => le_top
  have hηpos : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  set e : ℝ := η.toReal / 4 with hedef
  have he : 0 < e := by positivity
  have h4e : ENNReal.ofReal e + ENNReal.ofReal e + (ENNReal.ofReal e + ENNReal.ofReal e) ≤ η := by
    have : ENNReal.ofReal e + ENNReal.ofReal e + (ENNReal.ofReal e + ENNReal.ofReal e) =
        ENNReal.ofReal (4 * e) := by
      rw [← ENNReal.ofReal_add he.le he.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring
    rw [this, hedef, show 4 * (η.toReal / 4) = η.toReal by ring, ENNReal.ofReal_toReal hηtop]
  set l : ℝ := (a' + a').toReal / e + 1 with hldef
  have hl : 0 < l := by positivity
  have hY : ENNReal.ofReal l⁻¹ * (a' + a') ≤ ENNReal.ofReal e := by
    have hS : a' + a' = ENNReal.ofReal (a' + a').toReal :=
      (ENNReal.ofReal_toReal (ENNReal.add_ne_top.2 ⟨ha'top, ha'top⟩)).symm
    rw [hS, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_mul_le_iff₀ hl]
    have : (a' + a').toReal / e * e = (a' + a').toReal := by field_simp
    nlinarith
  have hX : ∀ᶠ m in atTop, ENNReal.ofReal (1 + l) *
      (∫⁻ ω, ‖(Ψ m).elemIntegral W T ω - M T ω‖ₑ ^ 2 ∂P +
        sqIntegralOn P (fun s ω => (Ψ m).toFun s ω - Φ s ω) T) ≤ ENNReal.ofReal e := by
    have h0 : Tendsto (fun m => ENNReal.ofReal (1 + l) *
        (∫⁻ ω, ‖(Ψ m).elemIntegral W T ω - M T ω‖ₑ ^ 2 ∂P +
          sqIntegralOn P (fun s ω => (Ψ m).toFun s ω - Φ s ω) T)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (hd.add hΨ) (Or.inr (ENNReal.ofReal_ne_top (r := 1 + l)))
      simpa using this
    exact ENNReal.tendsto_nhds_zero.1 h0 _ (ENNReal.ofReal_pos.2 he)
  obtain ⟨m, hm⟩ := hX.exists
  have hZ : ∀ᶠ n in atTop, ENNReal.ofReal (1 / (4 * e)) *
      ENNReal.ofReal (K m * (π n).mesh * T) ≤ ENNReal.ofReal e := by
    have h0 : Tendsto (fun n => ENNReal.ofReal (1 / (4 * e)) *
        ENNReal.ofReal (K m * (π n).mesh * T)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => K m * (π n).mesh * T) atTop (𝓝 0) := by
        simpa using (hmesh.const_mul (K m)).mul_const T
      have h2 := ENNReal.tendsto_ofReal h1
      rw [ENNReal.ofReal_zero] at h2
      have := ENNReal.Tendsto.const_mul h2 (Or.inr (ENNReal.ofReal_ne_top (r := 1 / (4 * e))))
      simpa using this
    exact ENNReal.tendsto_nhds_zero.1 h0 _ (ENNReal.ofReal_pos.2 he)
  filter_upwards [hZ] with n hn
  refine (key m n l e hl he).trans ?_
  refine le_trans ?_ h4e
  gcongr


/-- Quadratic variation along partitions, in probability: for partitions `π n` of `[0, T]` with
mesh `→ 0`, `∑_i (M_{t_{i+1}} - M_{t_i})² → ∫_0^T ∑_k |Φ^k|²` in probability. -/
theorem tendstoInMeasure_sumIncrements_sq [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ) {T : ℝ} (hT : 0 ≤ T)
    (π : ℕ → Partition 0 T) (hmesh : Tendsto (fun n => (π n).mesh) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => (π n).sumIncrements
      (fun s t => (itoIntegral P ℱ W Φ t ω - itoIntegral P ℱ W Φ s ω) ^ 2)) atTop
      (qvProcess Φ T) := by
  refine tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero ?_
  have hMmeas : ∀ t, Measurable (itoIntegral P ℱ W Φ t) := fun t =>
    (adapted_itoIntegral P ℱ W Φ t).mono (ℱ.le t) le_rfl
  have hfun : (fun n => eLpNorm ((fun ω => (π n).sumIncrements
      (fun s t => (itoIntegral P ℱ W Φ t ω - itoIntegral P ℱ W Φ s ω) ^ 2)) - qvProcess Φ T) 1 P) =
      fun n => ∫⁻ ω, ‖(π n).sumIncrements
        (fun s t => (itoIntegral P ℱ W Φ t ω - itoIntegral P ℱ W Φ s ω) ^ 2) -
          qvProcess Φ T ω‖ₑ ∂P := by
    funext n
    exact eLpNorm_one_eq_lintegral_enorm
      (((measurable_sumIncrements_sq hMmeas (π n)).sub
        ((adapted_qvProcess hΦ.prog T).mono (ℱ.le T) le_rfl)).aestronglyMeasurable)
  rw [hfun]
  exact lintegral_tendsto_sq_main hW hΦ hT π hmesh

/-- Covariation along partitions, in probability. -/
theorem tendstoInMeasure_sumIncrements_mul [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ) (hΦ' : IsProgressiveL2 P ℱ Φ')
    {T : ℝ} (hT : 0 ≤ T) (π : ℕ → Partition 0 T)
    (hmesh : Tendsto (fun n => (π n).mesh) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => (π n).sumIncrements
      (fun s t => (itoIntegral P ℱ W Φ t ω - itoIntegral P ℱ W Φ s ω) *
        (itoIntegral P ℱ W Φ' t ω - itoIntegral P ℱ W Φ' s ω))) atTop
      (covProcess Φ Φ' T) := by
  have hp := hΦ.add hΦ'
  have hm := hΦ.add (hΦ'.smul (-1))
  have L₁ := lintegral_tendsto_sq_main hW hp hT π hmesh
  have L₂ := lintegral_tendsto_sq_main hW hm hT π hmesh
  set M := itoIntegral P ℱ W Φ with hMdef
  set M' := itoIntegral P ℱ W Φ' with hM'def
  have hMmeas : ∀ t, Measurable (M t) := fun t => (adapted_itoIntegral P ℱ W Φ t).mono (ℱ.le t) le_rfl
  have hM'meas : ∀ t, Measurable (M' t) := fun t =>
    (adapted_itoIntegral P ℱ W Φ' t).mono (ℱ.le t) le_rfl
  have hmeasS : ∀ (Θ : ℝ → Ω → ι → ℝ) (n : ℕ), Measurable fun ω => (π n).sumIncrements
      (fun s t => (itoIntegral P ℱ W Θ t ω - itoIntegral P ℱ W Θ s ω) ^ 2) := fun Θ n =>
    measurable_sumIncrements_sq (fun t => (adapted_itoIntegral P ℱ W Θ t).mono (ℱ.le t) le_rfl) _
  have hmeasA : ∀ Θ : ℝ → Ω → ι → ℝ, IsProgressive ℱ Θ → Measurable (qvProcess Θ T) :=
    fun Θ hΘ => (adapted_qvProcess hΘ T).mono (ℱ.le T) le_rfl
  have hmeasC : ∀ n, Measurable fun ω => (π n).sumIncrements
      (fun s t => (M t ω - M s ω) * (M' t ω - M' s ω)) := fun n =>
    Finset.measurable_sum _ fun i _ => ((hMmeas _).sub (hMmeas _)).mul ((hM'meas _).sub (hM'meas _))
  have hmeasCov : Measurable (covProcess Φ Φ' T) :=
    (adapted_covProcess hΦ.prog hΦ'.prog T).mono (ℱ.le T) le_rfl
  refine tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero ?_
  have hfun : (fun n => eLpNorm ((fun ω => (π n).sumIncrements
      (fun s t => (M t ω - M s ω) * (M' t ω - M' s ω))) - covProcess Φ Φ' T) 1 P) =
      fun n => ∫⁻ ω, ‖(π n).sumIncrements
        (fun s t => (M t ω - M s ω) * (M' t ω - M' s ω)) - covProcess Φ Φ' T ω‖ₑ ∂P := by
    funext n
    exact eLpNorm_one_eq_lintegral_enorm ((hmeasC n).sub hmeasCov).aestronglyMeasurable
  rw [hfun]
  have hupper : Tendsto (fun n => ENNReal.ofReal (1 / 4) *
      (∫⁻ ω, ‖(π n).sumIncrements
        (fun s t => (itoIntegral P ℱ W (fun s ω => Φ s ω + Φ' s ω) t ω -
          itoIntegral P ℱ W (fun s ω => Φ s ω + Φ' s ω) s ω) ^ 2) -
          qvProcess (fun s ω => Φ s ω + Φ' s ω) T ω‖ₑ ∂P +
       ∫⁻ ω, ‖(π n).sumIncrements
        (fun s t => (itoIntegral P ℱ W (fun s ω => Φ s ω + (-1 : ℝ) • Φ' s ω) t ω -
          itoIntegral P ℱ W (fun s ω => Φ s ω + (-1 : ℝ) • Φ' s ω) s ω) ^ 2) -
          qvProcess (fun s ω => Φ s ω + (-1 : ℝ) • Φ' s ω) T ω‖ₑ ∂P)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (L₁.add L₂) (Or.inr (ENNReal.ofReal_ne_top (r := 1 / 4)))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => zero_le) (fun n => ?_)
  have hpt : ∀ᵐ ω ∂P, ‖(π n).sumIncrements (fun s t => (M t ω - M s ω) * (M' t ω - M' s ω)) -
      covProcess Φ Φ' T ω‖ₑ ≤ ENNReal.ofReal (1 / 4) *
      (‖(π n).sumIncrements
        (fun s t => (itoIntegral P ℱ W (fun s ω => Φ s ω + Φ' s ω) t ω -
          itoIntegral P ℱ W (fun s ω => Φ s ω + Φ' s ω) s ω) ^ 2) -
          qvProcess (fun s ω => Φ s ω + Φ' s ω) T ω‖ₑ +
       ‖(π n).sumIncrements
        (fun s t => (itoIntegral P ℱ W (fun s ω => Φ s ω + (-1 : ℝ) • Φ' s ω) t ω -
          itoIntegral P ℱ W (fun s ω => Φ s ω + (-1 : ℝ) • Φ' s ω) s ω) ^ 2) -
          qvProcess (fun s ω => Φ s ω + (-1 : ℝ) • Φ' s ω) T ω‖ₑ) := by
    filter_upwards [itoIntegral_add hW hΦ (hΦ'.smul (-1)), itoIntegral_add hW hΦ hΦ',
      itoIntegral_smul hW hΦ' (-1), qvProcess_add_sub_ae hΦ hΦ' T] with ω a1 a2 a3 a4
    have b1 : ∀ t, itoIntegral P ℱ W (fun s ω => Φ s ω + (-1 : ℝ) • Φ' s ω) t ω =
        M t ω - M' t ω := fun t => by rw [a1 t, a3 t]; ring
    have b2 : ∀ t, itoIntegral P ℱ W (fun s ω => Φ s ω + Φ' s ω) t ω = M t ω + M' t ω := a2
    have hs : (π n).sumIncrements (fun s t => (M t ω - M s ω) * (M' t ω - M' s ω)) =
        (1 / 4) * ((π n).sumIncrements (fun s t => ((M t ω + M' t ω) - (M s ω + M' s ω)) ^ 2) -
          (π n).sumIncrements (fun s t => ((M t ω - M' t ω) - (M s ω - M' s ω)) ^ 2)) := by
      unfold Partition.sumIncrements
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have key : (π n).sumIncrements (fun s t => (M t ω - M s ω) * (M' t ω - M' s ω)) -
        covProcess Φ Φ' T ω =
        (1 / 4) * (((π n).sumIncrements (fun s t => (itoIntegral P ℱ W
            (fun s ω => Φ s ω + Φ' s ω) t ω - itoIntegral P ℱ W
            (fun s ω => Φ s ω + Φ' s ω) s ω) ^ 2) -
          qvProcess (fun s ω => Φ s ω + Φ' s ω) T ω) -
          ((π n).sumIncrements (fun s t => (itoIntegral P ℱ W
            (fun s ω => Φ s ω + (-1 : ℝ) • Φ' s ω) t ω - itoIntegral P ℱ W
            (fun s ω => Φ s ω + (-1 : ℝ) • Φ' s ω) s ω) ^ 2) -
          qvProcess (fun s ω => Φ s ω + (-1 : ℝ) • Φ' s ω) T ω)) := by
      simp only [b1, b2]
      rw [hs]
      linear_combination (1 / 4 : ℝ) * a4
    rw [key, enorm_mul, Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    gcongr
    exact enorm_sub_le
  have hmu : Measurable fun ω => ‖(π n).sumIncrements
        (fun s t => (itoIntegral P ℱ W (fun s ω => Φ s ω + Φ' s ω) t ω -
          itoIntegral P ℱ W (fun s ω => Φ s ω + Φ' s ω) s ω) ^ 2) -
          qvProcess (fun s ω => Φ s ω + Φ' s ω) T ω‖ₑ :=
    ((hmeasS _ n).sub (hmeasA _ hp.prog)).enorm
  calc ∫⁻ ω, ‖(π n).sumIncrements (fun s t => (M t ω - M s ω) * (M' t ω - M' s ω)) -
        covProcess Φ Φ' T ω‖ₑ ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (1 / 4) *
        (‖(π n).sumIncrements
          (fun s t => (itoIntegral P ℱ W (fun s ω => Φ s ω + Φ' s ω) t ω -
            itoIntegral P ℱ W (fun s ω => Φ s ω + Φ' s ω) s ω) ^ 2) -
            qvProcess (fun s ω => Φ s ω + Φ' s ω) T ω‖ₑ +
         ‖(π n).sumIncrements
          (fun s t => (itoIntegral P ℱ W (fun s ω => Φ s ω + (-1 : ℝ) • Φ' s ω) t ω -
            itoIntegral P ℱ W (fun s ω => Φ s ω + (-1 : ℝ) • Φ' s ω) s ω) ^ 2) -
            qvProcess (fun s ω => Φ s ω + (-1 : ℝ) • Φ' s ω) T ω‖ₑ) ∂P := lintegral_mono_ae hpt
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hmu]

end Scalar

/-! ### Vector-valued integrals and `IsVectorMartingaleWithCovariation` -/

section Vector

variable {p : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

/-- The `ℝ^p`-valued process `(∫ Φ^a · dW)_{a < p}`. -/
def vectorItoIntegral (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : Fin p → ℝ → Ω → ι → ℝ) : ℝ → Ω → (ℝ^p) :=
  fun t ω => WithLp.toLp 2 fun a => itoIntegral P ℱ W (Φ a) t ω

/-- The covariation density `Σ^{ab}_s = ∑_k Φ^{a,k}_s Φ^{b,k}_s` (a Gram matrix, hence symmetric
positive semidefinite). -/
def covMatrixProcess (Φ : Fin p → ℝ → Ω → ι → ℝ) : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ :=
  fun s ω => Matrix.of fun a b => ∑ k, Φ a s ω k * Φ b s ω k

theorem sum_prod_eq_trace {p : ℕ} (M N : Matrix (Fin p) (Fin p) ℝ) :
    ∑ x : Fin p × Fin p, M x.1 x.2 * N x.1 x.2 = (M.transpose * N).trace := by
  rw [Fintype.sum_prod_type, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem covMatrixProcess_posSemidef (Φ : Fin p → ℝ → Ω → ι → ℝ) (s : ℝ) (ω : Ω) :
    (covMatrixProcess Φ s ω).PosSemidef := by
  have := Matrix.posSemidef_self_mul_conjTranspose
    (Matrix.of fun (a : Fin p) (k : ι) => Φ a s ω k)
  convert this using 1
  ext a b
  simp [covMatrixProcess, Matrix.mul_apply]

/-- For a positive semidefinite matrix the variational trace norm of `HRS/Prob/Metrics.lean`
equals the trace (ISSUES §C.5; the lemma belongs to METR-03 and is restated here because
`sigma_int` below needs it). -/
theorem traceNormMatrix_eq_trace_of_posSemidef (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : Q.PosSemidef) :
    traceNormMatrix Q = Matrix.trace Q := by
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin p) (Fin p) ℝ, Q = B.transpose * B := by
    obtain ⟨a, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.nonneg
    exact ⟨a, by simp [Matrix.star_eq_conjTranspose]⟩
  have hQt : Q.transpose = Q := by rw [hB]; simp
  have hS : 0 ≤ Matrix.trace Q := by
    rw [hB, ← sum_prod_eq_trace]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hle : ∀ U : Matrix.orthogonalGroup (Fin p) ℝ,
      Matrix.trace (Q.transpose * (U : Matrix (Fin p) (Fin p) ℝ)) ≤ Matrix.trace Q := by
    intro U
    have hU : (U : Matrix (Fin p) (Fin p) ℝ) * (U : Matrix (Fin p) (Fin p) ℝ).transpose = 1 :=
      (Matrix.mem_orthogonalGroup_iff _ _).1 U.2
    set C := B * (U : Matrix (Fin p) (Fin p) ℝ) with hC
    have h1 : Matrix.trace (Q.transpose * (U : Matrix (Fin p) (Fin p) ℝ)) =
        ∑ x : Fin p × Fin p, B x.1 x.2 * C x.1 x.2 := by
      rw [sum_prod_eq_trace, hQt, hB, hC, Matrix.mul_assoc]
    have h2 : ∑ x : Fin p × Fin p, C x.1 x.2 * C x.1 x.2 = Matrix.trace Q := by
      rw [sum_prod_eq_trace, hC, Matrix.transpose_mul]
      rw [show (U : Matrix (Fin p) (Fin p) ℝ).transpose * B.transpose * (B * U) =
          (U : Matrix (Fin p) (Fin p) ℝ).transpose * (B.transpose * B) * U by simp only [Matrix.mul_assoc]]
      rw [← hB, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hU, Matrix.mul_one]
    have h3 : ∑ x : Fin p × Fin p, B x.1 x.2 * B x.1 x.2 = Matrix.trace Q := by
      rw [sum_prod_eq_trace, hB]
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x : Fin p × Fin p => B x.1 x.2)
      (fun x => C x.1 x.2)
    rw [← h1] at cs
    simp only [← pow_two] at h2 h3
    rw [h2, h3] at cs
    nlinarith
  have hbdd : BddAbove (Set.range fun U : Matrix.orthogonalGroup (Fin p) ℝ =>
      Matrix.trace (Q.transpose * (U : Matrix (Fin p) (Fin p) ℝ))) :=
    ⟨Matrix.trace Q, by rintro _ ⟨U, rfl⟩; exact hle U⟩
  apply le_antisymm
  · exact ciSup_le hle
  · have := le_ciSup hbdd (1 : Matrix.orthogonalGroup (Fin p) ℝ)
    rw [traceNormMatrix]
    simpa [hQt] using this

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}

/-- The vector of Itô integrals is an `ℝ^p`-valued continuous `L²` martingale with absolutely
continuous covariation `[M^a, M^b]_t = ∫_0^t Σ^{ab}_s ds`, `Σ = covMatrixProcess Φ`, in the exact
sense of `HRS.IsVectorMartingaleWithCovariation` (Lemma A.21's hypothesis, M L10546-10547; the
particle martingales `M_N[f]`, M L1657, L6572-6575). -/
theorem vectorItoIntegral_isVectorMartingaleWithCovariation [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W) (Φ : Fin p → ℝ → Ω → ι → ℝ)
    (hΦ : ∀ a, IsProgressiveL2 P ℱ (Φ a)) (T : ℝ) :
    IsVectorMartingaleWithCovariation P ℱ T (vectorItoIntegral P ℱ W Φ) (covMatrixProcess Φ) := by
  have hpt : ∀ σ ω, s1Norm (covMatrixProcess Φ σ ω) = ∑ a, ∑ k, Φ a σ ω k ^ 2 := by
    intro σ ω
    unfold s1Norm
    rw [traceNormMatrix_eq_trace_of_posSemidef _ (covMatrixProcess_posSemidef Φ σ ω)]
    simp [Matrix.trace, covMatrixProcess, sq]
  refine ⟨fun a => martingale_itoIntegral hW (hΦ a), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun ω => by
      ext a; simp [vectorItoIntegral, itoIntegral_of_nonpos P ℱ W _ (le_refl (0 : ℝ))]
  · refine Filter.Eventually.of_forall fun ω => Continuous.continuousOn ?_
    exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun a => continuous_itoIntegral P ℱ W (Φ a) ω)
  · intro τ _
    exact memLp_piLp_iff.2 fun a => memLp_two_itoIntegral hW (hΦ a) τ
  · refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
    exact Finset.measurable_sum _ fun k _ =>
      (measurable_uncurry_progressive (isProgressive_coord (hΦ a).prog k)).mul
        (measurable_uncurry_progressive (isProgressive_coord (hΦ b).prog k))
  · intro σ
    letI : MeasurableSpace Ω := ℱ σ
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
    exact (isProgressive_sum_mul (hΦ a).prog (hΦ b).prog).adapted σ
  · exact Filter.Eventually.of_forall fun ω σ _ => covMatrixProcess_posSemidef Φ σ ω
  · have hint : Integrable (fun ω => ∑ a, qvProcess (Φ a) T ω) P :=
      integrable_finsetSum _ fun a _ => integrable_qvProcess (hΦ a) T
    refine hint.congr ?_
    filter_upwards [ae_all_iff.2 fun a => ae_integrableOn_sq (hΦ a).locL2] with ω hω
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun a _ => hω a T)]
    rfl
  · filter_upwards [ae_all_iff.2 fun a => ae_integrableOn_sq (hΦ a).locL2] with ω hω
    simp_rw [hpt]
    exact integrable_finsetSum _ fun a _ => hω a T
  · filter_upwards [ae_all_iff.2 fun a => ae_all_iff.2 fun b =>
      ae_integrableOn_mul (hΦ a).locL2 (hΦ b).locL2] with ω hω a b
    exact hω a b T
  · intro a b
    exact martingale_itoIntegral_mul_sub hW (hΦ a) (hΦ b)

end Vector

end HRS
