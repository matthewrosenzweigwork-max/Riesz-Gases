import HRS.Main.A8PAux1

/-!
# Packet A9, part 3: the Hilbert-parametrised shift bound (Lemma A.27 for `X : Ω → H`, `ι : ℝ^p → H`)

`a9_shift_H`: for a vector martingale `M ∈ ℝ^p` with covariation `Σ`, a deterministic covariance density `Σ̄`,
a linear contraction `ι : ℝ^p → H` into a Hilbert space, an `ℱ_0`-measurable `X : Ω → H` and `Φ ∈ C_b²(H)`,
`|E Φ(X + ι M_T) - E f(X)| ≤ ½ E ∫ ‖Σ-Σ̄‖_{S₁}` with `f(x) = ∫ Φ(x + ι z) dN(0,∫Σ̄)(z)`.
Proof: `ℱ_0`-simple approximation of `X` and the fibrewise `const_shift_bound`, exactly as `shift_bound_f`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.Main.A8P

section UnitBall

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem a9_cbUnit_deriv_le {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 2) {j : ℕ} (hj : j ≤ 2) (x : B) :
    ‖iteratedFDeriv ℝ j Φ x‖ ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := hΦ
  have hbdd := h2 j hj
  have hle : ‖iteratedFDeriv ℝ j Φ x‖ ≤ ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖ :=
    le_ciSup (f := fun z : B => ‖iteratedFDeriv ℝ j Φ z‖) hbdd x
  refine hle.trans (le_trans ?_ h3)
  unfold cbNorm
  have hnn : ∀ i ∈ Finset.range 3, 0 ≤ ⨆ z : B, ‖iteratedFDeriv ℝ i Φ z‖ :=
    fun i _ => Real.iSup_nonneg fun z => norm_nonneg _
  exact Finset.single_le_sum hnn (Finset.mem_range.2 (by omega))

theorem a9_cbUnit_bdd {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 2) (x : B) : |Φ x| ≤ 1 := by
  have := a9_cbUnit_deriv_le hΦ (j := 0) (by norm_num) x
  simpa [norm_iteratedFDeriv_zero] using this

theorem a9_cbUnit_lip {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 2) (x y : B) :
    |Φ x - Φ y| ≤ ‖x - y‖ := by
  have hd : Differentiable ℝ Φ := hΦ.1.differentiable (by norm_num)
  have h1 : ∀ z, ‖fderiv ℝ Φ z‖ ≤ 1 := fun z => by
    rw [← norm_iteratedFDeriv_one]; exact a9_cbUnit_deriv_le hΦ (by norm_num) z
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := Φ) (s := Set.univ)
    (fun z _ => hd z) (fun z _ => h1 z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using this

theorem a9_cbUnit_translate {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 2) (x : B) :
    (fun y => Φ (x + y)) ∈ CbUnitBall B 2 := by
  have hΦ' := hΦ
  obtain ⟨h1, h2, h3⟩ := hΦ
  have hb : ∀ (j : ℕ) (y : B), iteratedFDeriv ℝ j (fun y => Φ (x + y)) y =
      iteratedFDeriv ℝ j Φ (x + y) := fun j y => iteratedFDeriv_comp_add_left j x y
  refine ⟨h1.comp (contDiff_const.add contDiff_id), fun j hj => ?_, ?_⟩
  · obtain ⟨C, hC⟩ := h2 j hj
    exact ⟨C, by
      rintro _ ⟨y, rfl⟩
      show ‖iteratedFDeriv ℝ j (fun y => Φ (x + y)) y‖ ≤ C
      rw [hb]; exact hC ⟨x + y, rfl⟩⟩
  · refine le_trans ?_ h3
    unfold cbNorm
    refine Finset.sum_le_sum fun j hj => ?_
    have hjk : j ≤ 2 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have : Nonempty B := ⟨0⟩
    refine ciSup_le fun y => ?_
    show ‖iteratedFDeriv ℝ j (fun y => Φ (x + y)) y‖ ≤ _
    rw [hb]
    exact le_ciSup (f := fun z : B => ‖iteratedFDeriv ℝ j Φ z‖) (h2 j hjk) (x + y)

end UnitBall

section Shift

variable {p : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- the fibrewise estimate for a finite-range `ℱ_0`-measurable `ξ`. -/
theorem a9_shift_H_simple (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsb : IsDetCovMatrix T sb)
    (ι : (ℝ^p) →L[ℝ] H) (hι : ‖ι‖ ≤ 1)
    (ξ : Ω → H) (S : Finset H) (hS : ∀ ω, ξ ω ∈ S) (hξ : ∀ x, MeasurableSet[ℱ 0] (ξ ⁻¹' {x}))
    (Φ : H → ℝ) (hΦ : Φ ∈ CbUnitBall H 2) (f : H → ℝ) (hfc : Continuous f)
    (hfb : ∀ x, |f x| ≤ 1)
    (hf : ∀ x, f x = ∫ z, Φ (x + ι z) ∂(multivariateGaussian 0 (integratedCov T sb))) :
    |(∫ ω, Φ (ξ ω + ι (M T ω)) ∂P) - ∫ ω, f (ξ ω) ∂P| ≤
      (1 / 2) * ∫ ω, (∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ)) ∂P := by
  classical
  have hm0 : ∀ B, MeasurableSet[ℱ 0] B → MeasurableSet B := fun B hB => ℱ.le 0 _ hB
  have hξm : ∀ x, MeasurableSet (ξ ⁻¹' {x}) := fun x => hm0 _ (hξ x)
  have hξmeas : Measurable ξ := by
    intro s _
    have : ξ ⁻¹' s = ⋃ x ∈ (S.filter (· ∈ s)), ξ ⁻¹' {x} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop,
        Finset.mem_filter]
      exact ⟨fun h => ⟨ξ ω, ⟨hS ω, h⟩, rfl⟩, fun ⟨x, ⟨_, hx⟩, e⟩ => e ▸ hx⟩
    rw [this]
    exact Finset.measurableSet_biUnion _ fun x _ => hξm x
  have hMt : AEMeasurable (M T) P :=
    (hM.sq_int T ⟨hT, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hιm : Measurable ι := ι.continuous.measurable
  have hint1 : Integrable (fun ω => Φ (ξ ω + ι (M T ω))) P :=
    Integrable.of_bound (C := 1)
      (hΦc.measurable.comp_aemeasurable (hξmeas.aemeasurable.add (hιm.comp_aemeasurable hMt))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa using a9_cbUnit_bdd hΦ _)
  have hint2 : Integrable (fun ω => f (ξ ω)) P :=
    Integrable.of_bound (C := 1) (hfc.measurable.comp hξmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa using hfb (ξ ω))
  have hintg : Integrable (fun ω => ∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ)) P :=
    LindebergAux.Iblk_integrable P ℱ hM hsb.meas hsb.int le_rfl le_rfl
  have hA : MeasurableSet[ℱ 0] (Set.univ : Set Ω) := MeasurableSet.univ
  have fs1 := setIntegral_fiber_sum P (A := Set.univ) MeasurableSet.univ S ξ hS hξm hint1
  have fs2 := setIntegral_fiber_sum P (A := Set.univ) MeasurableSet.univ S ξ hS hξm hint2
  have fs3 := setIntegral_fiber_sum P (A := Set.univ) MeasurableSet.univ S ξ hS hξm hintg
  simp only [Measure.restrict_univ, Set.univ_inter] at fs1 fs2 fs3
  rw [fs1, fs2, fs3, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  have hB : MeasurableSet[ℱ 0] (ξ ⁻¹' {x}) := hξ x
  have hBm := hm0 _ hB
  set h : (ℝ^p) → ℝ := fun z => Φ (x + ι z) with hh
  have hhmem : h ∈ CbUnitBall (ℝ^p) 2 := cbUnitBall_comp_clm ι hι (a9_cbUnit_translate hΦ x)
  have e1 : ∫ ω in ξ ⁻¹' {x}, Φ (ξ ω + ι (M T ω)) ∂P = ∫ ω in ξ ⁻¹' {x}, h (0 + M T ω) ∂P :=
    setIntegral_congr_fun hBm fun ω hω => by
      rw [show ξ ω = x from hω]; simp [hh]
  have e2 : ∫ ω in ξ ⁻¹' {x}, f (ξ ω) ∂P = P.real (ξ ⁻¹' {x}) * f x := by
    rw [setIntegral_congr_fun hBm (g := fun _ => f x) fun ω hω => by rw [show ξ ω = x from hω],
      setIntegral_const, smul_eq_mul]
  rw [e1, e2, hf x]
  have := const_shift_bound P ℱ T hT M Sg hM sb hsb h (A8P.a8p_cbUnit_memCb hhmem) 0 hB
  simp only [zero_add] at this ⊢
  refine this.trans ?_
  have h1 : hessSup h ≤ 1 := A8P.a8p_cbUnit_hess hhmem
  have h0 : 0 ≤ ∫ ω in ξ ⁻¹' {x}, (∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ)) ∂P :=
    setIntegral_nonneg hBm fun ω _ => setIntegral_nonneg measurableSet_Icc fun σ _ =>
      traceNormMatrix_nonneg _
  nlinarith


omit [IsProbabilityMeasure P] in
theorem a9_exists_finrange_approx {m : MeasurableSpace Ω} {X : Ω → H} (hX : Measurable[m] X) :
    ∃ (ξ : ℕ → Ω → H) (S : ℕ → Finset H), (∀ n ω, ξ n ω ∈ S n) ∧
      (∀ n x, MeasurableSet[m] (ξ n ⁻¹' {x})) ∧
      ∀ ω, Tendsto (fun n => ξ n ω) atTop (𝓝 (X ω)) := by
  classical
  have hXs : StronglyMeasurable[m] X := hX.stronglyMeasurable
  exact ⟨fun n => hXs.approx n, fun n => (hXs.approx n).range,
    fun n ω => SimpleFunc.mem_range_self _ ω, fun n x => (hXs.approx n).measurableSet_fiber x,
    fun ω => hXs.tendsto_approx ω⟩

theorem a9_shift_H (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsb : IsDetCovMatrix T sb)
    (ι : (ℝ^p) →L[ℝ] H) (hι : ‖ι‖ ≤ 1)
    (X : Ω → H) (hX : Measurable[ℱ 0] X)
    (Φ : H → ℝ) (hΦ : Φ ∈ CbUnitBall H 2) (f : H → ℝ)
    (hf : ∀ x, f x = ∫ z, Φ (x + ι z) ∂(multivariateGaussian 0 (integratedCov T sb))) :
    |(∫ ω, Φ (X ω + ι (M T ω)) ∂P) - ∫ ω, f (X ω) ∂P| ≤
      (1 / 2) * ∫ ω, (∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ)) ∂P := by
  classical
  set γ : Measure (ℝ^p) := multivariateGaussian 0 (integratedCov T sb) with hγ
  haveI : IsProbabilityMeasure γ := inferInstance
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hfi : ∀ w : H, Integrable (fun z => Φ (w + ι z)) γ := fun w =>
    Integrable.of_bound (C := 1)
      (hΦc.comp (continuous_const.add ι.continuous)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simpa using a9_cbUnit_bdd hΦ (w + ι z))
  have hflip : ∀ x y, |f x - f y| ≤ ‖x - y‖ := fun x y => by
    rw [hf x, hf y, ← integral_sub (hfi x) (hfi y)]
    have : ∀ z, |Φ (x + ι z) - Φ (y + ι z)| ≤ ‖x - y‖ := fun z => by
      have := a9_cbUnit_lip hΦ (x + ι z) (y + ι z)
      simpa [add_sub_add_right_eq_sub] using this
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := ‖x - y‖) (Filter.Eventually.of_forall fun z => ?_)).trans
      (by simp)
    simpa [Real.norm_eq_abs] using this z
  have hfc : Continuous f := by
    have : LipschitzWith 1 f := LipschitzWith.of_dist_le_mul fun x y => by
      simpa [dist_eq_norm, Real.dist_eq] using hflip x y
    exact this.continuous
  have hfb : ∀ x, |f x| ≤ 1 := fun x => by
    have := norm_integral_le_of_norm_le_const (μ := γ) (C := 1) (f := fun z => Φ (x + ι z))
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using a9_cbUnit_bdd hΦ (x + ι z))
    rw [hf x]
    simpa [Real.norm_eq_abs] using this
  obtain ⟨ξ, S, hS, hξ, hξt⟩ := a9_exists_finrange_approx (m := ℱ 0) hX
  have hm0 : ℱ 0 ≤ mΩ := ℱ.le 0
  have hXm : Measurable X := hX.mono hm0 le_rfl
  have hMt : AEMeasurable (M T) P :=
    (hM.sq_int T ⟨hT, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hιm : Measurable ι := ι.continuous.measurable
  have hξmeas : ∀ n, Measurable (ξ n) := fun n => by
    intro s _
    have : ξ n ⁻¹' s = ⋃ x ∈ ((S n).filter (· ∈ s)), ξ n ⁻¹' {x} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop,
        Finset.mem_filter]
      exact ⟨fun h => ⟨ξ n ω, ⟨hS n ω, h⟩, rfl⟩, fun ⟨x, ⟨_, hx⟩, e⟩ => e ▸ hx⟩
    rw [this]
    exact Finset.measurableSet_biUnion _ fun x _ => hm0 _ (hξ n x)
  have hbd1 : Tendsto (fun n => ∫ ω, Φ (ξ n ω + ι (M T ω)) ∂P) atTop
      (𝓝 (∫ ω, Φ (X ω + ι (M T ω)) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_)
      (integrable_const 1) (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · exact (hΦc.measurable.comp_aemeasurable
        ((hξmeas n).aemeasurable.add (hιm.comp_aemeasurable hMt))).aestronglyMeasurable
    · simpa using a9_cbUnit_bdd hΦ _
    · exact (hΦc.tendsto _).comp ((hξt ω).add_const (ι (M T ω)))
  have hbd2 : Tendsto (fun n => ∫ ω, f (ξ n ω) ∂P) atTop (𝓝 (∫ ω, f (X ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_)
      (integrable_const 1) (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · exact (hfc.measurable.comp (hξmeas n)).aestronglyMeasurable
    · simpa using hfb _
    · exact (hfc.tendsto _).comp (hξt ω)
  have hlim := (hbd1.sub hbd2).abs
  refine le_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
  exact a9_shift_H_simple P ℱ T hT M Sg hM sb hsb ι hι (ξ n) (S n) (hS n) (hξ n) Φ hΦ f hfc hfb hf

end Shift

end HRS.Main.A9
