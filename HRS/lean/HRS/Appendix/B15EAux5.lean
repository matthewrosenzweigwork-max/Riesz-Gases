import HRS.Appendix.B15EAux4

/-!
# Packet B15E, part 5: lower semicontinuity of the Fisher information under uniformly convergent integrands,
the limit core, and Stage 1 (level-`M` regularised entropy inequality for `V ∈ C²`)
-/

noncomputable section

open MeasureTheory InformationTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ### Bounds for Fisher test fields -/

/-- A Fisher test field is bounded on the configuration space (continuity of its lift on the compact
fundamental cube). -/
theorem b15e_testField_bounded {ζ : Config d N → (Fin N → Euc d)} (hζ : IsFisherTestField ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X i, ‖ζ X i‖ ≤ C := by
  have hc : Continuous fun Y : Fin N → Euc d => ζ fun i => Torus.mk (Y i) := hζ.smooth.continuous
  have hcube : IsCompact ((WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1) :
      Set (Euc d)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  have hS : IsCompact (Set.pi Set.univ fun _ : Fin N =>
      ((WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1) : Set (Euc d))) :=
    isCompact_univ_pi fun _ => hcube
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun X i => ?_⟩
  have hmem : (fun i => Torus.rep (X i)) ∈ Set.pi Set.univ fun _ : Fin N =>
      ((WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1) : Set (Euc d)) :=
    fun i _ => d1_rep_mem_cube (X i)
  have h1 := hB _ hmem
  have hX : (fun j => Torus.mk (Torus.rep (X j))) = X := funext fun j => Torus.mk_rep (X j)
  rw [hX] at h1
  exact ((norm_le_pi_norm (ζ X) i).trans h1).trans (le_max_left _ _)

/-- The derivative of the lift of a Torus function at a representative is the inner product with the torus
gradient. -/
theorem b15e_fderiv_lift_eq_inner (g : Torus d → ℝ) (x : Torus d) (w : Euc d) :
    fderiv ℝ (Torus.lift g) (Torus.rep x) w = inner ℝ (Torus.grad g x) w := by
  unfold Torus.grad gradient
  rw [InnerProductSpace.toDual_symm_apply]

/-- **The Fisher integrands of potentials differing by a one-body term** are uniformly close, with
a bound proportional to the sup of `|∇g|` (`g = V' - V`). -/
theorem b15e_fisherIntegrand_sub {invβ : ℝ} {U : Config d N → ℝ}
    (hU : Differentiable ℝ (fun Z : Fin N → Euc d => U (fun i => Torus.mk (Z i))))
    (g : Torus d → ℝ) (hg : Differentiable ℝ (Torus.lift g)) {ε : ℝ} (hε : ∀ x, ‖Torus.grad g x‖ ≤ ε)
    (ζ : Config d N → (Fin N → Euc d)) {Cζ : ℝ} (hC : ∀ X i, ‖ζ X i‖ ≤ Cζ) (X : Config d N) :
    |b15c_fisherIntegrand invβ (fun X => U X + ∑ i, g (X i)) ζ X - b15c_fisherIntegrand invβ U ζ X| ≤
      2 * |invβ⁻¹| * ((N : ℝ) * (ε * Cζ)) := by
  set Y : Fin N → Euc d := fun i => Torus.rep (X i) with hY
  have hsum : HasFDerivAt (fun Z : Fin N → Euc d => ∑ i, Torus.lift g (Z i))
      (∑ i, (fderiv ℝ (Torus.lift g) (Y i)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i)) Y := by
    refine HasFDerivAt.fun_sum fun i _ => ?_
    have hp : HasFDerivAt (fun f : Fin N → Euc d => f i)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i) Y := hasFDerivAt_apply i Y
    exact HasFDerivAt.comp (g := Torus.lift g) Y (hg (Y i)).hasFDerivAt hp
  have hfd : fderiv ℝ (fun Z : Fin N → Euc d => (fun X => U X + ∑ i, g (X i)) (fun i => Torus.mk (Z i))) Y =
      fderiv ℝ (fun Z : Fin N → Euc d => U (fun i => Torus.mk (Z i))) Y +
        ∑ i, (fderiv ℝ (Torus.lift g) (Y i)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i) := by
    have h1 : (fun Z : Fin N → Euc d => (fun X => U X + ∑ i, g (X i)) (fun i => Torus.mk (Z i))) =
        fun Z => U (fun i => Torus.mk (Z i)) + ∑ i, Torus.lift g (Z i) := by
      funext Z; simp [Torus.lift]
    rw [h1]
    exact ((hU Y).hasFDerivAt.add hsum).fderiv
  unfold b15c_fisherIntegrand
  rw [hfd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  have key : |∑ i, fderiv ℝ (Torus.lift g) (Y i) (ζ X i)| ≤ (N : ℝ) * (ε * Cζ) := by
    calc |∑ i, fderiv ℝ (Torus.lift g) (Y i) (ζ X i)| ≤ ∑ i, |fderiv ℝ (Torus.lift g) (Y i) (ζ X i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, ε * Cζ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [hY, b15e_fderiv_lift_eq_inner]
          calc |inner ℝ (Torus.grad g (X i)) (ζ X i)| ≤ ‖Torus.grad g (X i)‖ * ‖ζ X i‖ :=
                abs_real_inner_le_norm _ _
            _ ≤ ε * Cζ := mul_le_mul (hε _) (hC X i) (norm_nonneg _) ((norm_nonneg _).trans (hε (X i)))
      _ = (N : ℝ) * (ε * Cζ) := by simp
  have e : (-2 * configDiv ζ X + 2 * invβ⁻¹ * (fderiv ℝ (fun Z : Fin N → Euc d => U (fun i => Torus.mk (Z i))) Y
        (ζ X) + ∑ i, fderiv ℝ (Torus.lift g) (Y i) (ζ X i)) - ∑ i, ‖ζ X i‖ ^ 2) -
      (-2 * configDiv ζ X + 2 * invβ⁻¹ * fderiv ℝ (fun Z : Fin N → Euc d => U (fun i => Torus.mk (Z i))) Y
        (ζ X) - ∑ i, ‖ζ X i‖ ^ 2) = 2 * invβ⁻¹ * ∑ i, fderiv ℝ (Torus.lift g) (Y i) (ζ X i) := by ring
  rw [e, abs_mul, abs_mul, abs_two]
  calc 2 * |invβ⁻¹| * |∑ i, fderiv ℝ (Torus.lift g) (Y i) (ζ X i)| ≤ 2 * |invβ⁻¹| * ((N : ℝ) * (ε * Cζ)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := rfl

/-! ### Fisher lower semicontinuity under uniformly convergent integrands -/

/-- **Lower semicontinuity of the Fisher functional** in the pair (potential, law) when the integrands for
`U_k` converge uniformly to those for `U` (instead of being eventually equal, `b15b_fisherInfoGen_liminf_le`). -/
theorem b15e_fisherInfoGen_liminf_le_unif (invβ : ℝ) {U : Config d N → ℝ} {Un : ℕ → Config d N → ℝ}
    {P : Measure (Config d N)} {Pn : ℕ → Measure (Config d N)} [∀ n, IsProbabilityMeasure (Pn n)]
    (hcont : ∀ ζ, IsFisherTestField ζ → Continuous (b15c_fisherIntegrand invβ U ζ))
    (hcontn : ∀ n ζ, IsFisherTestField ζ → Continuous (b15c_fisherIntegrand invβ (Un n) ζ))
    (hunif : ∀ ζ, IsFisherTestField ζ → ∀ ε > 0, ∀ᶠ n in atTop, ∀ X,
      |b15c_fisherIntegrand invβ (Un n) ζ X - b15c_fisherIntegrand invβ U ζ X| ≤ ε)
    (hP : ∀ φ : Config d N → ℝ, Continuous φ →
      Tendsto (fun n => ∫ x, φ x ∂(Pn n)) atTop (𝓝 (∫ x, φ x ∂P))) :
    b15_fisherInfoGen invβ U P ≤ liminf (fun n => b15_fisherInfoGen invβ (Un n) (Pn n)) atTop := by
  simp only [b15c_fisherInfoGen_eq]
  refine iSup₂_le fun ζ hζ => ?_
  have hint := hP _ (hcont ζ hζ)
  have h2 : Tendsto (fun n => ∫ X, b15c_fisherIntegrand invβ (Un n) ζ X ∂(Pn n)) atTop
      (𝓝 (∫ X, b15c_fisherIntegrand invβ U ζ X ∂P)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    filter_upwards [hunif ζ hζ (ε / 2) hε2, Metric.tendsto_nhds.1 hint (ε / 2) hε2] with n h1 h3
    have hI : ∀ (Q : Measure (Config d N)) [IsProbabilityMeasure Q] (f : Config d N → ℝ),
        Continuous f → Integrable f Q := fun Q _ f hf =>
      hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have h4 : |∫ X, b15c_fisherIntegrand invβ (Un n) ζ X ∂(Pn n) -
        ∫ X, b15c_fisherIntegrand invβ U ζ X ∂(Pn n)| ≤ ε / 2 := by
      rw [← integral_sub (hI _ _ (hcontn n ζ hζ)) (hI _ _ (hcont ζ hζ))]
      have := norm_integral_le_of_norm_le_const (μ := Pn n)
        (f := fun X => b15c_fisherIntegrand invβ (Un n) ζ X - b15c_fisherIntegrand invβ U ζ X)
        (C := ε / 2) (Filter.Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs]; exact h1 X)
      simpa [Measure.real, measure_univ] using this
    rw [Real.dist_eq] at h3 ⊢
    calc |∫ X, b15c_fisherIntegrand invβ (Un n) ζ X ∂(Pn n) - ∫ X, b15c_fisherIntegrand invβ U ζ X ∂P|
        = |(∫ X, b15c_fisherIntegrand invβ (Un n) ζ X ∂(Pn n) -
            ∫ X, b15c_fisherIntegrand invβ U ζ X ∂(Pn n)) +
          (∫ X, b15c_fisherIntegrand invβ U ζ X ∂(Pn n) - ∫ X, b15c_fisherIntegrand invβ U ζ X ∂P)| := by
          congr 1; ring
      _ ≤ |∫ X, b15c_fisherIntegrand invβ (Un n) ζ X ∂(Pn n) -
            ∫ X, b15c_fisherIntegrand invβ U ζ X ∂(Pn n)| +
          |∫ X, b15c_fisherIntegrand invβ U ζ X ∂(Pn n) - ∫ X, b15c_fisherIntegrand invβ U ζ X ∂P| :=
          abs_add_le _ _
      _ < ε := by linarith
  have h3 := ENNReal.tendsto_ofReal h2
  rw [← h3.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
  exact le_iSup₂ (f := fun (ζ : Config d N → (Fin N → Euc d)) (_ : IsFisherTestField ζ) =>
    ENNReal.ofReal (∫ X, b15c_fisherIntegrand invβ (Un n) ζ X ∂(Pn n))) ζ hζ

/-! ### Fatou in the time variable and the limit core -/

/-- Fatou for the time integral of the Fisher information. -/
theorem b15e_lintegral_liminf_le {f : ℝ → ℝ≥0∞} {fk : ℕ → ℝ → ℝ≥0∞} {t : ℝ}
    (hpt : ∀ r ∈ Set.Icc (0 : ℝ) t, f r ≤ liminf (fun k => fk k r) atTop)
    (hmeas : ∀ k, AEMeasurable (fk k) (volume.restrict (Set.Icc (0 : ℝ) t))) :
    ∫⁻ r in Set.Icc (0 : ℝ) t, f r ≤ liminf (fun k => ∫⁻ r in Set.Icc (0 : ℝ) t, fk k r) atTop :=
  calc ∫⁻ r in Set.Icc (0 : ℝ) t, f r
      ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, liminf (fun k => fk k r) atTop :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ ≤ _ := lintegral_liminf_le' hmeas

/-- **The limit core** (the `EReal` bookkeeping at the end of `b15b_step4_limit`): if
`H ≤ liminf H_k`, `I ≤ liminf I_k` and `H_k + β I_k ≤ K` for all `k`, then `H + β I ≤ K`. -/
theorem b15e_limit_core {invβ : ℝ} {H : EReal} {Hk : ℕ → EReal} {I : ℝ≥0∞} {Ik : ℕ → ℝ≥0∞} {K : EReal}
    (hH : H ≤ liminf Hk atTop) (hI : I ≤ liminf Ik atTop)
    (hreg : ∀ k, Hk k + ((ENNReal.ofReal invβ * Ik k : ℝ≥0∞) : EReal) ≤ K) :
    H + ((ENNReal.ofReal invβ * I : ℝ≥0∞) : EReal) ≤ K := by
  have hmono : Monotone (fun x : ℝ≥0∞ => ((ENNReal.ofReal invβ * x : ℝ≥0∞) : EReal)) :=
    fun x y h => EReal.coe_ennreal_le_coe_ennreal_iff.mpr (by gcongr)
  have hcont : Continuous (fun x : ℝ≥0∞ => ((ENNReal.ofReal invβ * x : ℝ≥0∞) : EReal)) :=
    continuous_coe_ennreal_ereal.comp (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top)
  have hb : ((ENNReal.ofReal invβ * I : ℝ≥0∞) : EReal) ≤
      liminf (fun k => ((ENNReal.ofReal invβ * Ik k : ℝ≥0∞) : EReal)) atTop := by
    refine (hmono hI).trans ?_
    exact (hmono.map_liminf_of_continuousAt (F := atTop) Ik hcont.continuousAt).le
  refine (add_le_add hH hb).trans ((EReal.le_liminf_add (f := atTop)).trans ?_)
  exact liminf_le_of_frequently_le' (Frequently.of_forall hreg)

/-- The measurability of `r ↦ 𝓘_{U^M}(P^r_M)` for the regularised process (downstream copy of
`b15b_measurable_fisherInfoGen_reg`, with `b15b_fisherIntegrand_continuous_proof`). -/
theorem b15e_measurable_fisherInfoGen_reg {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hV : Torus.IsCk 2 D.V) (M : ℝ) {T : ℝ}
    {Y₀ : Ω → Fin N → Euc d} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D)
      Y₀ (fun _ => ⊤) Y) :
    AEMeasurable (fun r : ℝ => b15_fisherInfoGen D.invβ (b15c_potentialReg D M)
      (selectedLaw P (b15c_regProcess Y) r)) (volume.restrict (Set.Icc 0 T)) := by
  rcases lt_or_ge T 0 with hT | hT
  · rw [Set.Icc_eq_empty (not_le.mpr hT), Measure.restrict_empty]
    exact aemeasurable_zero_measure
  refine b15b_fisherInfoGen_aemeasurable (P := P) D.invβ (U := b15c_potentialReg (N := N) D M)
    (fun ζ hζ => b15b_fisherIntegrand_continuous_proof _ (b15b_potentialReg_c1 D hV M) hζ)
    (fun s => b15c_regProcess_measurable hY s) ?_
  exact Filter.Eventually.of_forall fun ω =>
    b15c3_regProcess_contOn Y ω (hY.cont ω T hT (WithTop.coe_lt_top T))

end HRS
