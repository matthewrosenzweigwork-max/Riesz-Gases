import HRS.MS.OrbIdAux1
import HRS.MS.OrbIdAux2

/-!
# S5.2 `orbit_maximal_identification`: the identification clause (all-horizon form)

**Status.**  `orbit_maximal_identification_allhorizon` below is the identification clause of Lemma S5.2 with exactly the
conclusion of the frozen statement `HRS.Whole.orbit_maximal_identification` and the following single change of
hypothesis: `hΦ : ∀ T', IsHSIntegrand P ℱ T' Φ` (Hilbert-Schmidt integrand on every finite horizon `T'`) in place of
`hΦ : IsHSIntegrand P ℱ T Φ` (horizon `T` only).

**Why the change is necessary.**  `IsHilbertItoIntegral.approx` quantifies over all times `τ ≥ 0` and is phrased
through `itoIntegral`, which is `Classical.choose` of an `IsItoIntegral` when one exists and `0` otherwise
(`IsItoIntegral.approx` is vacuous for times at which the integrand is not `L²`).  With the integrand square
integrable only on `[0,T]` the coordinate integrals `⟨Φ,x⟩` can have no continuous version on `[0,∞)` (the integrand
beyond `T` is the base part `c(Dφ_α(X_r))_α`, controlled only pointwise in `x` by `OscAdjointInput.feature`, not
uniformly), so `itoIntegral = 0` and `hM` holds for a `M` with `⟨M_t,x⟩ = 0`; then the conclusion fails.  This is
the defect already recorded for `hilbert_polar_coupling` (attempt 4, `HRS/Prob/HilbertMartingale.lean`).  Whenever the
base part is bounded uniformly in `x` (as under the hypotheses of `orbit_feature_bounded`, `b = 0`), `hΦ` on `[0,T]`
implies the all-horizon form.  The originally frozen statement therefore could not be tied; approved (2026-10-23)
the repair that adds the uniform bound `hB` of the base part to `HRS.Whole.orbit_maximal_identification`, and
`orbit_maximal_identification_bdd` below is tied to the repaired statement with `type_of%`.

Proof: `⟨M_τ, y⟩` is the Itô integral of `⟨Φ, y⟩` (`s52_pair_ito`); the coordinate `α` of `(𝒯M)(t)` is
`⟨M_T,y1⟩ - ⟨M_T,y2⟩ + ⟨M_t,y2⟩` (`s52_coord_recon`); by the Duhamel identity of `OscAdjointInput`
`⟨Φ, y1⟩ - ⟨Φ, y2⟩` vanishes for `r > t` (`s52_pair_grad_y1`), so the integral of the difference stops at `t`
(`s52_lc`, `s52_kill`), and `⟨Φ, y1⟩` is the truncated integrand of the conclusion on `[0,t]`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S52

open HRS HRS.Whole

variable {d : ℕ}

/-- The pairing integrands of an all-horizon Hilbert-Schmidt integrand over a finite index set are progressive `L²`. -/
lemma s52_pairL2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] {κ : Type*} [Fintype κ]
    {Φ : ℝ → Ω → κ → H} (hΦ : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ) (y : H) :
    IsProgressiveL2 P ℱ (fun r ω (k : κ) => inner ℝ (Φ r ω k) y) := by
  refine ⟨isProgressive_pi (u := fun (k : κ) r ω => inner ℝ (Φ r ω k) y) fun k i =>
    ((hΦ 0).prog k i).inner measurable_const, fun T => ?_⟩
  have h1 := pc_sqIntegralOn_inner_le (P := P) (Φ := Φ) (Finset.univ : Finset κ) y T
  have h2 : sqIntegralOn P (fun r ω (k : κ) => inner ℝ (Φ r ω k) y) T =
      sqIntegralOn P (fun r ω (k : (Finset.univ : Finset κ)) => inner ℝ (Φ r ω k) y) T := by
    unfold sqIntegralOn
    refine lintegral_congr fun ω => lintegral_congr fun r => ?_
    exact (Finset.sum_coe_sort (Finset.univ : Finset κ)
      (fun k => ‖inner ℝ (Φ r ω k) y‖ₑ ^ 2)).symm.trans (by simp)
  rw [h2]
  exact lt_of_le_of_lt h1
    (ENNReal.mul_lt_top (hΦ T).sq (lt_top_iff_ne_top.2 (pc_enorm_sq_ne_top y)))

lemma s52_pair_Φ {C : WholeCoeff d} {m T q : ℝ} {N : ℕ} {Ω : Type*}
    (X : ℝ≥0 → Ω → EucConfig d N) (r : ℝ) (ω : Ω) (k : Fin N × Fin d) (y : KSpace d m T) :
    inner ℝ (empiricalNoiseIntegrand C m T q X r ω k) y =
      Real.sqrt (2 * q / N) * inner ℝ (gradFeature C m T k.2 r (X (Real.toNNReal r) ω k.1)) y := by
  unfold empiricalNoiseIntegrand
  rw [real_inner_smul_left]

/-- **Lemma S5.2, identification clause, all-horizon form** (see the module docstring: `hΦ` on every horizon). -/
theorem orbit_maximal_identification_allhorizon (C : WholeCoeff d) (m T q : ℝ) (N : ℕ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin N × Fin d → ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (M : ℝ → Ω → KSpace d m T) (hN : 1 ≤ N) (hW : IsCylindricalBrownian P ℱ W)
    (hΦ : ∀ T' : ℝ, IsHSIntegrand P ℱ T' (empiricalNoiseIntegrand C m T q X))
    (hM : IsHilbertItoIntegral P ℱ W (empiricalNoiseIntegrand C m T q X) M)
    (hC : OscAdjointInput C m T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d, ∀ᵐ ζ ∂P,
      OscDual.coord (reconstructPath m T M ζ t) α =
        itoIntegral P ℱ W (fun r ζ' ia => if r ∈ Set.Icc (0 : ℝ) t then Real.sqrt (2 * q / N) *
          gradComp ia.2 (propagatorW C r t (oscTestFun m α)) (X (Real.toNNReal r) ζ' ia.1) else 0) t ζ := by
  classical
  intro t ht α
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hW' : IsBrownianFiltration P ℱ W := s52_brownian_of_cyl hW
  set Φ := empiricalNoiseIntegrand C m T q X with hΦdef
  set c0 : ℝ := Real.sqrt (2 * q / N) with hc0
  set u1 : ℝ → Ω → Fin N × Fin d → ℝ := fun r ω k => inner ℝ (Φ r ω k) (s52y1 m T t α) with hu1
  set u2 : ℝ → Ω → Fin N × Fin d → ℝ := fun r ω k => inner ℝ (Φ r ω k) (s52y2 m T α) with hu2
  have hL1 : IsProgressiveL2 P ℱ u1 := s52_pairL2 hΦ _
  have hL2 : IsProgressiveL2 P ℱ u2 := s52_pairL2 hΦ _
  have hLd : IsProgressiveL2 P ℱ (fun r ω k => u1 r ω k - u2 r ω k) := isProgressiveL2_sub hL1 hL2
  set ud : ℝ → Ω → Fin N × Fin d → ℝ := fun r ω k => u1 r ω k - u2 r ω k with hud
  -- pointwise values of the pairings
  have hu2val : ∀ r ω (k : Fin N × Fin d), u2 r ω k =
      c0 * gradComp k.2 (oscTestFun m α) (X (Real.toNNReal r) ω k.1) := by
    intro r ω k
    simp only [hu2, hΦdef, hc0]
    rw [s52_pair_Φ, s52_pair_grad_y2 hC hT]
  have hu1val : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ ω (k : Fin N × Fin d), u1 r ω k =
      c0 * (if r ≤ t then gradComp k.2 (propagatorW C r t (oscTestFun m α))
        (X (Real.toNNReal r) ω k.1) else gradComp k.2 (oscTestFun m α) (X (Real.toNNReal r) ω k.1)) := by
    intro r hr ω k
    simp only [hu1, hΦdef, hc0]
    rw [s52_pair_Φ, s52_pair_grad_y1 hC ht.2 k.2 hr]
  -- the pairings with the Itô integrals
  have hp1T := s52_pair_ito hW' hM (s52y1 m T t α)
    (pc_isProgressiveL2_inner hΦ (s52y1 m T t α) Finset.univ) hT
  have hp2T := s52_pair_ito hW' hM (s52y2 m T α) (pc_isProgressiveL2_inner hΦ (s52y2 m T α) Finset.univ) hT
  have hp2t := s52_pair_ito hW' hM (s52y2 m T α) (pc_isProgressiveL2_inner hΦ (s52y2 m T α) Finset.univ) ht.1
  have hsub := itoIntegral_sub hW' hL1 hL2
  -- the integral of the difference stops at `t`
  have hagreeE : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ ω, ud r ω = (fun r ω k => if r ≤ t then ud r ω k else 0) r ω := by
    intro r hr ω
    funext k
    by_cases hrt : r ≤ t
    · simp [hrt]
    · simp only [hrt, if_false, hud, hu2val r ω k, hu1val r hr ω k]
      simp
  have hLdt : IsProgressiveL2 P ℱ (fun r ω k => if r ≤ t then ud r ω k else 0) := by
    have := s52_isProgressiveL2_ite hLd (measurableSet_Iic (a := t))
    simpa using this
  have hlcE := s52_lc hW' hLd hLdt hT hagreeE
  have hkillE := s52_kill hW' hLd ht.1
  -- the target integrand
  set ψ : ℝ → Ω → Fin N × Fin d → ℝ := fun r ζ' ia => if r ∈ Set.Icc (0 : ℝ) t then Real.sqrt (2 * q / N) *
    gradComp ia.2 (propagatorW C r t (oscTestFun m α)) (X (Real.toNNReal r) ζ' ia.1) else 0 with hψ
  have hψeq : ψ = fun r ω k => if r ∈ Set.Icc (0 : ℝ) t then u1 r ω k else 0 := by
    funext r ω k
    by_cases hr : r ∈ Set.Icc (0 : ℝ) t
    · have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
      simp only [hψ, hr, if_true, hu1val r hrT ω k, hr.2]
      rfl
    · simp only [hψ, if_neg hr]
  have hLψ : IsProgressiveL2 P ℱ ψ := by
    rw [hψeq]; exact s52_isProgressiveL2_ite hL1 measurableSet_Icc
  have hagreeG : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ ω, u1 r ω = ψ r ω := by
    intro r hr ω
    rw [hψeq]
    simp [hr]
  have hlcG := s52_lc hW' hL1 hLψ ht.1 hagreeG
  filter_upwards [hp1T, hp2T, hp2t, hsub, hlcE, hkillE, hlcG] with ζ h1 h2 h3 h4 h5 h6 h7
  rw [s52_coord_recon ht.1 ht.2]
  have k0a : inner ℝ (M T ζ) (s52y1 m T t α) = itoIntegral P ℱ W u1 T ζ := h1
  have k0b : inner ℝ (M T ζ) (s52y2 m T α) = itoIntegral P ℱ W u2 T ζ := h2
  have k0c : inner ℝ (M t ζ) (s52y2 m T α) = itoIntegral P ℱ W u2 t ζ := h3
  have k1 : itoIntegral P ℱ W ud T ζ = itoIntegral P ℱ W u1 T ζ - itoIntegral P ℱ W u2 T ζ := h4 T
  have k2 : itoIntegral P ℱ W ud t ζ = itoIntegral P ℱ W u1 t ζ - itoIntegral P ℱ W u2 t ζ := h4 t
  have k3 : itoIntegral P ℱ W ud (min T T) ζ =
      itoIntegral P ℱ W (fun r ω k => if r ≤ t then ud r ω k else 0) (min T T) ζ := h5 T hT
  have k4 : itoIntegral P ℱ W (fun r ω k => if r ≤ t then ud r ω k else 0) T ζ =
      itoIntegral P ℱ W ud (min T t) ζ := h6 T hT
  have k5 : itoIntegral P ℱ W u1 (min t t) ζ = itoIntegral P ℱ W ψ (min t t) ζ := h7 t ht.1
  rw [min_self] at k3 k5
  rw [min_eq_right ht.2] at k4
  rw [k0a, k0b, k0c]
  linarith


/-! ### From the horizon `T` to all horizons under a uniform bound of the base part -/

lemma s52_norm_mk_le {m T : ℝ} (a a' b : _) :
    ‖(KSpace.mk a a' b : KSpace d m T)‖ ≤ ‖(a : OscDual d m)‖ + ‖(a' : L2Path d m T)‖ + ‖(b : OscDual d m)‖ := by
  unfold KSpace.mk
  show ‖(WithLp.toLp 2 (a, WithLp.toLp 2 (a', b)) :
    WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m)))‖ ≤ _
  rw [WithLp.prod_norm_eq_of_L2]
  change Real.sqrt (‖a‖ ^ 2 + ‖(WithLp.toLp 2 (a', b) : WithLp 2 (L2Path d m T × OscDual d m))‖ ^ 2) ≤ _
  rw [WithLp.prod_norm_eq_of_L2]
  change Real.sqrt (‖a‖ ^ 2 + Real.sqrt (‖a'‖ ^ 2 + ‖b‖ ^ 2) ^ 2) ≤ _
  have h1 : Real.sqrt (‖a'‖ ^ 2 + ‖b‖ ^ 2) ≤ ‖a'‖ + ‖b‖ :=
    Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [norm_nonneg a', norm_nonneg b]⟩
  have h2 : Real.sqrt (‖a‖ ^ 2 + Real.sqrt (‖a'‖ ^ 2 + ‖b‖ ^ 2) ^ 2) ≤
      ‖a‖ + Real.sqrt (‖a'‖ ^ 2 + ‖b‖ ^ 2) :=
    Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [norm_nonneg a, Real.sqrt_nonneg (‖a'‖ ^ 2 + ‖b‖ ^ 2)]⟩
  linarith

/-- For `r ≥ T` the `L²_t` component of the feature vanishes, so `‖Γ‖ ≤ 2 ‖base‖`. -/
lemma s52_norm_feature_tail {C : WholeCoeff d} {m T r : ℝ} (hr : T ≤ r)
    (Dop : (Euc d → ℝ) → Euc d → ℝ) (x : Euc d) :
    ‖orbitFeature C m T Dop r x‖ ≤ 2 * ‖ellVec (d := d) m (fun α => Dop (oscTestFun m α) x)‖ := by
  classical
  have hf : (fun t : ℝ => if r < t then ellVec (d := d) m (fun α => Dop
      (propagatorW C r t (generatorW C t (oscTestFun m α))) x) else 0) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)]
      (fun _ => (0 : OscDual d m)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht
    have : ¬ r < t := not_lt.2 (ht.2.trans hr)
    simp [this]
  have hA : (if h : MemLp (fun t : ℝ => if r < t then ellVec (d := d) m (fun α => Dop
      (propagatorW C r t (generatorW C t (oscTestFun m α))) x) else 0) 2
        (volume.restrict (Set.Icc (0 : ℝ) T)) then h.toLp _ else (0 : L2Path d m T)) = 0 := by
    split_ifs with h
    · have hz : MemLp (fun _ : ℝ => (0 : OscDual d m)) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) :=
        MemLp.zero
      have := MemLp.toLp_congr h hz hf
      rw [this]; exact MemLp.toLp_zero _
    · rfl
  unfold orbitFeature
  simp only []
  rw [hA]
  have := s52_norm_mk_le (d := d) (m := m) (T := T)
    (ellVec (d := d) m (fun α => Dop (oscTestFun m α) x)) 0
    (ellVec (d := d) m (fun α => Dop (oscTestFun m α) x))
  simp only [norm_zero, add_zero] at this
  linarith

/-- The frozen horizon-`T` hypothesis `hΦ` together with a uniform bound of the base part gives all horizons. -/
lemma s52_hs_allhorizon {C : WholeCoeff d} {m T q : ℝ} (hT0 : 0 ≤ T) {N : ℕ} {Ω : Type*}
    {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (X : ℝ≥0 → Ω → EucConfig d N)
    (hΦ : IsHSIntegrand P ℱ T (empiricalNoiseIntegrand C m T q X))
    (hB : ∃ B : ℝ, ∀ (a : Fin d) (x : Euc d),
      ‖ellVec (d := d) m (fun α => gradComp a (oscTestFun m α) x)‖ ≤ B) (T' : ℝ) :
    IsHSIntegrand P ℱ T' (empiricalNoiseIntegrand C m T q X) := by
  classical
  obtain ⟨B, hB⟩ := hB
  refine ⟨hΦ.prog, hΦ.summable, ?_⟩
  by_cases hTT : T' ≤ T
  · refine lt_of_le_of_lt ?_ hΦ.sq
    unfold hsSqIntegralOn
    refine lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right hTT)
  · have hTT' : T ≤ T' := (not_le.1 hTT).le
    set K : ℝ≥0∞ := (Fintype.card (Fin N × Fin d) : ℝ≥0∞) *
      (ENNReal.ofReal (2 * |Real.sqrt (2 * q / N)| * max B 0)) ^ 2 with hK
    have hpt : ∀ r : ℝ, T ≤ r → ∀ ω, ∑' k : Fin N × Fin d,
        ‖empiricalNoiseIntegrand C m T q X r ω k‖ₑ ^ 2 ≤ K := by
      intro r hr ω
      rw [tsum_fintype]
      calc ∑ k : Fin N × Fin d, ‖empiricalNoiseIntegrand C m T q X r ω k‖ₑ ^ 2
          ≤ ∑ _k : Fin N × Fin d, (ENNReal.ofReal (2 * |Real.sqrt (2 * q / N)| * max B 0)) ^ 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            gcongr
            rw [← ofReal_norm]
            apply ENNReal.ofReal_le_ofReal
            unfold empiricalNoiseIntegrand
            rw [norm_smul, Real.norm_eq_abs]
            have h1 := s52_norm_feature_tail (C := C) (m := m) (T := T) hr (gradComp k.2)
              (X (Real.toNNReal r) ω k.1)
            have h2 := hB k.2 (X (Real.toNNReal r) ω k.1)
            have h3 : ‖gradFeature C m T k.2 r (X (Real.toNNReal r) ω k.1)‖ ≤ 2 * max B 0 := by
              unfold gradFeature
              exact h1.trans (by linarith [le_max_left B 0])
            calc |Real.sqrt (2 * q / N)| * ‖gradFeature C m T k.2 r (X (Real.toNNReal r) ω k.1)‖
                ≤ |Real.sqrt (2 * q / N)| * (2 * max B 0) := by gcongr
              _ = _ := by ring
        _ = K := by simp [hK]
    unfold hsSqIntegralOn
    have hsplit : ∀ ω : Ω, (∫⁻ r in Set.Icc 0 T', ∑' k, ‖empiricalNoiseIntegrand C m T q X r ω k‖ₑ ^ 2) ≤
        (∫⁻ r in Set.Icc 0 T, ∑' k, ‖empiricalNoiseIntegrand C m T q X r ω k‖ₑ ^ 2) +
          ENNReal.ofReal (T' - T) * K := by
      intro ω
      rw [← Set.Icc_union_Ioc_eq_Icc hT0 hTT', lintegral_union measurableSet_Ioc
        (Set.disjoint_left.2 fun a ha hb => absurd ha.2 (not_le.2 hb.1))]
      refine add_le_add_right ?_ _
      calc (∫⁻ r in Set.Ioc T T', ∑' k, ‖empiricalNoiseIntegrand C m T q X r ω k‖ₑ ^ 2)
          ≤ ∫⁻ r in Set.Ioc T T', K :=
            setLIntegral_mono' measurableSet_Ioc fun r hr => hpt r hr.1.le ω
        _ = ENNReal.ofReal (T' - T) * K := by
            rw [setLIntegral_const, Real.volume_Ioc, mul_comm]
    have hKtop : ENNReal.ofReal (T' - T) * K < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top))
    calc ∫⁻ ω, (∫⁻ r in Set.Icc 0 T', ∑' k, ‖empiricalNoiseIntegrand C m T q X r ω k‖ₑ ^ 2) ∂P
        ≤ ∫⁻ ω, ((∫⁻ r in Set.Icc 0 T, ∑' k, ‖empiricalNoiseIntegrand C m T q X r ω k‖ₑ ^ 2) +
          ENNReal.ofReal (T' - T) * K) ∂P := lintegral_mono hsplit
      _ = (∫⁻ ω, (∫⁻ r in Set.Icc 0 T, ∑' k, ‖empiricalNoiseIntegrand C m T q X r ω k‖ₑ ^ 2) ∂P) +
          ENNReal.ofReal (T' - T) * K := by
            rw [lintegral_add_right _ measurable_const]; simp
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hΦ.sq, hKtop⟩


/-- **Lemma S5.2, identification clause, with the frozen hypotheses plus a uniform bound of the base part.**
Same hypotheses as the frozen `orbit_maximal_identification` (`hΦ` on the horizon `T` only) and one extra hypothesis
`hB`: `x ↦ (∂_aφ_α(x))_α` is bounded in `ℓ²` uniformly in `x` (`a < d`).  Under `hB`, `hΦ` implies the
all-horizon form (`s52_hs_allhorizon`).  `hB` holds in the setting of `orbit_feature_bounded` (the base part is the
`ℓ²` component `A₀ = B` of `Γ_{r,a}(x)`, bounded by `C_{T,0}`); it is the only difference to the frozen statement. -/
theorem orbit_maximal_identification_bdd (C : WholeCoeff d) (m T q : ℝ) (N : ℕ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin N × Fin d → ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (M : ℝ → Ω → KSpace d m T) (hN : 1 ≤ N) (hW : IsCylindricalBrownian P ℱ W)
    (hΦ : IsHSIntegrand P ℱ T (empiricalNoiseIntegrand C m T q X))
    (hM : IsHilbertItoIntegral P ℱ W (empiricalNoiseIntegrand C m T q X) M)
    (hC : OscAdjointInput C m T)
    (hB : ∃ B : ℝ, ∀ (a : Fin d) (x : Euc d),
      ‖ellVec (d := d) m (fun α => gradComp a (oscTestFun m α) x)‖ ≤ B) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d, ∀ᵐ ζ ∂P,
      OscDual.coord (reconstructPath m T M ζ t) α =
        itoIntegral P ℱ W (fun r ζ' ia => if r ∈ Set.Icc (0 : ℝ) t then Real.sqrt (2 * q / N) *
          gradComp ia.2 (propagatorW C r t (oscTestFun m α)) (X (Real.toNNReal r) ζ' ia.1) else 0) t ζ := by
  intro t ht α
  have hT0 : 0 ≤ T := ht.1.trans ht.2
  exact orbit_maximal_identification_allhorizon C m T q N P ℱ W X M hN hW
    (s52_hs_allhorizon hT0 P ℱ X hΦ hB) hM hC t ht α

/-- Tie to the repaired frozen statement (S5.2 repair `hB`, approved 2026-10-23). -/
example := (@orbit_maximal_identification_bdd : type_of% @HRS.Whole.orbit_maximal_identification)

end HRS.MS.S52
