import HRS.Prob.Metrics

/-!
# Chunk E, row 2.10 (fixed-`β` closure), packet C: abstract lemmas on a separable Banach space

Statements used by `HRS.ME.Bias` (assembly of `critical_bias_constants_fixed`):

* `smoothConstant_pos_of_aemeasurable`: `0 < 𝔠_k(G,h)` for every `h ≠ 0` and every `G` (no Gaussianity,
  no moments): test function `ε sin(λ L z)` with `L` norming `h` and `λ` small.
* `wassersteinE_translate_sandwich`: `W_p(Law(X+h), Q)` lies within `W_p(Law X, Q)` of `‖h‖`
  if `‖X‖` is integrable (upper bound: triangle inequality and `wassersteinE_translate`; lower bound:
  triangle inequality and `W_1(Law(X+h), Law X) ≥ |L h|` for a norming functional `L`).
* `smooth_translation_expansion_sep`, `smooth_translation_distance_sep`: Lemma 4.27
  (`smooth_translation_expansion`, `smooth_translation_distance`) for `X` and `G` on two *different*
  probability spaces, by passing to the product space.
* `div_bound`: the scalar estimate that turns the error budget into `C/√log N`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.Bias

/-! ### Product-space helpers (ℝ-valued integrands and laws) -/

theorem integral_fst_prod_aux {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (g : Ω → ℝ) (hg : AEStronglyMeasurable g P) :
    ∫ w, g w.1 ∂(P.prod P') = ∫ ω, g ω ∂P := by
  have hm : (P.prod P').map Prod.fst = P := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have h1 := integral_map (μ := P.prod P') (φ := Prod.fst) (f := g)
    measurable_fst.aemeasurable (by rw [hm]; exact hg)
  rw [hm] at h1
  exact h1.symm

theorem integral_snd_prod_aux {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (g : Ω' → ℝ) (hg : AEStronglyMeasurable g P') :
    ∫ w, g w.2 ∂(P.prod P') = ∫ ω, g ω ∂P' := by
  have hm : (P.prod P').map Prod.snd = P' := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have h1 := integral_map (μ := P.prod P') (φ := Prod.snd) (f := g)
    measurable_snd.aemeasurable (by rw [hm]; exact hg)
  rw [hm] at h1
  exact h1.symm

theorem law_fst_prod_aux {Ω Ω' B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω → B) (hY : AEMeasurable Y P) :
    law (P.prod P') (fun w : Ω × Ω' => Y w.1) = law P Y := by
  have hm : (P.prod P').map Prod.fst = P := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hY' : AEMeasurable Y ((P.prod P').map Prod.fst) := by rw [hm]; exact hY
  have h1 : Measure.map Y ((P.prod P').map Prod.fst) = Measure.map (fun w : Ω × Ω' => Y w.1) (P.prod P') :=
    AEMeasurable.map_map_of_aemeasurable hY' measurable_fst.aemeasurable
  show Measure.map (fun w : Ω × Ω' => Y w.1) (P.prod P') = Measure.map Y P
  rw [← h1, hm]

theorem law_snd_prod_aux {Ω Ω' B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → B) (hY : AEMeasurable Y P') :
    law (P.prod P') (fun w : Ω × Ω' => Y w.2) = law P' Y := by
  have hm : (P.prod P').map Prod.snd = P' := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hY' : AEMeasurable Y ((P.prod P').map Prod.snd) := by rw [hm]; exact hY
  have h1 : Measure.map Y ((P.prod P').map Prod.snd) = Measure.map (fun w : Ω × Ω' => Y w.2) (P.prod P') :=
    AEMeasurable.map_map_of_aemeasurable hY' measurable_snd.aemeasurable
  show Measure.map (fun w : Ω × Ω' => Y w.2) (P.prod P') = Measure.map Y P'
  rw [← h1, hm]

section Abstract

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B] [CompleteSpace B]

/-- Symmetry of `wassersteinE`. -/
theorem wassersteinE_comm' (p : ℝ) (P Q : Measure B) : wassersteinE p P Q = wassersteinE p Q P := by
  have aux : ∀ P Q : Measure B, wassersteinE p P Q ≤ wassersteinE p Q P := by
    intro P Q
    refine le_iInf fun π => ?_
    have hsw : IsCoupling (π.1.map Prod.swap) P Q := by
      refine ⟨?_, ?_⟩
      · rw [Measure.map_map measurable_fst measurable_swap]
        exact π.2.2
      · rw [Measure.map_map measurable_snd measurable_swap]
        exact π.2.1
    refine (wassersteinE_le_cost (p := p) hsw).trans (le_of_eq ?_)
    congr 1
    rw [show π.1.map Prod.swap = π.1.map (MeasurableEquiv.prodComm : B × B ≃ᵐ B × B) from rfl,
      lintegral_map_equiv (fun z : B × B => ENNReal.ofReal (‖z.1 - z.2‖ ^ p)) (MeasurableEquiv.prodComm)]
    congr 1; ext z
    change ENNReal.ofReal (‖z.2 - z.1‖ ^ p) = ENNReal.ofReal (‖z.1 - z.2‖ ^ p)
    rw [norm_sub_rev]
  exact le_antisymm (aux P Q) (aux Q P)

/-- `|∫ L dP - ∫ L dQ| ≤ W_1(P, Q)` for a functional of norm at most `1` that is integrable for both. -/
theorem le_wassersteinE_one_of_dual {P Q : Measure B} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (L : StrongDual ℝ B) (hL : ‖L‖ ≤ 1) (hP : Integrable (fun z => L z) P)
    (hQ : Integrable (fun z => L z) Q) :
    ENNReal.ofReal |∫ z, L z ∂P - ∫ z, L z ∂Q| ≤ wassersteinE 1 P Q := by
  have hL' : ∀ x y : B, |L x - L y| ≤ ‖x - y‖ := by
    intro x y
    have e : L x - L y = L (x - y) := (map_sub L x y).symm
    rw [e, ← Real.norm_eq_abs]
    calc ‖L (x - y)‖ ≤ ‖L‖ * ‖x - y‖ := ContinuousLinearMap.le_opNorm L (x - y)
      _ ≤ 1 * ‖x - y‖ := by gcongr
      _ = ‖x - y‖ := one_mul _
  refine le_iInf fun π => ?_
  have hπ : IsProbabilityMeasure π.1 := IsCoupling.isProbabilityMeasure π.2
  have e1 : ∫ z, L z ∂P = ∫ z, L z.1 ∂π.1 := by
    have := integral_map (μ := π.1) (φ := Prod.fst) (f := fun z : B => L z) measurable_fst.aemeasurable
      (by rw [π.2.1]; exact L.continuous.aestronglyMeasurable)
    rwa [π.2.1] at this
  have e2 : ∫ z, L z ∂Q = ∫ z, L z.2 ∂π.1 := by
    have := integral_map (μ := π.1) (φ := Prod.snd) (f := fun z : B => L z) measurable_snd.aemeasurable
      (by rw [π.2.2]; exact L.continuous.aestronglyMeasurable)
    rwa [π.2.2] at this
  have hPfst : Integrable (fun z : B => L z) (Measure.map Prod.fst π.1) := by
    rw [π.2.1]; exact hP
  have hQsnd : Integrable (fun z : B => L z) (Measure.map Prod.snd π.1) := by
    rw [π.2.2]; exact hQ
  have hi1 : Integrable (fun z : B × B => L z.1) π.1 := hPfst.comp_measurable measurable_fst
  have hi2 : Integrable (fun z : B × B => L z.2) π.1 := hQsnd.comp_measurable measurable_snd
  have hmain : ENNReal.ofReal |∫ z, L z ∂P - ∫ z, L z ∂Q| ≤ ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π.1 := by
    rw [e1, e2, ← integral_sub hi1 hi2, ← Real.norm_eq_abs]
    calc ENNReal.ofReal ‖∫ z, (L z.1 - L z.2) ∂π.1‖
        ≤ ENNReal.ofReal (∫ z, ‖L z.1 - L z.2‖ ∂π.1) :=
          ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)
      _ = ∫⁻ z, ‖L z.1 - L z.2‖ₑ ∂π.1 := ofReal_integral_norm_eq_lintegral_enorm (hi1.sub hi2)
      _ ≤ _ := by
          refine lintegral_mono fun z => ?_
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact hL' _ _)
  simp only [Real.rpow_one, div_one, ENNReal.rpow_one]
  exact hmain

/-- Translation sandwich: `W_p(Law(X+h), Q)` is finite and within `W_p(Law X, Q)` of `‖h‖`,
provided `W_p(Law X, Q) < ∞` and `‖X‖` is integrable. -/
theorem wassersteinE_translate_sandwich {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → B) (hX : AEMeasurable X P)
    (hint : Integrable (fun ω => ‖X ω‖) P) (h : B) (Q : Measure B) [IsProbabilityMeasure Q]
    (p : ℝ) (hp : 1 ≤ p) (hfin : wassersteinE p (law P X) Q ≠ ⊤) :
    wassersteinE p (law P (fun ω => X ω + h)) Q ≠ ⊤ ∧
      |(wassersteinE p (law P (fun ω => X ω + h)) Q).toReal - ‖h‖| ≤
        (wassersteinE p (law P X) Q).toReal := by
  have hXh : AEMeasurable (fun ω => X ω + h) P := hX.add_const h
  -- upper bound on `W_p(Law(X+h), Law X)`
  have hX0 : law P (fun ω => X ω + 0) = law P X := by simp only [add_zero]
  have hup1 : wassersteinE p (law P (fun ω => X ω + h)) (law P X) ≤ ENNReal.ofReal ‖h‖ := by
    have h0 := wassersteinE_translate P p hp X hX h 0
    rw [hX0, sub_zero] at h0
    exact h0
  have hle : wassersteinE p (law P (fun ω => X ω + h)) Q ≤
      ENNReal.ofReal ‖h‖ + wassersteinE p (law P X) Q :=
    (wassersteinE_triangle p hp (law P (fun ω => X ω + h)) (law P X) Q).trans (add_le_add hup1 le_rfl)
  have hbne : ENNReal.ofReal ‖h‖ + wassersteinE p (law P X) Q ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hfin⟩
  have hane : wassersteinE p (law P (fun ω => X ω + h)) Q ≠ ⊤ := ne_top_of_le_ne_top hbne hle
  -- lower bound through a norming functional
  obtain ⟨L, hL1, hLh0⟩ := exists_dual_vector'' ℝ h
  have hLh : L h = ‖h‖ := by simpa using hLh0
  have hLX : Integrable (fun ω => L (X ω)) P := by
    refine Integrable.mono' (hint.const_mul ‖L‖)
      (L.continuous.aestronglyMeasurable.comp_aemeasurable hX) (ae_of_all _ fun ω => ?_)
    exact ContinuousLinearMap.le_opNorm L (X ω)
  have hLXh : Integrable (fun ω => L (X ω + h)) P := by
    have e : (fun ω => L (X ω + h)) = fun ω => L (X ω) + L h := by
      funext ω; rw [map_add]
    rw [e]
    exact hLX.add (integrable_const _)
  have hPi : Integrable (fun z => L z) (law P (fun ω => X ω + h)) :=
    (integrable_map_measure L.continuous.aestronglyMeasurable hXh).2 hLXh
  have hQi : Integrable (fun z => L z) (law P X) :=
    (integrable_map_measure L.continuous.aestronglyMeasurable hX).2 hLX
  have hdiff : ∫ z, L z ∂(law P (fun ω => X ω + h)) - ∫ z, L z ∂(law P X) = ‖h‖ := by
    have h1 : ∫ z, L z ∂(law P (fun ω => X ω + h)) = ∫ ω, L (X ω) ∂P + L h := by
      rw [integral_map hXh L.continuous.aestronglyMeasurable]
      have e : (fun ω => L (X ω + h)) = fun ω => L (X ω) + L h := by
        funext ω; rw [map_add]
      rw [e, integral_add hLX (integrable_const (L h))]
      simp
    have h2 : ∫ z, L z ∂(law P X) = ∫ ω, L (X ω) ∂P :=
      integral_map hX L.continuous.aestronglyMeasurable
    rw [h1, h2]
    linarith
  have hW1 : ENNReal.ofReal ‖h‖ ≤ wassersteinE 1 (law P (fun ω => X ω + h)) (law P X) := by
    have := le_wassersteinE_one_of_dual L hL1 hPi hQi
    rw [hdiff, abs_norm] at this
    exact this
  have hlow : ENNReal.ofReal ‖h‖ ≤
      wassersteinE p (law P (fun ω => X ω + h)) Q + wassersteinE p (law P X) Q := by
    calc ENNReal.ofReal ‖h‖ ≤ wassersteinE 1 (law P (fun ω => X ω + h)) (law P X) := hW1
      _ ≤ wassersteinE p (law P (fun ω => X ω + h)) (law P X) :=
          wassersteinE_mono 1 p le_rfl hp (law P (fun ω => X ω + h)) (law P X)
      _ ≤ wassersteinE p (law P (fun ω => X ω + h)) Q + wassersteinE p Q (law P X) :=
          wassersteinE_triangle p hp (law P (fun ω => X ω + h)) Q (law P X)
      _ = wassersteinE p (law P (fun ω => X ω + h)) Q + wassersteinE p (law P X) Q := by
          rw [wassersteinE_comm' p Q (law P X)]
  have hup_r : (wassersteinE p (law P (fun ω => X ω + h)) Q).toReal ≤
      ‖h‖ + (wassersteinE p (law P X) Q).toReal := by
    have := ENNReal.toReal_mono hbne hle
    rwa [ENNReal.toReal_add ENNReal.ofReal_ne_top hfin, ENNReal.toReal_ofReal (norm_nonneg h)] at this
  have hlow_r : ‖h‖ ≤ (wassersteinE p (law P (fun ω => X ω + h)) Q).toReal +
      (wassersteinE p (law P X) Q).toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hane, hfin⟩) hlow
    rwa [ENNReal.toReal_add hane hfin, ENNReal.toReal_ofReal (norm_nonneg h)] at this
  exact ⟨hane, abs_le.2 ⟨by linarith, by linarith⟩⟩

/-- `smoothConstant` is positive in every nonzero direction (for any `G`, `k ≥ 1`). -/
theorem smoothConstant_pos_of_aemeasurable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : Ω → B) (hG : AEMeasurable G P) (k : ℕ) (hk : 1 ≤ k) (h : B)
    (hh : h ≠ 0) : 0 < smoothConstant P k G h := by
  obtain ⟨L, hL1, hLh0⟩ := exists_dual_vector'' ℝ h
  have hLh : L h = ‖h‖ := by simpa using hLh0
  have hhn : 0 < ‖h‖ := norm_pos_iff.2 hh
  have hψ : ∀ x : ℝ, Continuous fun z : B => Real.cos (x * L z) := fun x =>
    Real.continuous_cos.comp (continuous_const.mul L.continuous)
  have hcont : Continuous fun x : ℝ => ∫ ω, Real.cos (x * L (G ω)) ∂P := by
    refine continuous_of_dominated (F := fun x ω => Real.cos (x * L (G ω)))
      (bound := fun _ => (1:ℝ)) (fun x => (hψ x).aestronglyMeasurable.comp_aemeasurable hG)
      (fun x => ae_of_all _ fun ω => ?_) (integrable_const (1:ℝ)) (ae_of_all _ fun ω => ?_)
    · simp only [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    · exact Real.continuous_cos.comp (continuous_id.mul continuous_const)
  have h0 : (0:ℝ) < ∫ ω, Real.cos ((0:ℝ) * L (G ω)) ∂P := by simp
  have hev : ∀ᶠ x in 𝓝 (0:ℝ), (0:ℝ) < ∫ ω, Real.cos (x * L (G ω)) ∂P :=
    (hcont.tendsto 0).eventually (lt_mem_nhds h0)
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨lam, hlam0, hlam1, hpos⟩ : ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
      0 < ∫ ω, Real.cos (lam * L (G ω)) ∂P := by
    refine ⟨min (δ / 2) 1, lt_min (half_pos hδ0) one_pos, min_le_right _ _, hδ ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min (half_pos hδ0) one_pos)]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ0)
  have hnorm : ‖lam • L‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
    nlinarith [norm_nonneg L]
  have hmem := sin_dual_mem (lam • L) hnorm k
  have hd : ∀ z : B, HasFDerivAt (fun z => Real.sin ((lam • L) z))
      (Real.cos ((lam • L) z) • (lam • L)) z :=
    fun z => (lam • L).hasFDerivAt.sin
  have hderiv : ∀ z : B, fderiv ℝ (fun z => (1 / ((k:ℝ) + 1)) * Real.sin ((lam • L) z)) z h
      = (1 / ((k:ℝ) + 1)) * (lam * ‖h‖ * Real.cos (lam * L z)) := by
    intro z
    rw [((hd z).const_mul (1 / ((k:ℝ) + 1))).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hLh]
    ring
  have hle := integral_fderiv_le_smoothConstant P hk hmem G h
  simp only [hderiv] at hle
  have hI : ∫ ω, (1 / ((k:ℝ) + 1)) * (lam * ‖h‖ * Real.cos (lam * L (G ω))) ∂P
      = (1 / ((k:ℝ) + 1)) * ((lam * ‖h‖) * ∫ ω, Real.cos (lam * L (G ω)) ∂P) := by
    rw [integral_const_mul, integral_const_mul]
  have hpos' : 0 < (1 / ((k:ℝ) + 1)) * ((lam * ‖h‖) * ∫ ω, Real.cos (lam * L (G ω)) ∂P) :=
    mul_pos (by positivity) (mul_pos (mul_pos hlam0 hhn) hpos)
  rw [hI] at hle
  exact lt_of_lt_of_le hpos' hle

/-- Lemma 4.27 (expansion) with `X` on `(Ω, P)` and `G` on `(Ω', P')`. -/
theorem smooth_translation_expansion_sep {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω → B) (G : Ω' → B) (hX : AEMeasurable X P) (hG : AEMeasurable G P')
    (a h : B) (r : ℝ) (hr : 0 < r) (k : ℕ) (hk : 2 ≤ k) (Φ : B → ℝ) (hΦ : Φ ∈ CbUnitBall B k) :
    |∫ ω, Φ (X ω + a) ∂P - ∫ ω, Φ (G ω) ∂P' - r * ∫ ω, fderiv ℝ Φ (G ω) h ∂P'| ≤
      smoothDist k (law P X) (law P' G) + ‖a - r • h‖ + (1 / 2) * r ^ 2 * ‖h‖ ^ 2 := by
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hDc : Continuous fun z => fderiv ℝ Φ z h :=
    (hΦ.1.continuous_fderiv (by norm_cast; omega)).clm_apply continuous_const
  have hX' : AEMeasurable (fun w : Ω × Ω' => X w.1) (P.prod P') :=
    hX.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hG' : AEMeasurable (fun w : Ω × Ω' => G w.2) (P.prod P') :=
    hG.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have key : |∫ w, Φ (X w.1 + a) ∂(P.prod P') - ∫ w, Φ (G w.2) ∂(P.prod P') -
      r * ∫ w, fderiv ℝ Φ (G w.2) h ∂(P.prod P')| ≤
      smoothDist k (law (P.prod P') (fun w : Ω × Ω' => X w.1))
        (law (P.prod P') (fun w : Ω × Ω' => G w.2)) + ‖a - r • h‖ + (1 / 2) * r ^ 2 * ‖h‖ ^ 2 :=
    smooth_translation_expansion (P.prod P') (fun w : Ω × Ω' => X w.1) (fun w : Ω × Ω' => G w.2)
      hX' hG' a h r hr k hk Φ hΦ
  have e1 : ∫ w, Φ (X w.1 + a) ∂(P.prod P') = ∫ ω, Φ (X ω + a) ∂P :=
    integral_fst_prod_aux P P' (fun ω => Φ (X ω + a))
      (hΦc.aestronglyMeasurable.comp_aemeasurable (hX.add_const a))
  have e2 : ∫ w, Φ (G w.2) ∂(P.prod P') = ∫ ω, Φ (G ω) ∂P' :=
    integral_snd_prod_aux P P' (fun ω => Φ (G ω))
      (hΦc.aestronglyMeasurable.comp_aemeasurable hG)
  have e3 : ∫ w, fderiv ℝ Φ (G w.2) h ∂(P.prod P') = ∫ ω, fderiv ℝ Φ (G ω) h ∂P' :=
    integral_snd_prod_aux P P' (fun ω => fderiv ℝ Φ (G ω) h)
      (hDc.aestronglyMeasurable.comp_aemeasurable hG)
  have e4 : law (P.prod P') (fun w : Ω × Ω' => X w.1) = law P X := law_fst_prod_aux P P' X hX
  have e5 : law (P.prod P') (fun w : Ω × Ω' => G w.2) = law P' G := law_snd_prod_aux P P' G hG
  rw [e1, e2, e3, e4, e5] at key
  exact key

/-- Lemma 4.27 (distance) with `X` on `(Ω, P)` and `G` on `(Ω', P')`. -/
theorem smooth_translation_distance_sep {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω → B) (G : Ω' → B) (hX : AEMeasurable X P) (hG : AEMeasurable G P')
    (a h : B) (r : ℝ) (hr : 0 < r) (k : ℕ) (hk : 2 ≤ k) :
    |smoothDist k (law P (fun ω => X ω + a)) (law P' G) - r * smoothConstant P' k G h| ≤
      smoothDist k (law P X) (law P' G) + ‖a - r • h‖ + (1 / 2) * r ^ 2 * ‖h‖ ^ 2 := by
  have hX' : AEMeasurable (fun w : Ω × Ω' => X w.1) (P.prod P') :=
    hX.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hG' : AEMeasurable (fun w : Ω × Ω' => G w.2) (P.prod P') :=
    hG.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have key : |smoothDist k (law (P.prod P') (fun w : Ω × Ω' => X w.1 + a))
      (law (P.prod P') (fun w : Ω × Ω' => G w.2)) -
      r * smoothConstant (P.prod P') k (fun w : Ω × Ω' => G w.2) h| ≤
      smoothDist k (law (P.prod P') (fun w : Ω × Ω' => X w.1))
        (law (P.prod P') (fun w : Ω × Ω' => G w.2)) + ‖a - r • h‖ + (1 / 2) * r ^ 2 * ‖h‖ ^ 2 :=
    smooth_translation_distance (P.prod P') (fun w : Ω × Ω' => X w.1) (fun w : Ω × Ω' => G w.2)
      hX' hG' a h r hr k hk
  have e4 : law (P.prod P') (fun w : Ω × Ω' => X w.1 + a) = law P (fun ω => X ω + a) :=
    law_fst_prod_aux P P' (fun ω => X ω + a) (hX.add_const a)
  have e5 : law (P.prod P') (fun w : Ω × Ω' => G w.2) = law P' G := law_snd_prod_aux P P' G hG
  have e6 : law (P.prod P') (fun w : Ω × Ω' => X w.1) = law P X := law_fst_prod_aux P P' X hX
  have e7 : smoothConstant (P.prod P') k (fun w : Ω × Ω' => G w.2) h = smoothConstant P' k G h := by
    unfold smoothConstant
    congr 1
    funext Φ'
    exact integral_snd_prod_aux P P' (fun ω => fderiv ℝ Φ'.1 (G ω) h)
      ((((Φ'.2.1).continuous_fderiv (by norm_cast; omega)).clm_apply continuous_const).aestronglyMeasurable.comp_aemeasurable hG)
  rw [e4, e5, e6, e7] at key
  exact key

end Abstract

/-- The scalar estimate behind clauses 1 and 2: for fixed `A, B, D ≥ 0` there is `C > 0` with
`(A N^{-1/2} + B √(log N)/√N + ½ (log N/√N)² D) / (log N/√N) ≤ C/√(log N)` for all `N ≥ 2`. -/
theorem div_bound (A B D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (A * (N : ℝ) ^ (-(1 : ℝ) / 2) + B * (Real.sqrt (Real.log N) / Real.sqrt N) +
          (1 / 2) * (Real.log N / Real.sqrt N) ^ 2 * D) / (Real.log N / Real.sqrt N) ≤
        C / Real.sqrt (Real.log N) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu0 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 hl2
  have hC : 0 < A / Real.sqrt (Real.log 2) + B + 3 * D + 1 := by
    have h1 := div_nonneg hA hu0.le
    linarith
  refine ⟨A / Real.sqrt (Real.log 2) + B + 3 * D + 1, hC, fun N hN => ?_⟩
  have hx2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hx0 : (0:ℝ) < (N:ℝ) := by linarith
  have hlogx : Real.log 2 ≤ Real.log (N:ℝ) := Real.log_le_log (by norm_num) hx2
  have hlogpos : 0 < Real.log (N:ℝ) := lt_of_lt_of_le hl2 hlogx
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = Real.sqrt (Real.log (N:ℝ)) := ⟨_, rfl⟩
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = Real.sqrt (N:ℝ) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht_def]; exact Real.sqrt_pos.2 hlogpos
  have hs0 : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.2 hx0
  have hs2 : s ^ 2 = (N:ℝ) := by rw [hs_def]; exact Real.sq_sqrt hx0.le
  have ht2 : t ^ 2 = Real.log (N:ℝ) := by rw [ht_def]; exact Real.sq_sqrt hlogpos.le
  have hu_le : Real.sqrt (Real.log 2) ≤ t := by rw [ht_def]; exact Real.sqrt_le_sqrt hlogx
  have hpow : (N:ℝ) ^ (-(1:ℝ) / 2) = 1 / s := by
    rw [hs_def, show -(1:ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow,
      one_div]
  -- cube-root bound: `log N ≤ 3 N^{1/3}`, `t^6 ≤ 27 N = 27 s^2`
  obtain ⟨y, hy_def⟩ : ∃ y : ℝ, y = (N:ℝ) ^ ((1:ℝ) / 3) := ⟨_, rfl⟩
  have hy_nonneg : 0 ≤ y := by rw [hy_def]; exact Real.rpow_nonneg hx0.le _
  have hy3 : y ^ 3 = (N:ℝ) := by
    rw [hy_def, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hlog_y : Real.log (N:ℝ) ≤ 3 * y := by
    have h := Real.log_le_rpow_div hx0.le (by norm_num : (0:ℝ) < 1 / 3)
    have e : (N:ℝ) ^ ((1:ℝ) / 3) / (1 / 3) = 3 * (N:ℝ) ^ ((1:ℝ) / 3) := by ring
    rw [hy_def]
    linarith
  have ht6 : t ^ 6 ≤ 27 * s ^ 2 := by
    have h1 : t ^ 2 ≤ 3 * y := by rw [ht2]; exact hlog_y
    have h2 : t ^ 2 * t ^ 2 ≤ (3 * y) * (3 * y) :=
      mul_le_mul h1 h1 (sq_nonneg t) (by linarith)
    have h3 : t ^ 2 * t ^ 2 * t ^ 2 ≤ (3 * y) * (3 * y) * (3 * y) :=
      mul_le_mul h2 h1 (sq_nonneg t) (mul_nonneg (by linarith) (by linarith))
    have h7 : (3 * y) * (3 * y) * (3 * y) = 27 * (N:ℝ) := by rw [← hy3]; ring
    have h6 : t ^ 6 = t ^ 2 * t ^ 2 * t ^ 2 := by ring
    rw [h6, hs2]
    linarith
  have ht3 : t ^ 3 ≤ 6 * s := by
    by_contra hcon
    push_neg at hcon
    have h6s : 0 ≤ 6 * s := by linarith
    have hsq : 6 * s * (6 * s) < t ^ 3 * t ^ 3 := by nlinarith [hcon, h6s]
    have e1 : t ^ 6 = t ^ 3 * t ^ 3 := by ring
    have e2 : 6 * s * (6 * s) = 36 * s ^ 2 := by ring
    linarith [sq_nonneg s]
  have hE : (A * (1 / s) + B * (t / s) + (1 / 2) * (t ^ 2 / s) ^ 2 * D) / (t ^ 2 / s)
      = A / t ^ 2 + B / t + (1 / 2) * D * t ^ 2 / s := by
    have hs' : s ≠ 0 := hs0.ne'
    have ht' : t ≠ 0 := ht0.ne'
    field_simp
  rw [hpow, ← ht_def, ← hs_def, ← ht2, hE]
  have hta : A / t ^ 2 ≤ A / Real.sqrt (Real.log 2) / t := by
    rw [div_div, div_le_div_iff₀ (pow_pos ht0 2) (mul_pos hu0 ht0)]
    exact mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_right hu_le ht0.le]) hA
  have htc : (1 / 2) * D * t ^ 2 / s ≤ 3 * D / t := by
    rw [div_le_div_iff₀ hs0 ht0]
    nlinarith [mul_le_mul_of_nonneg_left ht3 hD]
  have hsum : A / t ^ 2 + B / t + (1 / 2) * D * t ^ 2 / s ≤
      (A / Real.sqrt (Real.log 2) + B + 3 * D) / t := by
    have e : (A / Real.sqrt (Real.log 2) + B + 3 * D) / t =
        A / Real.sqrt (Real.log 2) / t + B / t + 3 * D / t := by ring
    rw [e]
    linarith
  have hfin : (A / Real.sqrt (Real.log 2) + B + 3 * D) / t ≤
      (A / Real.sqrt (Real.log 2) + B + 3 * D + 1) / t := by
    rw [div_le_div_iff₀ ht0 ht0]
    exact mul_le_mul_of_nonneg_right (by linarith) ht0.le
  linarith [hsum, hfin]

end HRS.ME.Bias
