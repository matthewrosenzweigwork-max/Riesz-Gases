import Mathlib

/-!
# Packet Q41, helper 1: a stationary-type Gaussian sequence with uniformly nondegenerate
covariance is a.s. unbounded

Abstract probabilistic input of Proposition 5.18(ii) (`HRS.unbounded_stationary_sup`): if
`W : ℕ → Ω → ℝ` is a centred Gaussian process (all finite subfamilies jointly Gaussian) such that
every finite linear combination `∑ w_i W_i` has variance `≥ c₀ ∑ w_i²`, then
`ℙ(∀ n, |W_n| ≤ M) = 0` for every `M`.  Proof: the residual `ξ = W_L - ∑ a_i W_i` of the
`L²`-regression of `W_L` on `W_0, …, W_{L-1}` is independent of `(W_0,…,W_{L-1})` and `N(0,v)`
with `v ≥ c₀`; hence `ℙ(|W_L| ≤ M ∣ past) ≤ 1 - κ` with `κ = κ(M, c₀) > 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Matrix

namespace HRS.Q41

/-- The Gaussian tail constant `κ(M, c₀)`. -/
def q41_kappa (M c0 : ℝ) : ℝ :=
  min ((gaussianReal 0 1).real (Set.Ioi (M / Real.sqrt c0)))
    ((gaussianReal 0 1).real (Set.Iio (-(M / Real.sqrt c0))))

lemma q41_std_Ioi_pos (x : ℝ) : 0 < (gaussianReal 0 1).real (Set.Ioi x) := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  rw [measureReal_def]
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  intro h
  have h1 : volume (Set.Ioi x) = 0 := gaussianReal_absolutelyContinuous' 0 hv h
  simp at h1

lemma q41_std_Iio_pos (x : ℝ) : 0 < (gaussianReal 0 1).real (Set.Iio x) := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  rw [measureReal_def]
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  intro h
  have h1 : volume (Set.Iio x) = 0 := gaussianReal_absolutelyContinuous' 0 hv h
  simp at h1

lemma q41_kappa_pos {M c0 : ℝ} : 0 < q41_kappa M c0 :=
  lt_min (q41_std_Ioi_pos _) (q41_std_Iio_pos _)

lemma q41_kappa_le_one (M c0 : ℝ) : q41_kappa M c0 ≤ 1 :=
  (min_le_left _ _).trans (measureReal_le_one)

/-- scaling: `N(0,v)` is the image of `N(0,1)` under `z ↦ √v z`. -/
lemma q41_gauss_scale (v : ℝ≥0) :
    gaussianReal 0 v = (gaussianReal 0 1).map (fun z => Real.sqrt v * z) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt]

lemma q41_gauss_Ioi_ge {M c0 : ℝ} (hM : 0 < M) (hc0 : 0 < c0) (v : ℝ≥0) (hv : c0 ≤ (v : ℝ)) :
    q41_kappa M c0 ≤ (gaussianReal 0 v).real (Set.Ioi M) := by
  refine (min_le_left _ _).trans ?_
  have hvpos : 0 < Real.sqrt v := Real.sqrt_pos.2 (lt_of_lt_of_le hc0 hv)
  have hsq : Real.sqrt c0 ≤ Real.sqrt v := Real.sqrt_le_sqrt hv
  have hc0s : 0 < Real.sqrt c0 := Real.sqrt_pos.2 hc0
  rw [q41_gauss_scale v, measureReal_def, measureReal_def,
    Measure.map_apply (by fun_prop) measurableSet_Ioi]
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
  intro z hz
  simp only [Set.mem_Ioi, Set.mem_preimage] at hz ⊢
  have h1 : M ≤ M / Real.sqrt c0 * Real.sqrt v := by
    calc M = M / Real.sqrt c0 * Real.sqrt c0 := by field_simp
      _ ≤ M / Real.sqrt c0 * Real.sqrt v :=
        mul_le_mul_of_nonneg_left hsq (div_nonneg hM.le hc0s.le)
  have h2 : Real.sqrt v * (M / Real.sqrt c0) < Real.sqrt v * z := mul_lt_mul_of_pos_left hz hvpos
  linarith [mul_comm (Real.sqrt v) (M / Real.sqrt c0)]

lemma q41_gauss_Iio_ge {M c0 : ℝ} (hM : 0 < M) (hc0 : 0 < c0) (v : ℝ≥0) (hv : c0 ≤ (v : ℝ)) :
    q41_kappa M c0 ≤ (gaussianReal 0 v).real (Set.Iio (-M)) := by
  refine (min_le_right _ _).trans ?_
  have hvpos : 0 < Real.sqrt v := Real.sqrt_pos.2 (lt_of_lt_of_le hc0 hv)
  have hsq : Real.sqrt c0 ≤ Real.sqrt v := Real.sqrt_le_sqrt hv
  have hc0s : 0 < Real.sqrt c0 := Real.sqrt_pos.2 hc0
  rw [q41_gauss_scale v, measureReal_def, measureReal_def,
    Measure.map_apply (by fun_prop) measurableSet_Iio]
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
  intro z hz
  simp only [Set.mem_Iio, Set.mem_preimage] at hz ⊢
  have h1 : M / Real.sqrt c0 * Real.sqrt c0 ≤ M / Real.sqrt c0 * Real.sqrt v :=
    mul_le_mul_of_nonneg_left hsq (div_nonneg hM.le hc0s.le)
  have h1' : M / Real.sqrt c0 * Real.sqrt c0 = M := by field_simp
  have h2 : Real.sqrt v * z < Real.sqrt v * (-(M / Real.sqrt c0)) := mul_lt_mul_of_pos_left hz hvpos
  nlinarith [mul_comm (Real.sqrt v) (M / Real.sqrt c0)]

/-- A centred Gaussian of variance `≥ c₀` puts mass `≤ 1 - κ` on every interval of length `2M`. -/
lemma q41_slice {M c0 : ℝ} (hM : 0 < M) (hc0 : 0 < c0) (v : ℝ≥0) (hv : c0 ≤ (v : ℝ)) (b : ℝ) :
    (gaussianReal 0 v).real {t | |b + t| ≤ M} ≤ 1 - q41_kappa M c0 := by
  haveI : IsProbabilityMeasure (gaussianReal 0 v) := inferInstance
  have hS : MeasurableSet {t : ℝ | |b + t| ≤ M} :=
    measurableSet_le (by fun_prop) measurable_const
  have hcompl : q41_kappa M c0 ≤ (gaussianReal 0 v).real {t : ℝ | |b + t| ≤ M}ᶜ := by
    rcases le_or_gt 0 b with hb | hb
    · refine (q41_gauss_Ioi_ge hM hc0 v hv).trans (measureReal_mono ?_)
      intro t ht
      simp only [Set.mem_Ioi] at ht
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
      rw [lt_abs]
      left; linarith
    · refine (q41_gauss_Iio_ge hM hc0 v hv).trans (measureReal_mono ?_)
      intro t ht
      simp only [Set.mem_Iio] at ht
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
      rw [lt_abs]
      right; linarith
  have := probReal_compl_eq_one_sub (μ := gaussianReal 0 v) hS
  linarith

section Gauss

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A centred Gaussian process `W` all of whose finite linear combinations have variance
`≥ c₀ ∑ w_i²` (uniform nondegeneracy). -/
structure NondegGauss (W : ℕ → Ω → ℝ) (P : Measure Ω) (c0 : ℝ) : Prop where
  gauss : IsGaussianProcess W P
  meas : ∀ i, Measurable (W i)
  centered : ∀ i, ∫ ω, W i ω ∂P = 0
  var : ∀ (L : ℕ) (w : Fin L → ℝ), c0 * ∑ i, w i ^ 2 ≤
    variance (fun ω => ∑ i : Fin L, w i * W i ω) P

variable {W : ℕ → Ω → ℝ} {P : Measure Ω} {c0 : ℝ}

lemma NondegGauss.memLp (h : NondegGauss W P c0) (i : ℕ) : MemLp (W i) 2 P :=
  (h.gauss.hasGaussianLaw_eval i).memLp_two

lemma NondegGauss.isProb (h : NondegGauss W P c0) : IsProbabilityMeasure P :=
  h.gauss.isProbabilityMeasure

lemma q41_var_eq_quad {W : ℕ → Ω → ℝ} {P : Measure Ω} (hG : IsGaussianProcess W P)
    (hmeas : ∀ i, Measurable (W i)) (L : ℕ) (w : Fin L → ℝ) :
    variance (fun ω => ∑ i : Fin L, w i * W i ω) P =
      ∑ i, ∑ j, w i * w j * cov[W i, W j; P] := by
  haveI := hG.isProbabilityMeasure
  have hmemLp : ∀ i, MemLp (W i) 2 P := fun i => (hG.hasGaussianLaw_eval i).memLp_two
  have hm : AEMeasurable (fun ω => ∑ i : Fin L, w i * W i ω) P :=
    Finset.aemeasurable_fun_sum _ fun i _ => ((hmeas i).const_mul (w i)).aemeasurable
  rw [← covariance_self hm]
  have hX : ∀ i : Fin L, MemLp (fun ω => w i * W i ω) 2 P := fun i => (hmemLp i).const_mul (w i)
  rw [covariance_fun_sum_fun_sum hX hX]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]
  ring

lemma NondegGauss.var_eq_quad (h : NondegGauss W P c0) (L : ℕ) (w : Fin L → ℝ) :
    variance (fun ω => ∑ i : Fin L, w i * W i ω) P =
      ∑ i, ∑ j, w i * w j * cov[W i, W j; P] :=
  q41_var_eq_quad h.gauss h.meas L w

lemma NondegGauss.exists_regression (h : NondegGauss W P c0) (hc0 : 0 < c0) (L : ℕ) :
    ∃ a : Fin L → ℝ, ∀ j : Fin L, cov[W L, W j; P] = ∑ i, a i * cov[W i, W j; P] := by
  classical
  set G : Matrix (Fin L) (Fin L) ℝ := Matrix.of fun i j => cov[W i, W j; P] with hG
  have hherm : G.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp [hG, covariance_comm]
  have hpd : G.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm fun x hx => ?_
    have hq : star x ⬝ᵥ (G *ᵥ x) = ∑ i, ∑ j, x i * x j * cov[W i, W j; P] := by
      simp only [dotProduct, Matrix.mulVec, hG, Matrix.of_apply, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hq, ← h.var_eq_quad L x]
    have hxs : 0 < ∑ i, x i ^ 2 := by
      by_contra hneg
      push_neg at hneg
      apply hx
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).1
        (le_antisymm hneg (Finset.sum_nonneg fun i _ => sq_nonneg (x i))) i (Finset.mem_univ i)
      simpa using this
    exact lt_of_lt_of_le (mul_pos hc0 hxs) (h.var L x)
  have hU : IsUnit G := hpd.isUnit
  refine ⟨G⁻¹ *ᵥ fun j : Fin L => cov[W L, W j; P], fun j => ?_⟩
  have h1 : G *ᵥ (G⁻¹ *ᵥ fun j : Fin L => cov[W L, W j; P]) = fun j : Fin L => cov[W L, W j; P] := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G ((Matrix.isUnit_iff_isUnit_det G).1 hU),
      Matrix.one_mulVec]
  have h2 := congrFun h1 j
  have hGji : ∀ i j : Fin L, G j i = cov[W j, W i; P] := fun _ _ => rfl
  simp only [Matrix.mulVec, dotProduct, hGji] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct]
  rw [covariance_comm (X := W j) (Y := W i) (μ := P)]
  ring

/-- The regression residual `ξ = W_L - ∑ a_i W_i`. -/
def resid (W : ℕ → Ω → ℝ) (L : ℕ) (a : Fin L → ℝ) (ω : Ω) : ℝ :=
  W L ω - ∑ i : Fin L, a i * W i ω

lemma NondegGauss.resid_gauss (h : NondegGauss W P c0) (L : ℕ) (a : Fin L → ℝ) :
    IsGaussianProcess (Sum.elim (fun i : Fin L => W i) (fun _ : Unit => resid W L a)) P := by
  refine IsGaussianProcess.of_isGaussianProcess h.gauss ?_
  rintro (i | u)
  · refine ⟨{(i : ℕ)}, ContinuousLinearMap.proj ⟨(i : ℕ), by simp⟩, fun ω => ?_⟩
    simp [Finset.restrict_def]
  · refine ⟨Finset.range (L + 1),
      ContinuousLinearMap.proj ⟨L, by simp⟩ -
        ∑ i : Fin L, a i • (ContinuousLinearMap.proj (⟨(i : ℕ), by simp⟩ :
          (Finset.range (L + 1)))), fun ω => ?_⟩
    simp [resid, Finset.restrict_def]

lemma NondegGauss.cov_resid (h : NondegGauss W P c0) (hc0 : 0 < c0) (L : ℕ) (a : Fin L → ℝ)
    (ha : ∀ j : Fin L, cov[W L, W j; P] = ∑ i, a i * cov[W i, W j; P]) (j : Fin L) :
    cov[W j, resid W L a; P] = 0 := by
  haveI := h.isProb
  have hmem : ∀ i : Fin L, MemLp (fun ω => a i * W i ω) 2 P := fun i => (h.memLp i).const_mul (a i)
  have hsum : MemLp (fun ω => ∑ i : Fin L, a i * W i ω) 2 P := by
    have := memLp_finsetSum' (Finset.univ : Finset (Fin L)) (fun i _ => hmem i)
    convert this using 1
    ext ω; simp
  unfold resid
  rw [covariance_fun_sub_right (h.memLp j) (h.memLp L) hsum, covariance_fun_sum_right hmem (h.memLp j)]
  simp_rw [covariance_const_mul_right]
  rw [covariance_comm (X := W j) (Y := W L) (μ := P), ha j]
  have : ∀ i : Fin L, cov[W j, W i; P] = cov[W i, W j; P] := fun i => covariance_comm _ _
  simp_rw [this]
  ring

lemma NondegGauss.resid_var (h : NondegGauss W P c0) (hc0 : 0 < c0) (L : ℕ) (a : Fin L → ℝ) :
    c0 ≤ variance (resid W L a) P := by
  set w : Fin (L + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) (fun i => -a i) 1 with hw
  have hfun : (fun ω => ∑ k : Fin (L + 1), w k * W k ω) = resid W L a := by
    funext ω
    rw [Fin.sum_univ_castSucc]
    simp [hw, resid, sub_eq_add_neg, Finset.sum_neg_distrib]
    ring
  have h1 := h.var (L + 1) w
  rw [hfun] at h1
  have h2 : (1 : ℝ) ≤ ∑ k : Fin (L + 1), w k ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    simp only [hw, Fin.snoc_last]
    have : 0 ≤ ∑ i : Fin L, w (Fin.castSucc i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith
  nlinarith

lemma NondegGauss.indep_resid (h : NondegGauss W P c0) (hc0 : 0 < c0) (L : ℕ) (a : Fin L → ℝ)
    (ha : ∀ j : Fin L, cov[W L, W j; P] = ∑ i, a i * cov[W i, W j; P]) :
    IndepFun (fun ω (i : Fin L) => W i ω) (resid W L a) P := by
  have hres_meas : Measurable (resid W L a) := by
    unfold resid
    exact (h.meas L).sub (Finset.measurable_sum (Finset.univ : Finset (Fin L))
      fun (i : Fin L) _ => (h.meas i).const_mul (a i))
  have hXY := h.resid_gauss L a
  have hind := hXY.indepFun_of_covariance_eq_zero (X := fun i : Fin L => W i)
    (Y := fun _ : Unit => resid W L a) (fun i => (h.meas i).aemeasurable)
    (fun _ => hres_meas.aemeasurable) (fun i _ => h.cov_resid hc0 L a ha i)
  have hψ : Measurable (fun f : Unit → ℝ => f ()) := measurable_pi_apply ()
  have hφ : Measurable (id : (Fin L → ℝ) → (Fin L → ℝ)) := measurable_id
  have := hind.comp hφ hψ
  simpa [Function.comp_def] using this

lemma NondegGauss.resid_meas (h : NondegGauss W P c0) (L : ℕ) (a : Fin L → ℝ) :
    Measurable (resid W L a) := by
  unfold resid
  exact (h.meas L).sub (Finset.measurable_sum (Finset.univ : Finset (Fin L))
    fun (i : Fin L) _ => (h.meas i).const_mul (a i))

lemma NondegGauss.resid_mean (h : NondegGauss W P c0) (L : ℕ) (a : Fin L → ℝ) :
    ∫ ω, resid W L a ω ∂P = 0 := by
  haveI := h.isProb
  have hmem : ∀ i : Fin L, Integrable (fun ω => a i * W i ω) P :=
    fun i => (h.memLp i).integrable (by norm_num) |>.const_mul (a i)
  unfold resid
  rw [integral_sub ((h.memLp L).integrable (by norm_num)) (integrable_finset_sum _ fun i _ => hmem i),
    integral_finset_sum _ fun i _ => hmem i]
  simp [integral_const_mul, h.centered]

lemma q41_measurableSet_box (L : ℕ) (M : ℝ) : MeasurableSet {u : Fin L → ℝ | ∀ i, |u i| ≤ M} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const

lemma NondegGauss.step (h : NondegGauss W P c0) (hc0 : 0 < c0) {M : ℝ} (hM : 0 < M) (L : ℕ) :
    P {ω | ∀ i : Fin (L + 1), |W i ω| ≤ M} ≤
      ENNReal.ofReal (1 - q41_kappa M c0) * P {ω | ∀ i : Fin L, |W i ω| ≤ M} := by
  haveI := h.isProb
  obtain ⟨a, ha⟩ := h.exists_regression hc0 L
  have hind := h.indep_resid hc0 L a ha
  set U : Ω → (Fin L → ℝ) := fun ω i => W i ω with hU
  have hUm : Measurable U := measurable_pi_iff.2 fun i => h.meas i
  have hξm : Measurable (resid W L a) := h.resid_meas L a
  have hξG : HasGaussianLaw (resid W L a) P :=
    (h.resid_gauss L a).hasGaussianLaw_eval (Sum.inr ())
  have hlaw : P.map (resid W L a) = gaussianReal 0 (variance (resid W L a) P).toNNReal := by
    rw [hξG.map_eq_gaussianReal]
    have := h.resid_mean L a
    rw [this]
  set v : ℝ≥0 := (variance (resid W L a) P).toNNReal with hv
  have hvc : c0 ≤ (v : ℝ) := by
    rw [hv, Real.coe_toNNReal _ (variance_nonneg _ _)]
    exact h.resid_var hc0 L a
  let B : Set ((Fin L → ℝ) × ℝ) := {p | (∀ i, |p.1 i| ≤ M) ∧ |∑ i, a i * p.1 i + p.2| ≤ M}
  have hBm : MeasurableSet B := by
    refine MeasurableSet.inter ?_ ?_
    · exact (q41_measurableSet_box L M).preimage measurable_fst
    · exact measurableSet_le (f := fun p : (Fin L → ℝ) × ℝ => |∑ i, a i * p.1 i + p.2|)
        (by fun_prop) measurable_const
  have hset : {ω | ∀ i : Fin (L + 1), |W i ω| ≤ M} = (fun ω => (U ω, resid W L a ω)) ⁻¹' B := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, B, hU, Fin.forall_fin_succ' (P := fun i => |W (i : ℕ) ω| ≤ M)]
    simp only [resid, Fin.val_last, Fin.coe_castSucc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by simpa using h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by simpa using h2⟩
  have hbox : {ω | ∀ i : Fin L, |W i ω| ≤ M} = U ⁻¹' {u | ∀ i, |u i| ≤ M} := by
    ext ω; simp [hU]
  rw [hset, hbox, ← Measure.map_apply (hUm.prodMk hξm) hBm,
    (indepFun_iff_map_prod_eq_prod_map_map hUm.aemeasurable hξm.aemeasurable).1 hind,
    Measure.prod_apply hBm, ← Measure.map_apply hUm (q41_measurableSet_box L M), hlaw]
  have hpt : ∀ u : Fin L → ℝ, (gaussianReal 0 v) (Prod.mk u ⁻¹' B) ≤
      Set.indicator {u : Fin L → ℝ | ∀ i, |u i| ≤ M} (fun _ => ENNReal.ofReal (1 - q41_kappa M c0)) u := by
    intro u
    by_cases hu : ∀ i, |u i| ≤ M
    · rw [Set.indicator_of_mem (show u ∈ {u : Fin L → ℝ | ∀ i, |u i| ≤ M} from hu)]
      have hs : Prod.mk u ⁻¹' B = {t : ℝ | |(∑ i, a i * u i) + t| ≤ M} := by
        ext t; simp [B, hu]
      rw [hs]
      have := q41_slice hM hc0 v hvc (∑ i, a i * u i)
      rw [measureReal_def] at this
      calc (gaussianReal 0 v) {t : ℝ | |(∑ i, a i * u i) + t| ≤ M}
          = ENNReal.ofReal ((gaussianReal 0 v) {t : ℝ | |(∑ i, a i * u i) + t| ≤ M}).toReal :=
            (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal this
    · rw [Set.indicator_of_notMem (show u ∉ {u : Fin L → ℝ | ∀ i, |u i| ≤ M} from hu)]
      have hs : Prod.mk u ⁻¹' B = ∅ := by
        ext t; simp [B, hu]
      rw [hs]; simp
  calc ∫⁻ u, (gaussianReal 0 v) (Prod.mk u ⁻¹' B) ∂(P.map U)
      ≤ ∫⁻ u, Set.indicator {u : Fin L → ℝ | ∀ i, |u i| ≤ M}
          (fun _ => ENNReal.ofReal (1 - q41_kappa M c0)) u ∂(P.map U) := lintegral_mono hpt
    _ = ENNReal.ofReal (1 - q41_kappa M c0) * (P.map U) {u | ∀ i, |u i| ≤ M} :=
        lintegral_indicator_const (q41_measurableSet_box L M) _

lemma NondegGauss.measure_box_le (h : NondegGauss W P c0) (hc0 : 0 < c0) {M : ℝ} (hM : 0 < M)
    (L : ℕ) :
    P {ω | ∀ i : Fin L, |W i ω| ≤ M} ≤ ENNReal.ofReal (1 - q41_kappa M c0) ^ L := by
  haveI := h.isProb
  induction L with
  | zero => simp
  | succ L ih =>
    calc P {ω | ∀ i : Fin (L + 1), |W i ω| ≤ M}
        ≤ ENNReal.ofReal (1 - q41_kappa M c0) * P {ω | ∀ i : Fin L, |W i ω| ≤ M} :=
          h.step hc0 hM L
      _ ≤ ENNReal.ofReal (1 - q41_kappa M c0) * ENNReal.ofReal (1 - q41_kappa M c0) ^ L :=
          by gcongr
      _ = _ := by rw [pow_succ']

/-- A uniformly nondegenerate centred Gaussian sequence is almost surely unbounded. -/
theorem NondegGauss.ae_unbounded (h : NondegGauss W P c0) (hc0 : 0 < c0) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ n : ℕ, M < |W n ω| := by
  haveI := h.isProb
  have hM : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ n : ℕ, (k + 1 : ℝ) < |W n ω| := by
    intro k
    have hk : (0 : ℝ) < k + 1 := by positivity
    have hq : ENNReal.ofReal (1 - q41_kappa (k + 1) c0) < 1 := by
      have := q41_kappa_pos (M := (k + 1 : ℝ)) (c0 := c0)
      rw [ENNReal.ofReal_lt_one]; linarith
    have h0 : P {ω | ∀ n : ℕ, |W n ω| ≤ k + 1} = 0 := by
      refine le_antisymm ?_ bot_le
      refine ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) fun L => ?_
      refine le_trans (measure_mono ?_) (h.measure_box_le hc0 hk L)
      intro ω hω i
      exact hω i
    rw [ae_iff]
    convert h0 using 2
    ext ω
    simp [not_lt]
  filter_upwards [ae_all_iff.2 hM] with ω hω M
  obtain ⟨n, hn⟩ := hω ⌈M⌉₊
  exact ⟨n, lt_of_le_of_lt (Nat.le_ceil M) (lt_trans (by linarith) hn)⟩

end Gauss

end HRS.Q41
