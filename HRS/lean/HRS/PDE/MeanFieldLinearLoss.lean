import HRS.PDE.MeanFieldAdjointWiring
import HRS.PDE.MeanFieldLinearResponse
import HRS.PDE.MeanFieldLinearGaussian

/-!
# Corollary 5.3 `C:cor:linear`: loss of the initial law for the linear SPDE (package MF-01, P13c)

See `HRS/PDE/MeanFieldAdjointPlan.md`, packet P13c.  The file proves

* `integrable_norm_of_law_gaussian`: the norm of a random vector with a Gaussian law is integrable
  (Mathlib's Fernique theorem for `ProbabilityTheory.multivariateGaussian`);
* `exists_cov_comparison`: the covariance matrix `M_u` of the Gaussian part is positive semidefinite
  and converges exponentially fast to `stationaryLagCov`, which is positive semidefinite too;
* `exists_initial_part_bound`: exponential decay of the transported initial part;
* `linear_loss_of_initial_law_aux`: Corollary 5.3, wired into `HRS/PDE/MeanField.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.PDE.MFLinear

variable {d : ℕ}

/-! ### A. Probabilistic preliminaries -/

theorem integrable_norm_of_law_gaussian {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p : ℕ} (G : Ω → EuclideanSpace ℝ (Fin p)) (hG : Measurable G)
    (M : Matrix (Fin p) (Fin p) ℝ)
    (hlaw : law P G = ProbabilityTheory.multivariateGaussian 0 M) :
    Integrable (fun ω => ‖G ω‖) P := by
  have h1 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => x)
      (ProbabilityTheory.multivariateGaussian 0 M) :=
    ProbabilityTheory.IsGaussian.integrable_id
  rw [← hlaw] at h1
  have h2 : Integrable (fun ω => G ω) P :=
    (integrable_map_measure h1.aestronglyMeasurable hG.aemeasurable).1 h1
  exact h2.norm

theorem continuous_eval_const {m : ℝ} (φ : Torus d → ℝ)
    (hφ : Summable fun k : NonzeroLattice d =>
      Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) :
    Continuous (fun F : NegSobolev d m => NegSobolev.eval F φ) := by
  classical
  set y : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k with hy
  have hy2 : Summable fun k => y k ^ 2 := by
    refine hφ.congr fun k => ?_
    simp only [hy]; rw [mul_pow, Torus.jp_rpow_sq]
  have hmem : Memℓp y 2 := by
    rw [Torus.memℓp_two_iff]; exact hy2
  let Y : lp (fun _ : NonzeroLattice d => ℝ) 2 := ⟨y, hmem⟩
  have e : ∀ F : NegSobolev d m, NegSobolev.eval F φ =
      inner ℝ Y (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) := by
    intro F
    rw [lp.inner_eq_tsum]
    unfold NegSobolev.eval NegSobolev.fourierCoeff NegSobolev.coord
    refine tsum_congr fun k => ?_
    simp only [hy, Y]
    simp
    ring
  have : (fun F : NegSobolev d m => NegSobolev.eval F φ) =
      fun F => inner ℝ Y (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) := funext e
  rw [this]
  exact continuous_const.inner continuous_id

/-! ### B. Sobolev preliminaries -/

theorem memSobolev_sub {m : ℝ} {f g : Torus d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfm : MemSobolev m f) (hgm : MemSobolev m g) : MemSobolev m (fun x => f x - g x) := by
  refine memSobolev_of_memHs m _ (hfm.1.sub hgm.1) ?_
  rw [ET.coeffOf_sub_fun hf hg]
  exact memHs_sub (hsNormSq_coeffOf m f hfm).1 (hsNormSq_coeffOf m g hgm).1

theorem grad_sub {f g : Torus d → ℝ} (hf : Torus.IsCk 1 f) (hg : Torus.IsCk 1 g) (x : Torus d) :
    Torus.grad (fun y => f y - g y) x = Torus.grad f x - Torus.grad g x := by
  have hf' : ContDiff ℝ 1 (Torus.lift f) := hf
  have hg' : ContDiff ℝ 1 (Torus.lift g) := hg
  unfold Torus.grad
  have : Torus.lift (fun y => f y - g y) = fun z => Torus.lift f z - Torus.lift g z := rfl
  rw [this]
  unfold gradient
  rw [fderiv_fun_sub (hf'.differentiable one_ne_zero _) (hg'.differentiable one_ne_zero _), map_sub]

theorem grad_sub_const (f : Torus d → ℝ) (c : ℝ) (x : Torus d) :
    Torus.grad (fun y => f y - c) x = Torus.grad f x := by
  unfold Torus.grad
  have : Torus.lift (fun y => f y - c) = fun z => Torus.lift f z - c := rfl
  rw [this]
  unfold gradient
  rw [fderiv_sub_const]

theorem isCk_sub_const {f : Torus d → ℝ} {k : ℕ} (hf : Torus.IsCk k f) (c : ℝ) :
    Torus.IsCk k (fun x => f x - c) :=
  hf.sub contDiff_const

theorem isCk_sub {f g : Torus d → ℝ} {k : ℕ} (hf : Torus.IsCk k f) (hg : Torus.IsCk k g) :
    Torus.IsCk k (fun x => f x - g x) :=
  hf.sub hg

/-- Sup bound of the gradient by a high Sobolev norm. -/
theorem exists_grad_sup_le (j : ℕ) (hj : (d : ℝ) / 2 + 1 < j) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ f : Torus d → ℝ, MemSobolev (j : ℝ) f → Torus.IsCk 1 f →
      ∀ x, ‖Torus.grad f x‖ ≤ Cs * sobolevNorm (j : ℝ) f := by
  obtain ⟨C, hC⟩ := cbNorm_le_sobolevNorm (d := d) 1 (j : ℝ) (by simpa using hj)
  refine ⟨max C 0, le_max_right _ _, fun f hf hf1 x => ?_⟩
  have h0 : 0 ≤ sobolevNorm (j : ℝ) f := Real.sqrt_nonneg _
  calc ‖Torus.grad f x‖ ≤ Torus.cbNorm 1 f := MFApriori.norm_grad_le_cbNorm hf1 x
    _ ≤ C * sobolevNorm (j : ℝ) f := hC f hf (by simpa using hf1)
    _ ≤ max C 0 * sobolevNorm (j : ℝ) f := mul_le_mul_of_nonneg_right (le_max_left _ _) h0

/-- `|F(f)| ≤ ‖F‖ ‖f - c‖_{H^m}`: the zero-mass pairing does not see constants. -/
theorem abs_eval_le_sobolev {m : ℝ} (F : NegSobolev d m) (f : Torus d → ℝ) (c : ℝ)
    (hmem : MemSobolev m (fun x => f x - c)) :
    |NegSobolev.eval F f| ≤ ‖F‖ * sobolevNorm m (fun x => f x - c) := by
  have hf2 : MemLp f 2 volume := by
    have := hmem.1.add (memLp_const (c : ℝ) : MemLp (fun _ : Torus d => c) 2 volume)
    have e : ((fun x => f x - c) + fun _ : Torus d => c) = f := by
      funext x; simp
    rwa [e] at this
  have hint : Integrable f := hf2.integrable one_le_two
  have hcoef : ∀ k : NonzeroLattice d, Torus.funRealCoeff (fun x => f x - c) k =
      Torus.funRealCoeff f k := by
    intro k
    unfold Torus.funRealCoeff
    have hL : MemLp (Torus.realMode k) 2 volume :=
      (continuous_realMode' k).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hrm : Integrable (fun x => Torus.realMode k x * f x) := hL.integrable_mul hf2
    have hrc : Integrable (fun x => Torus.realMode k x * c) :=
      ((continuous_realMode' k).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).mul_const c
    have : (fun x => Torus.realMode k x * (f x - c)) =
        fun x => Torus.realMode k x * f x - Torus.realMode k x * c := by
      funext x; ring
    rw [this, integral_sub hrm hrc, integral_mul_const, Torus.integral_realMode]
    ring
  have hev : NegSobolev.eval F f = NegSobolev.eval F (fun x => f x - c) := by
    unfold NegSobolev.eval
    exact tsum_congr fun k => by rw [hcoef k]
  rw [hev]
  refine (NegSobolev.abs_eval_le F _ hmem.2).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  unfold sobolevNorm
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Torus.mean (fun x => f x - c))])

/-! ### C. Real-variable estimate for the entry comparison -/

theorem entry_real (t : ℝ) (ht : 0 ≤ t) (E w : ℝ → ℝ) (B B' m c : ℝ) (hc : 0 < c)
    (hE : ContinuousOn E (Set.Icc 0 t)) (hw : IntegrableOn w (Set.Ici 0))
    (hdiff : ∀ v ∈ Set.Icc 0 t, |E (t - v) - w v| ≤ B * Real.exp (-m * t))
    (hwb : ∀ v, 0 ≤ v → |w v| ≤ B' * Real.exp (-c * v)) :
    |(∫ r in Set.Ioc 0 t, E r) - ∫ v in Set.Ici 0, w v| ≤
      t * (B * Real.exp (-m * t)) + B' / c * Real.exp (-c * t) := by
  have hEi : IntervalIntegrable E volume 0 t := hE.intervalIntegrable_of_Icc ht
  have hEi' : IntervalIntegrable (fun v => E (t - v)) volume 0 t := by
    have := hEi.comp_sub_left t
    simp only [sub_self, sub_zero] at this
    exact this.symm
  have hwI : IntegrableOn w (Set.Ioc 0 t) :=
    hw.mono_set (fun x hx => le_of_lt hx.1)
  have hwi : IntervalIntegrable w volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]; exact hwI
  have hwIoi : IntegrableOn w (Set.Ioi t) :=
    hw.mono_set (fun x hx => le_trans ht (le_of_lt hx))
  have e1 : ∫ r in Set.Ioc 0 t, E r = ∫ v in (0:ℝ)..t, E (t - v) := by
    rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero,
      intervalIntegral.integral_of_le ht]
  have e2 : ∫ v in Set.Ici (0:ℝ), w v = (∫ v in (0:ℝ)..t, w v) + ∫ v in Set.Ioi t, w v := by
    rw [integral_Ici_eq_integral_Ioi, intervalIntegral.integral_of_le ht,
      ← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hwI hwIoi,
      Set.Ioc_union_Ioi_eq_Ioi ht]
  have hsplit : (∫ r in Set.Ioc 0 t, E r) - ∫ v in Set.Ici (0:ℝ), w v =
      (∫ v in (0:ℝ)..t, (E (t - v) - w v)) - ∫ v in Set.Ioi t, w v := by
    rw [e1, e2, intervalIntegral.integral_sub hEi' hwi]; ring
  rw [hsplit]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (f := fun v => E (t - v) - w v) (C := B * Real.exp (-m * t)) (by
        intro v hv
        rw [Set.uIoc_of_le ht] at hv
        rw [Real.norm_eq_abs]
        exact hdiff v ⟨hv.1.le, hv.2⟩)
    rw [Real.norm_eq_abs] at this
    simpa [abs_of_nonneg ht, mul_comm] using this
  · have hint : IntegrableOn (fun v : ℝ => B' * Real.exp (-c * v)) (Set.Ioi t) :=
      (integrableOn_exp_mul_Ioi (by linarith : -c < 0) t).const_mul B'
    have := norm_integral_le_of_norm_le (μ := volume.restrict (Set.Ioi t)) (f := w)
      (g := fun v : ℝ => B' * Real.exp (-c * v)) hint (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        rw [Real.norm_eq_abs]
        exact hwb v (le_trans ht (le_of_lt hv)))
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -c < 0)] at this
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    field_simp

/-! ### D. Gram matrices of gradient fields are positive semidefinite -/

/-- The pointwise Gram identity: for continuous vector fields `h a` and a nonnegative continuous
weight, `∑_{ab} ∫ ⟨h_a,h_b⟩ ρ ≥ 0`. -/
theorem gram_pointwise {p : ℕ} (h : Fin p → Torus d → Euc d) (ρ : Torus d → ℝ)
    (hh : ∀ a, Continuous (h a)) (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x) :
    0 ≤ ∑ a, ∑ b, ∫ x, inner ℝ (h a x) (h b x) * ρ x := by
  have hint : ∀ a b, Integrable (fun x => inner ℝ (h a x) (h b x) * ρ x) := fun a b =>
    (((hh a).inner (hh b)).mul hρ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have e : ∑ a, ∑ b, ∫ x, inner ℝ (h a x) (h b x) * ρ x =
      ∫ x, ‖∑ a, h a x‖ ^ 2 * ρ x := by
    have e1 : ∑ a, ∑ b, ∫ x, inner ℝ (h a x) (h b x) * ρ x =
        ∑ a, ∫ x, ∑ b, inner ℝ (h a x) (h b x) * ρ x :=
      Finset.sum_congr rfl fun a _ => (integral_finsetSum _ (fun b _ => hint a b)).symm
    rw [e1, ← integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hint a b))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← real_inner_self_eq_norm_sq, sum_inner, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_sum, Finset.sum_mul]
  rw [e]
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hρ0 x)

theorem gram_posSemidef {p : ℕ} (t : Fin p → ℝ) (g : Fin p → ℝ → Torus d → Euc d)
    (μ : ℝ → Torus d → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hcont : ∀ a r, r ∈ Set.Ioc 0 (t a) → Continuous (g a r))
    (hμc : ∀ r, 0 < r → Continuous (μ r)) (hμ0 : ∀ r, 0 < r → ∀ x, 0 ≤ μ r x)
    (hint : ∀ a b, IntegrableOn (fun r => ∫ x, inner ℝ (g a r x) (g b r x) * μ r x)
        (Set.Ioc 0 (min (t a) (t b)))) :
    (Matrix.of fun a b => c * ∫ r in Set.Icc 0 (min (t a) (t b)),
        ∫ x, inner ℝ (g a r x) (g b r x) * μ r x).PosSemidef := by
  classical
  set E : Fin p → Fin p → ℝ → ℝ := fun a b r => ∫ x, inner ℝ (g a r x) (g b r x) * μ r x
    with hE
  have hEsymm : ∀ a b r, E a b r = E b a r := by
    intro a b r
    simp only [hE]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [real_inner_comm]
  set F : Fin p → Fin p → ℝ → ℝ := fun a b => (Set.Ioc 0 (min (t a) (t b))).indicator (E a b)
    with hF
  have hFint : ∀ a b, Integrable (F a b) := fun a b =>
    (hint a b).integrable_indicator measurableSet_Ioc
  have hFI : ∀ a b, ∫ r in Set.Icc 0 (min (t a) (t b)), E a b r = ∫ r, F a b r := by
    intro a b
    rw [integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Ioc]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun ξ => ?_⟩
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    rw [min_comm]
    congr 2
    funext r
    exact hEsymm b a r
  · have hLHS : dotProduct (star ξ) (Matrix.mulVec (Matrix.of fun a b => c *
        ∫ r in Set.Icc 0 (min (t a) (t b)), ∫ x, inner ℝ (g a r x) (g b r x) * μ r x) ξ) =
        ∫ r, c * ∑ a, ∑ b, ξ a * ξ b * F a b r := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial]
      rw [integral_const_mul]
      have h1 : ∀ a b, (c * ∫ r in Set.Icc 0 (min (t a) (t b)),
          ∫ x, inner ℝ (g a r x) (g b r x) * μ r x) * ξ b * ξ a =
          c * ∫ r, ξ a * ξ b * F a b r := by
        intro a b
        rw [integral_const_mul, ← hFI a b]
        simp only [hE]
        ring
      rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => (hFint a b).const_mul _))]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ (fun b _ => (hFint a b).const_mul _), Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← h1 a b]
      ring
    rw [hLHS]
    refine integral_nonneg fun r => mul_nonneg hc ?_
    by_cases hr : 0 < r
    · set w : Fin p → ℝ := fun a => if r ≤ t a then ξ a else 0 with hw
      set h : Fin p → Torus d → Euc d := fun a x => w a • g a r x with hh
      have hhc : ∀ a, Continuous (h a) := by
        intro a
        by_cases hra : r ≤ t a
        · have : h a = fun x => ξ a • g a r x := by
            funext x; simp [hh, hw, hra]
          rw [this]
          exact (continuous_const : Continuous fun _ : Torus d => ξ a).smul (hcont a r ⟨hr, hra⟩)
        · have : h a = fun _ => 0 := by
            funext x; simp [hh, hw, hra]
          rw [this]
          exact continuous_const
      have hFw : ∀ a b, ξ a * ξ b * F a b r = ∫ x, inner ℝ (h a x) (h b x) * μ r x := by
        intro a b
        have hinner : ∀ x, inner ℝ (h a x) (h b x) * μ r x =
            (w a * w b) * (inner ℝ (g a r x) (g b r x) * μ r x) := by
          intro x
          simp only [hh, inner_smul_left, inner_smul_right]
          simp
          ring
        simp_rw [hinner]
        rw [integral_const_mul]
        by_cases hra : r ≤ t a <;> by_cases hrb : r ≤ t b
        · have hm : r ≤ min (t a) (t b) := le_min hra hrb
          have : F a b r = E a b r := by
            simp only [hF]
            rw [Set.indicator_of_mem (show r ∈ Set.Ioc 0 (min (t a) (t b)) from ⟨hr, hm⟩)]
          rw [this]
          simp [hw, hra, hrb, hE]
        · have hm : ¬ r ≤ min (t a) (t b) := fun h' => hrb (le_trans h' (min_le_right _ _))
          have : F a b r = 0 := by
            simp only [hF]
            rw [Set.indicator_of_notMem (fun h' => hm h'.2)]
          simp [hw, hra, hrb, this]
        · have hm : ¬ r ≤ min (t a) (t b) := fun h' => hra (le_trans h' (min_le_left _ _))
          have : F a b r = 0 := by
            simp only [hF]
            rw [Set.indicator_of_notMem (fun h' => hm h'.2)]
          simp [hw, hra, hrb, this]
        · have hm : ¬ r ≤ min (t a) (t b) := fun h' => hra (le_trans h' (min_le_left _ _))
          have : F a b r = 0 := by
            simp only [hF]
            rw [Set.indicator_of_notMem (fun h' => hm h'.2)]
          simp [hw, hra, hrb, this]
      simp_rw [hFw]
      exact gram_pointwise h (μ r) hhc (hμc r hr) (hμ0 r hr)
    · have : ∀ a b, F a b r = 0 := by
        intro a b
        simp only [hF]
        rw [Set.indicator_of_notMem (fun h' => hr h'.1)]
      simp [this]

/-! ### E. Comparison of two energy pairings -/

theorem pair_diff_le {f g F G ρ ρ' : Torus d → ℝ}
    (hf : Torus.IsCk 1 f) (hg : Torus.IsCk 1 g) (hF : Torus.IsCk 1 F) (hG : Torus.IsCk 1 G)
    (hρ : Continuous ρ) (hρ' : Continuous ρ') (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (a1 a2 a3 a4 a5 e : ℝ)
    (h1 : ∀ x, ‖Torus.grad f x - Torus.grad F x‖ ≤ a1) (h2 : ∀ x, ‖Torus.grad g x‖ ≤ a2)
    (h3 : ∀ x, ‖Torus.grad F x‖ ≤ a3) (h4 : ∀ x, ‖Torus.grad g x - Torus.grad G x‖ ≤ a4)
    (h5 : ∀ x, ‖Torus.grad G x‖ ≤ a5) (he : ∀ x, |ρ x - ρ' x| ≤ e) :
    |(∫ x, inner ℝ (Torus.grad f x) (Torus.grad g x) * ρ x) -
        ∫ x, inner ℝ (Torus.grad F x) (Torus.grad G x) * ρ' x| ≤ a1 * a2 + a3 * a4 + a3 * a5 * e := by
  have x0 : Torus d := 0
  have ha1 : 0 ≤ a1 := (norm_nonneg _).trans (h1 x0)
  have ha2 : 0 ≤ a2 := (norm_nonneg _).trans (h2 x0)
  have ha3 : 0 ≤ a3 := (norm_nonneg _).trans (h3 x0)
  have ha4 : 0 ≤ a4 := (norm_nonneg _).trans (h4 x0)
  have ha5 : 0 ≤ a5 := (norm_nonneg _).trans (h5 x0)
  have he0 : 0 ≤ e := (abs_nonneg _).trans (he x0)
  have iX := integrable_energy hρ hf hg
  have iY := integrable_energy hρ' hF hG
  have hbound : Integrable (fun x => (a1 * a2 + a3 * a4) * ρ x + a3 * a5 * e) := by
    refine Integrable.add ?_ (integrable_const _)
    exact (hρ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _
  rw [← integral_sub iX iY, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hbound (Filter.Eventually.of_forall fun x => ?_)).trans ?_
  · have e1 : inner ℝ (Torus.grad f x) (Torus.grad g x) * ρ x -
        inner ℝ (Torus.grad F x) (Torus.grad G x) * ρ' x =
        (inner ℝ (Torus.grad f x - Torus.grad F x) (Torus.grad g x) +
          inner ℝ (Torus.grad F x) (Torus.grad g x - Torus.grad G x)) * ρ x +
        inner ℝ (Torus.grad F x) (Torus.grad G x) * (ρ x - ρ' x) := by
      rw [inner_sub_left, inner_sub_right]; ring
    rw [e1, Real.norm_eq_abs]
    have c1 : |inner ℝ (Torus.grad f x - Torus.grad F x) (Torus.grad g x)| ≤ a1 * a2 :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (h1 x) (h2 x) (norm_nonneg _) ha1)
    have c2 : |inner ℝ (Torus.grad F x) (Torus.grad g x - Torus.grad G x)| ≤ a3 * a4 :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (h3 x) (h4 x) (norm_nonneg _) ha3)
    have c3 : |inner ℝ (Torus.grad F x) (Torus.grad G x)| ≤ a3 * a5 :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (h3 x) (h5 x) (norm_nonneg _) ha3)
    have c4 : |inner ℝ (Torus.grad f x - Torus.grad F x) (Torus.grad g x) +
        inner ℝ (Torus.grad F x) (Torus.grad g x - Torus.grad G x)| ≤ a1 * a2 + a3 * a4 :=
      (abs_add_le _ _).trans (add_le_add c1 c2)
    calc _ ≤ |(inner ℝ (Torus.grad f x - Torus.grad F x) (Torus.grad g x) +
          inner ℝ (Torus.grad F x) (Torus.grad g x - Torus.grad G x)) * ρ x| +
        |inner ℝ (Torus.grad F x) (Torus.grad G x) * (ρ x - ρ' x)| := abs_add_le _ _
      _ ≤ (a1 * a2 + a3 * a4) * ρ x + a3 * a5 * e := by
          rw [abs_mul, abs_mul, abs_of_nonneg (hρ0 x)]
          exact add_le_add (mul_le_mul_of_nonneg_right c4 (hρ0 x))
            (mul_le_mul c3 (he x) (abs_nonneg _) (by positivity))
  · rw [integral_add ((hρ.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _) (integrable_const _), integral_const_mul,
      hρ1]
    simp

/-! ### F. Classical regularity of the propagator -/

/-- A classical adjoint solution realising `propagator` on `[0,t]`. -/
theorem exists_classical_prop (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ)
    (hj : mStar d ≤ j) (R : Regime) (MB Λ VB ν₀ : ℝ) (D : DynData d) (μ : ℝ → Torus d → ℝ)
    (hAD : ∀ T, 0 < T → AdjointData s j R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : 0 < t)
    {φ : Torus d → ℝ} (hφc : Continuous φ) (hφ : MemSobolev (j : ℝ) φ) :
    ∃ F : ℝ → Torus d → ℝ, IsClassicalAdjointSolution D μ t φ F ∧
      ∀ r ∈ Set.Icc 0 t, propagator D μ r t φ = F r := by
  obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical hd s hs0 hsd j hj R MB Λ VB
  obtain ⟨h1, h2, -⟩ := hmain D ν₀ t μ (hAD t ht) t ⟨ht, le_rfl⟩ φ hφc hφ
  exact ⟨_, h1, h2⟩

theorem continuous_partialDeriv_prod {D : DynData d} {μ : ℝ → Torus d → ℝ} {t : ℝ}
    {φ : Torus d → ℝ} {F : ℝ → Torus d → ℝ} (hF : IsClassicalAdjointSolution D μ t φ F)
    (i : Fin d) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => Torus.partialDeriv i (F p.1) p.2 := by
  refine ClassicalAux.continuous_prod_of_lift (X := Set.Icc (0 : ℝ) t)
    (fun r x => Torus.partialDeriv i (F r) x) ?_
  have h1 := ClassicalAux.continuous_iteratedFDeriv_eval
    (G := fun r : Set.Icc (0 : ℝ) t => Torus.lift (F r)) 1 (hF.cont_c2 1 (by norm_num))
    ![EuclideanSpace.single i 1]
  refine h1.congr fun p => ?_
  rw [iteratedFDeriv_one_apply, partialDeriv_mk i (F p.1.1) (by
    exact (hF.c2 p.1.1 p.1.2).of_le (by norm_num))]
  simp

/-- Joint continuity of the energy integrand of two classical solutions. -/
theorem continuous_energy_integrand {D : DynData d} {μ : ℝ → Torus d → ℝ} {t t' : ℝ}
    {φ φ' : Torus d → ℝ} {F F' : ℝ → Torus d → ℝ}
    (hF : IsClassicalAdjointSolution D μ t φ F) (hF' : IsClassicalAdjointSolution D μ t' φ' F')
    {m : ℝ} (hmt : m ≤ t) (hmt' : m ≤ t')
    (hμ : ContinuousOn (fun p : ℝ × Torus d => μ p.1 p.2) (Set.Icc 0 m ×ˢ Set.univ)) :
    ContinuousOn (fun r => ∫ x, inner ℝ (Torus.grad (F r) x) (Torus.grad (F' r) x) * μ r x)
      (Set.Icc 0 m) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let ι : Set.Icc (0 : ℝ) m → Set.Icc (0 : ℝ) t := fun r => ⟨r.1, r.2.1, r.2.2.trans hmt⟩
  let ι' : Set.Icc (0 : ℝ) m → Set.Icc (0 : ℝ) t' := fun r => ⟨r.1, r.2.1, r.2.2.trans hmt'⟩
  have hι : Continuous ι := Continuous.subtype_mk continuous_subtype_val _
  have hι' : Continuous ι' := Continuous.subtype_mk continuous_subtype_val _
  have key := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Torus d)))
    (f := fun (r : Set.Icc (0 : ℝ) m) (x : Torus d) =>
      inner ℝ (Torus.grad (F r.1) x) (Torus.grad (F' r.1) x) * μ r.1 x) (by
      have hμ' : Continuous fun p : Set.Icc (0 : ℝ) m × Torus d => μ p.1.1 p.2 := by
        have := hμ.comp_continuous (f := fun p : Set.Icc (0 : ℝ) m × Torus d => (p.1.1, p.2))
          ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
          (fun p => ⟨p.1.2, Set.mem_univ _⟩)
        exact this
      have hg : Continuous fun p : Set.Icc (0 : ℝ) m × Torus d =>
          inner ℝ (Torus.grad (F p.1.1) p.2) (Torus.grad (F' p.1.1) p.2) := by
        simp_rw [MFApriori.inner_grad_grad]
        refine continuous_finsetSum _ fun i _ => ?_
        exact ((continuous_partialDeriv_prod hF i).comp (hι.comp continuous_fst |>.prodMk continuous_snd)).mul
          ((continuous_partialDeriv_prod hF' i).comp (hι'.comp continuous_fst |>.prodMk continuous_snd))
      exact hg.mul hμ') isCompact_univ
  simp only [MeasureTheory.Measure.restrict_univ] at key
  exact key

/-! ### G. The abstract entry comparison -/

theorem abs_energy_le_sup {f g ρ : Torus d → ℝ} (hf : Torus.IsCk 1 f) (hg : Torus.IsCk 1 g)
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1) (a b : ℝ)
    (ha : ∀ x, ‖Torus.grad f x‖ ≤ a) (hb : ∀ x, ‖Torus.grad g x‖ ≤ b) :
    |∫ x, inner ℝ (Torus.grad f x) (Torus.grad g x) * ρ x| ≤ a * b := by
  have x0 : Torus d := 0
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha x0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb x0)
  have hint : Integrable (fun x => a * b * ρ x) :=
    (hρ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun x => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 x)]
    exact mul_le_mul_of_nonneg_right ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul (ha x) (hb x) (norm_nonneg _) ha0)) (hρ0 x)
  · rw [integral_const_mul, hρ1]; simp

theorem entry_abstract (UA UB : ℝ → ℝ → Torus d → ℝ) (SA SB : ℝ → Torus d → ℝ)
    (μ : ℝ → Torus d → ℝ) (ρβ : Torus d → ℝ) (m Cρ CA CB : ℝ) (hm : 0 < m) (hCρ : 0 ≤ Cρ)
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hρβc : Continuous ρβ) (hρβ0 : ∀ x, 0 ≤ ρβ x) (hρβ1 : ∫ x, ρβ x = 1)
    (hμc : ∀ r, 0 ≤ r → Continuous (μ r)) (hμ0 : ∀ r, 0 ≤ r → ∀ x, 0 ≤ μ r x)
    (hμ1 : ∀ r, 0 ≤ r → ∫ x, μ r x = 1)
    (hμρ : ∀ r, 0 ≤ r → ∀ x, |μ r x - ρβ x| ≤ Cρ * Real.exp (-m * r))
    (hUA1 : ∀ t, 0 < t → ∀ r ∈ Set.Icc 0 t, Torus.IsCk 1 (UA r t))
    (hUB1 : ∀ t, 0 < t → ∀ r ∈ Set.Icc 0 t, Torus.IsCk 1 (UB r t))
    (hSA1 : ∀ v, 0 ≤ v → Torus.IsCk 1 (SA v)) (hSB1 : ∀ v, 0 ≤ v → Torus.IsCk 1 (SB v))
    (hUAS : ∀ t, 0 < t → ∀ r ∈ Set.Icc 0 t, ∀ x,
      ‖Torus.grad (UA r t) x - Torus.grad (SA (t - r)) x‖ ≤ CA * Real.exp (-m * t))
    (hSA : ∀ v, 0 ≤ v → ∀ x, ‖Torus.grad (SA v) x‖ ≤ CA * Real.exp (-m * v))
    (hUB : ∀ t, 0 < t → ∀ r ∈ Set.Icc 0 t, ∀ x,
      ‖Torus.grad (UB r t) x‖ ≤ CB * Real.exp (-m * (t - r)))
    (hUBS : ∀ t, 0 < t → ∀ r ∈ Set.Icc 0 t, ∀ x,
      ‖Torus.grad (UB r t) x - Torus.grad (SB (t - r)) x‖ ≤ CB * Real.exp (-m * t))
    (hSB : ∀ v, 0 ≤ v → ∀ x, ‖Torus.grad (SB v) x‖ ≤ CB * Real.exp (-m * v))
    (δ : ℝ) (hδ : 0 ≤ δ) (t : ℝ) (ht : 0 < t)
    (hEc : ContinuousOn (fun r => ∫ x, inner ℝ (Torus.grad (UA r t) x)
      (Torus.grad (UB r (t + δ)) x) * μ r x) (Set.Icc 0 t))
    (hw : IntegrableOn (fun v => ∫ x, inner ℝ (Torus.grad (SA v) x)
      (Torus.grad (SB (v + δ)) x) * ρβ x) (Set.Ici 0)) :
    |(∫ r in Set.Ioc 0 t, ∫ x, inner ℝ (Torus.grad (UA r t) x)
        (Torus.grad (UB r (t + δ)) x) * μ r x) -
      ∫ v in Set.Ici 0, ∫ x, inner ℝ (Torus.grad (SA v) x) (Torus.grad (SB (v + δ)) x) * ρβ x| ≤
      t * (CA * CB * (2 + Cρ) * Real.exp (-m * t)) + CA * CB / m * Real.exp (-m * t) := by
  refine entry_real t ht.le _ _ (CA * CB * (2 + Cρ)) (CA * CB) m m hm hEc hw ?_ ?_
  · intro v hv
    have hr : t - v ∈ Set.Icc (0 : ℝ) t := ⟨by linarith [hv.2], by linarith [hv.1]⟩
    have hr0 : 0 ≤ t - v := hr.1
    have hrt : t - v ∈ Set.Icc (0 : ℝ) (t + δ) := ⟨hr.1, by linarith [hr.2]⟩
    have ht' : 0 < t + δ := by linarith
    have e1 : t - (t - v) = v := by ring
    have e2 : t + δ - (t - v) = v + δ := by ring
    have hv0 : 0 ≤ v := hv.1
    have hexp1 : Real.exp (-m * v) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hexp2 : Real.exp (-m * (v + δ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hexp3 : Real.exp (-m * (t + δ)) ≤ Real.exp (-m * t) :=
      Real.exp_le_exp.2 (by nlinarith)
    have hprod : Real.exp (-m * v) * Real.exp (-m * (t - v)) = Real.exp (-m * t) := by
      rw [← Real.exp_add]; congr 1; ring
    have := pair_diff_le (f := UA (t - v) t) (g := UB (t - v) (t + δ)) (F := SA v)
      (G := SB (v + δ)) (ρ := μ (t - v)) (ρ' := ρβ) (hUA1 t ht _ hr) (hUB1 (t + δ) ht' _ hrt)
      (hSA1 v hv0) (hSB1 (v + δ) (by linarith)) (hμc _ hr0) hρβc (hμ0 _ hr0) (hμ1 _ hr0)
      (CA * Real.exp (-m * t)) CB (CA * Real.exp (-m * v)) (CB * Real.exp (-m * t)) CB
      (Cρ * Real.exp (-m * (t - v)))
      (fun x => by have := hUAS t ht _ hr x; rwa [e1] at this)
      (fun x => by
        have := hUB (t + δ) ht' _ hrt x
        rw [e2] at this
        refine this.trans ?_
        have : Real.exp (-m * (v + δ)) ≤ 1 := hexp2
        nlinarith)
      (fun x => hSA v hv0 x)
      (fun x => by
        have := hUBS (t + δ) ht' _ hrt x
        rw [e2] at this
        refine this.trans ?_
        exact mul_le_mul_of_nonneg_left hexp3 hCB)
      (fun x => by
        refine (hSB (v + δ) (by linarith) x).trans ?_
        nlinarith)
      (fun x => hμρ _ hr0 x)
    refine this.trans ?_
    have hexpt : 0 ≤ Real.exp (-m * t) := (Real.exp_pos _).le
    have hexpv : 0 ≤ Real.exp (-m * v) := (Real.exp_pos _).le
    have t1 : CA * Real.exp (-m * t) * CB ≤ CA * CB * Real.exp (-m * t) := by nlinarith
    have t2 : CA * Real.exp (-m * v) * (CB * Real.exp (-m * t)) ≤ CA * CB * Real.exp (-m * t) := by
      have : Real.exp (-m * v) * Real.exp (-m * t) ≤ Real.exp (-m * t) := by nlinarith
      nlinarith [mul_nonneg hCA hCB]
    have t3 : CA * Real.exp (-m * v) * CB * (Cρ * Real.exp (-m * (t - v))) =
        CA * CB * Cρ * Real.exp (-m * t) := by
      rw [← hprod]; ring
    nlinarith
  · intro v hv
    have hv' : (0 : ℝ) ≤ v := hv
    have := abs_energy_le_sup (f := SA v) (g := SB (v + δ)) (ρ := ρβ) (hSA1 v hv')
      (hSB1 (v + δ) (by linarith)) hρβc hρβ0 hρβ1 (CA * Real.exp (-m * v))
      (CB * Real.exp (-m * (v + δ))) (hSA v hv') (hSB (v + δ) (by linarith))
    refine this.trans ?_
    have e3 : Real.exp (-m * (v + δ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h0 : 0 ≤ Real.exp (-m * v) := (Real.exp_pos _).le
    have : CA * Real.exp (-m * v) * (CB * Real.exp (-m * (v + δ))) ≤ CA * CB * Real.exp (-m * v) := by
      have : Real.exp (-m * v) * Real.exp (-m * (v + δ)) ≤ Real.exp (-m * v) := by nlinarith
      nlinarith [mul_nonneg hCA hCB]
    exact this

/-! ### H. The concrete decay facts -/

/-- The bundle of analytic facts about the solution `ρ^t`, the propagator `U^{r,t}` and the
frozen semigroup `S_β(v)` used in the entry comparison: one rate `m`, one constant `Cρ`, and for
each smooth test function one constant for the gradient bounds. -/
structure LossFacts (D : DynData d) (ρc : ℝ → Coeff d) (ρβ : Torus d → ℝ) (m Cρ : ℝ) : Prop where
  m_pos : 0 < m
  Cρ_nonneg : 0 ≤ Cρ
  rho_dec : ∀ r, 0 ≤ r → ∀ x, |mfPath ρc r x - ρβ x| ≤ Cρ * Real.exp (-m * r)
  mu_nonneg : ∀ r, 0 ≤ r → ∀ x, 0 ≤ mfPath ρc r x
  mu_cont : ∀ r, 0 ≤ r → Continuous (mfPath ρc r)
  mu_one : ∀ r, 0 ≤ r → ∫ x, mfPath ρc r x = 1
  mu_joint : ∀ T, ContinuousOn (fun p : ℝ × Torus d => mfPath ρc p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ)
  rhoβ_cont : Continuous ρβ
  rhoβ_nonneg : ∀ x, 0 ≤ ρβ x
  rhoβ_one : ∫ x, ρβ x = 1
  classical : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ t, 0 < t →
    ∃ F : ℝ → Torus d → ℝ, IsClassicalAdjointSolution D (mfPath ρc) t φ F ∧
      ∀ r ∈ Set.Icc 0 t, propagator D (mfPath ρc) r t φ = F r
  grad : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∃ C : ℝ, 0 ≤ C ∧
    (∀ v, 0 ≤ v → Torus.IsCk 2 (equilibriumSemigroup D ρβ v φ)) ∧
    (∀ v, 0 ≤ v → ∀ x, ‖Torus.grad (equilibriumSemigroup D ρβ v φ) x‖ ≤ C * Real.exp (-m * v)) ∧
    (∀ t, 0 < t → ∀ r ∈ Set.Icc 0 t, ∀ x,
      ‖Torus.grad (propagator D (mfPath ρc) r t φ) x -
        Torus.grad (equilibriumSemigroup D ρβ (t - r) φ) x‖ ≤ C * Real.exp (-m * t)) ∧
    (∀ t, 0 < t → ∀ r ∈ Set.Icc 0 t, ∀ x,
      ‖Torus.grad (propagator D (mfPath ρc) r t φ) x‖ ≤ C * Real.exp (-m * (t - r)))

theorem continuous_of_isSmooth {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : Continuous φ :=
  MFAux.continuous_of_isCk (ContDiff.of_le
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from hφ)
    (by exact_mod_cast le_top))


theorem loss_facts (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (j : ℕ) (hjeven : Even j) (hj : (d : ℝ) / 2 + 4 < j)
    (hK : 2 * j + 4 * d + 20 ≤ K) (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρc : ℝ → Coeff d)
    (hρc : IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Continuous ρβ)
    (hpos : ∀ x, 0 < ρβ x) :
    ∃ (m Cρ c₀ Λ₀ : ℝ),
      LossFacts (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) ρc ρβ m Cρ ∧
      MFAdjoint.FrozenHyp d s (2 * mStar d + 4) βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρβ := by
  classical
  obtain ⟨R, Λ, Λ₀, c₀, Cd, κ, hc₀, hκ, hall⟩ :=
    MFAdjoint.finiteReg_hypotheses hd s βm βp K V ρ₀ H j hj hK
  obtain ⟨hFz, hAD, hdec⟩ := hall β hβ ρc hρc ρβ hρβ hρC hpos
  obtain ⟨C5, c5, κ5, hC5, hc5, hκ5, h52⟩ :=
    MFAdjoint.adjoint_decay_comparison_wiring hd s βm βp K V ρ₀ H j hjeven hj hK
  obtain ⟨Cf, cf, hCf, hcf, hfd⟩ := MFAdjoint.exists_frozen_hj_decay' hd s j hj βp⁻¹ βm⁻¹ c₀ Λ₀
  obtain ⟨Cs, hCs0, hCs⟩ := exists_grad_sup_le (d := d) j (by linarith)
  have hmj : mStar d + 2 ≤ j := MFAdjoint.mStar_add_two_le_of_gt hj
  have hFz2 : MFAdjoint.FrozenHyp d s (2 * mStar d + 4) βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρβ :=
    hFz.mono (by omega)
  have hFzj : MFAdjoint.FrozenHyp d s (j + mStar d) βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρβ :=
    hFz.mono (by omega)
  have hβ0 : 0 < β := lt_of_lt_of_le H.hβm hβ.1
  -- the solution `ρ^t`
  have hKd : (d : ℝ) / 2 < K := by linarith [H.hK]
  have hK2 : (d : ℝ) / 2 + 2 < K := by linarith [H.hK]
  have hreal := MFGlobal.isRealCoeff_of_isMFSolutionHK hd s βm βp K V ρ₀ H β hβ ρc hρc
  have hsumK : ∀ t, 0 ≤ t → Summable fun k => ‖ρc t k‖ := fun t ht =>
    summable_norm_of_memHs (K : ℝ) hKd _ (hρc.cont.1 t ht)
  have hSol : ∀ T, MFApriori.MFSolRealOn d s V β⁻¹ (K : ℝ) ρ₀ ρc T := fun T =>
    ⟨MFApriori.IsMFSolutionHK.toSolOn hρc T, fun τ hτ => hreal τ hτ.1⟩
  have hμcont : ∀ r, 0 ≤ r → Continuous (mfPath ρc r) := fun r hr =>
    MFApriori.MFSolRealOn.continuous_mfPath hKd (hSol r) ⟨hr, le_rfl⟩
  have hprob := fun r (hr : 0 ≤ r) =>
    MFWeak.isProbDensity_mfPath hd s βm βp K V ρ₀ H β hβ ρc hρc r hr
  obtain ⟨cU, CU, hcU, hU⟩ := MFGlobal.finite_reg_uniform_bounds hd s βm βp K V ρ₀ H
  -- sup bound of the density difference
  have hdrA : (d : ℝ) / 2 < (j : ℝ) + (d : ℝ) / 2 + 2 := by
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  obtain ⟨A, hA0, hA⟩ := MFAdjoint.wire_sup_le (d := d) _ hdrA
  have hρdec : ∀ r, 0 ≤ r → ∀ x, |mfPath ρc r x - ρβ x| ≤ A * Cd * Real.exp (-κ * r) := by
    intro r hr x
    obtain ⟨hmem, hnorm⟩ := hdec r hr
    set f : Torus d → ℝ := fun y => mfPath ρc r y - ρβ y with hf
    have hfc : Continuous f := (hμcont r hr).sub hρC
    have hco : coeffOf f = coeffOf (mfPath ρc r) - coeffOf ρβ :=
      ET.coeffOf_sub_fun (hμcont r hr) hρC
    rw [← hco] at hmem hnorm
    have hsum := summable_norm_of_memHs _ hdrA _ hmem
    have hff : toFun (coeffOf f) = f := toFun_coeffOf f hfc hsum
    calc |mfPath ρc r x - ρβ x| = |toFun (coeffOf f) x| := by rw [hff]
      _ ≤ A * hsNorm _ (coeffOf f) := hA _ hmem x
      _ ≤ A * (Cd * Real.exp (-κ * r)) := mul_le_mul_of_nonneg_left hnorm hA0
      _ = A * Cd * Real.exp (-κ * r) := by ring
  have hCd0 : 0 ≤ Cd := by
    have := (hdec 0 le_rfl).2
    have h0 : 0 ≤ hsNorm ((j : ℝ) + (d : ℝ) / 2 + 2) (coeffOf (mfPath ρc 0) - coeffOf ρβ) :=
      Real.sqrt_nonneg _
    simp at this
    linarith
  set m : ℝ := min (min c5 κ5) (min cf κ) with hm
  have hm0 : 0 < m := lt_min (lt_min hc5 hκ5) (lt_min hcf hκ)
  have hm_c5 : m ≤ c5 := (min_le_left _ _).trans (min_le_left _ _)
  have hm_κ5 : m ≤ κ5 := (min_le_left _ _).trans (min_le_right _ _)
  have hm_cf : m ≤ cf := (min_le_right _ _).trans (min_le_left _ _)
  have hm_κ : m ≤ κ := (min_le_right _ _).trans (min_le_right _ _)
  have hclass : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ t, 0 < t →
      ∃ F : ℝ → Torus d → ℝ, IsClassicalAdjointSolution
        (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) (mfPath ρc) t φ F ∧
        ∀ r ∈ Set.Icc 0 t, propagator (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1))
          (mfPath ρc) r t φ = F r := by
    intro φ hφ t ht
    exact exists_classical_prop hd s H.hs0 H.hsd j (by omega) R 1 Λ (Torus.cbNorm (j + 3) V)
      βp⁻¹ _ (mfPath ρc) hAD ht (continuous_of_isSmooth hφ)
      (MFSemigroup.memSobolev_of_isSmooth hφ _)
  refine ⟨m, A * Cd, c₀, Λ₀, ⟨hm0, mul_nonneg hA0 hCd0, ?_, ?_, hμcont, ?_, ?_, hρC, ?_, ?_, ?_, ?_⟩, hFz2⟩
  · intro r hr x
    refine (hρdec r hr x).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (mul_nonneg hA0 hCd0)
  · exact fun r hr => (hprob r hr).nonneg
  · exact fun r hr => (hprob r hr).integral_one
  · intro T
    exact (MFApriori.continuousOn_mfPath_prod_on hd s H.hs0 H.hsd K hK2 V ρ₀ H.hV β⁻¹ ρc
      (hSol T)).1
  · exact hρβ.1.nonneg
  · exact hρβ.1.integral_one
  · exact hclass
  · intro φ hφ
    have hφc : Continuous φ := continuous_of_isSmooth hφ
    have hφj : MemSobolev (j : ℝ) φ := MFSemigroup.memSobolev_of_isSmooth hφ _
    have hφ4 : MemSobolev ((mStar d : ℝ) + 4) φ := MFSemigroup.memSobolev_of_isSmooth hφ _
    set N : ℝ := sobolevNorm (j : ℝ) (projMean (withDensityReal ρβ) φ) with hN
    have hN0 : 0 ≤ N := Real.sqrt_nonneg _
    have hCnn : 0 ≤ Cs * (C5 + Cf) * N := by positivity
    have hS2 : ∀ v, 0 ≤ v → Torus.IsCk 2 (equilibriumSemigroup
        (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) ρβ v φ) := fun v hv =>
      (frozen_path_data hd hFz2 hφc hφ4 (T' := v + 1) (by linarith)).1 v ⟨hv, by linarith⟩
    have hU2 : ∀ t, 0 < t → ∀ r ∈ Set.Icc (0 : ℝ) t, Torus.IsCk 2 (propagator
        (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) (mfPath ρc) r t φ) := by
      intro t ht r hr
      obtain ⟨F, hF, hFp⟩ := hclass φ hφ t ht
      rw [hFp r hr]; exact hF.c2 r hr
    have hexpS : ∀ v, 0 ≤ v → Real.exp (-cf * v) ≤ Real.exp (-m * v) := fun v hv =>
      Real.exp_le_exp.2 (by nlinarith)
    refine ⟨Cs * (C5 + Cf) * N, hCnn, hS2, ?_, ?_, ?_⟩
    · intro v hv x
      have hS := hfd β V ρβ hFzj φ hφc hφj v hv
      have h1 := hCs _ hS.1 ((hS2 v hv).of_le (by norm_num)) x
      refine h1.trans ?_
      calc Cs * sobolevNorm (j : ℝ) (equilibriumSemigroup
            (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) ρβ v φ)
          ≤ Cs * (Cf * Real.exp (-cf * v) * N) := mul_le_mul_of_nonneg_left hS.2 hCs0
        _ ≤ Cs * ((C5 + Cf) * Real.exp (-m * v) * N) := by
            gcongr <;> linarith
        _ = Cs * (C5 + Cf) * N * Real.exp (-m * v) := by ring
    · intro t ht r hr x
      have hrt : 0 ≤ r ∧ r ≤ t := hr
      obtain ⟨hm1, hn1, hn2⟩ := h52 β hβ ρc hρc ρβ hρβ hρC hpos φ hφc hφj r t hrt.1 hrt.2
      set f := propagator (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) (mfPath ρc) r t φ
        with hf
      have hf2 : Torus.IsCk 2 f := hU2 t ht r hr
      have hQ1 : Torus.IsCk 1 (projMean (withDensityReal ρβ) f) :=
        isCk_sub_const (hf2.of_le (by norm_num)) _
      have hSv := hfd β V ρβ hFzj φ hφc hφj (t - r) (by linarith)
      have hS1 : Torus.IsCk 1 (equilibriumSemigroup
          (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) ρβ (t - r) φ) :=
        (hS2 (t - r) (by linarith)).of_le (by norm_num)
      have hQc : Continuous (projMean (withDensityReal ρβ) f) :=
        MFAux.continuous_of_isCk (hQ1.of_le (by norm_num))
      have hSc : Continuous (equilibriumSemigroup
          (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) ρβ (t - r) φ) :=
        MFAux.continuous_of_isCk (hS1.of_le (by norm_num))
      have hS' : equilibriumSemigroup (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) ρβ (t - r)
          (projMean (withDensityReal ρβ) φ) = equilibriumSemigroup
          (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) ρβ (t - r) φ :=
        MFAdjoint.equilibriumSemigroup_projMean hd s βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρβ hFz2 φ hφc hφ4 (t - r)
          (by linarith)
      rw [hS'] at hn2
      have hmem := memSobolev_sub hQc hSc hm1 hSv.1
      have hg : ∀ x, Torus.grad f x - Torus.grad (equilibriumSemigroup
          (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) ρβ (t - r) φ) x =
          Torus.grad (fun y => projMean (withDensityReal ρβ) f y - equilibriumSemigroup
            (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) ρβ (t - r) φ y) x := by
        intro y
        rw [grad_sub hQ1 hS1]
        have : Torus.grad (projMean (withDensityReal ρβ) f) y = Torus.grad f y :=
          grad_sub_const f _ y
        rw [this]
      rw [hg x]
      have h1 := hCs _ hmem (isCk_sub hQ1 hS1) x
      refine h1.trans ?_
      have hN2 : sobolevNorm (j : ℝ) (fun y => projMean (withDensityReal ρβ) f y -
          equilibriumSemigroup (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) ρβ (t - r) φ y)
          ≤ C5 * Real.exp (-c5 * (t - r)) * Real.exp (-κ5 * r) * N := hn2
      refine (mul_le_mul_of_nonneg_left hN2 hCs0).trans ?_
      have e1 : Real.exp (-c5 * (t - r)) ≤ Real.exp (-m * (t - r)) :=
        Real.exp_le_exp.2 (by nlinarith [hrt.2])
      have e2 : Real.exp (-κ5 * r) ≤ Real.exp (-m * r) := Real.exp_le_exp.2 (by nlinarith [hrt.1])
      have e3 : Real.exp (-m * (t - r)) * Real.exp (-m * r) = Real.exp (-m * t) := by
        rw [← Real.exp_add]; congr 1; ring
      calc Cs * (C5 * Real.exp (-c5 * (t - r)) * Real.exp (-κ5 * r) * N)
          ≤ Cs * (C5 * Real.exp (-m * (t - r)) * Real.exp (-m * r) * N) := by
            gcongr
        _ = Cs * C5 * N * Real.exp (-m * t) := by rw [← e3]; ring
        _ ≤ Cs * (C5 + Cf) * N * Real.exp (-m * t) := by
            gcongr <;> linarith
    · intro t ht r hr x
      have hrt : 0 ≤ r ∧ r ≤ t := hr
      obtain ⟨hm1, hn1, hn2⟩ := h52 β hβ ρc hρc ρβ hρβ hρC hpos φ hφc hφj r t hrt.1 hrt.2
      set f := propagator (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) (mfPath ρc) r t φ
        with hf
      have hf2 : Torus.IsCk 2 f := hU2 t ht r hr
      have hQ1 : Torus.IsCk 1 (projMean (withDensityReal ρβ) f) :=
        isCk_sub_const (hf2.of_le (by norm_num)) _
      have h1 := hCs _ hm1 hQ1 x
      have hg : Torus.grad (projMean (withDensityReal ρβ) f) x = Torus.grad f x :=
        grad_sub_const f _ x
      rw [hg] at h1
      refine h1.trans ?_
      refine (mul_le_mul_of_nonneg_left hn1 hCs0).trans ?_
      have e1 : Real.exp (-c5 * (t - r)) ≤ Real.exp (-m * (t - r)) :=
        Real.exp_le_exp.2 (by nlinarith [hrt.2])
      calc Cs * (C5 * Real.exp (-c5 * (t - r)) * N)
          ≤ Cs * (C5 * Real.exp (-m * (t - r)) * N) := by gcongr
        _ = Cs * C5 * N * Real.exp (-m * (t - r)) := by ring
        _ ≤ Cs * (C5 + Cf) * N * Real.exp (-m * (t - r)) := by
            gcongr <;> linarith



theorem continuous_grad {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) : Continuous (Torus.grad f) := by
  have : Torus.grad f = fun x => WithLp.toLp 2 (fun i => Torus.partialDeriv i f x) := by
    funext x; ext i; simp [MFAux.grad_apply]
  rw [this]
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_partialDeriv i f hf)

theorem continuousOn_energy_prop {D : DynData d} {ρc : ℝ → Coeff d} {ρβ : Torus d → ℝ} {m Cρ : ℝ}
    (hF : LossFacts D ρc ρβ m Cρ) {A B : Torus d → ℝ} (hA : Torus.IsSmooth A)
    (hB : Torus.IsSmooth B) {t t' mm : ℝ} (hmm : 0 < mm) (hmt : mm ≤ t) (hmt' : mm ≤ t') :
    ContinuousOn (fun r => ∫ x, inner ℝ (Torus.grad (propagator D (mfPath ρc) r t A) x)
      (Torus.grad (propagator D (mfPath ρc) r t' B) x) * mfPath ρc r x) (Set.Icc 0 mm) := by
  obtain ⟨Fa, hFa, hFpa⟩ := hF.classical A hA t (by linarith)
  obtain ⟨Fb, hFb, hFpb⟩ := hF.classical B hB t' (by linarith)
  refine (continuous_energy_integrand hFa hFb hmt hmt' (hF.mu_joint mm)).congr fun r hr => ?_
  simp only
  rw [hFpa r ⟨hr.1, hr.2.trans hmt⟩, hFpb r ⟨hr.1, hr.2.trans hmt'⟩]

theorem mul_exp_neg_le {m t : ℝ} (hm : 0 < m) (ht : 0 ≤ t) :
    t * Real.exp (-m * t) ≤ (2 / m) * Real.exp (-(m / 2) * t) := by
  have h1 : m * t / 2 ≤ Real.exp (m * t / 2) := by
    have := Real.add_one_le_exp (m * t / 2); linarith
  have h2 : Real.exp (-m * t) = Real.exp (-(m / 2) * t) * Real.exp (-(m / 2) * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (m * t / 2) * Real.exp (-(m / 2) * t) = 1 := by
    rw [← Real.exp_add]; convert Real.exp_zero using 2; ring
  have h4 : t ≤ (2 / m) * Real.exp (m * t / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]; nlinarith
  have hpos : 0 ≤ Real.exp (-(m / 2) * t) := (Real.exp_pos _).le
  calc t * Real.exp (-m * t) = (t * Real.exp (-(m / 2) * t)) * Real.exp (-(m / 2) * t) := by
        rw [h2]; ring
    _ ≤ ((2 / m) * Real.exp (m * t / 2) * Real.exp (-(m / 2) * t)) * Real.exp (-(m / 2) * t) := by
        gcongr
    _ = (2 / m) * Real.exp (-(m / 2) * t) * (Real.exp (m * t / 2) * Real.exp (-(m / 2) * t)) := by
        ring
    _ = (2 / m) * Real.exp (-(m / 2) * t) := by rw [h3]; ring

theorem S_memSobolev_mStar (hd : 1 ≤ d) {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ}
    (Hz : MFAdjoint.FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ) {ψ : Torus d → ℝ}
    (hψc : Continuous ψ) (hψ : MemSobolev ((mStar d : ℝ) + 4) ψ) {τ : ℝ} (hτ : 0 ≤ τ) :
    MemSobolev ((mStar d : ℝ) + 4)
      (equilibriumSemigroup (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρβ τ ψ) := by
  obtain ⟨C, c, hC, hc, h⟩ :=
    MFAdjoint.exists_frozen_hj_decay hd s (mStar d + 4) le_rfl νm νp c₀ Λ₀
  have := (h β V ρβ (Hz.mono (by omega)) ψ hψc (by exact_mod_cast hψ) τ hτ).1
  exact_mod_cast this

theorem cov_symm (hd : 1 ≤ d) {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ}
    (Hz : MFAdjoint.FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ) {φ ψ : Torus d → ℝ}
    (hφ : Continuous φ) (hφm : MemSobolev ((mStar d : ℝ) + 4) φ) (hψ : Continuous ψ)
    (hψm : MemSobolev ((mStar d : ℝ) + 4) ψ) :
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ ψ =
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β ψ φ := by
  rw [(susceptibilityCov_eq_integral hd s νm νp c₀ Λ₀ β V ρβ Hz φ ψ hφ hφm hψ hψm).2,
    (susceptibilityCov_eq_integral hd s νm νp c₀ Λ₀ β V ρβ Hz ψ φ hψ hψm hφ hφm).2]
  congr 2
  funext v
  congr 1
  funext x
  rw [real_inner_comm]


/-- The integrand `E_{AB}(r) = ∫ ⟨∇U^{r,t}A, ∇U^{r,t'}B⟩ ρ^r dx` of the noise covariance. -/
def Eint (D : DynData d) (ρc : ℝ → Coeff d) (A B : Torus d → ℝ) (t t' r : ℝ) : ℝ :=
  ∫ x, inner ℝ (Torus.grad (propagator D (mfPath ρc) r t A) x)
    (Torus.grad (propagator D (mfPath ρc) r t' B) x) * mfPath ρc r x

theorem Eint_comm (D : DynData d) (ρc : ℝ → Coeff d) (A B : Torus d → ℝ) (t t' r : ℝ) :
    Eint D ρc A B t t' r = Eint D ρc B A t' t r := by
  unfold Eint
  congr 1
  funext x
  rw [real_inner_comm]

/-- The covariance matrix `M_u` of the Gaussian part. -/
def Mcov (D : DynData d) (ρc : ℝ → Coeff d) {p : ℕ} (τ : Fin p → ℝ) (φ : Fin p → Torus d → ℝ)
    (u : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun a b => 2 * D.invβ *
    ∫ r in Set.Icc 0 (min (u + τ a) (u + τ b)), Eint D ρc (φ a) (φ b) (u + τ a) (u + τ b) r

theorem entry_ordered (hd : 1 ≤ d) {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ}
    (Hz : MFAdjoint.FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ)
    {ρc : ℝ → Coeff d} {m Cρ : ℝ}
    (hF : LossFacts (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρc ρβ m Cρ)
    {A B : Torus d → ℝ} (hA : Torus.IsSmooth A) (hB : Torus.IsSmooth B) {CA CB : ℝ}
    (hCA : 0 ≤ CA)
    (hA2 : ∀ v, 0 ≤ v → Torus.IsCk 2 (equilibriumSemigroup (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρβ v A))
    (hAS : ∀ v, 0 ≤ v → ∀ x, ‖Torus.grad (equilibriumSemigroup
      (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρβ v A) x‖ ≤ CA * Real.exp (-m * v))
    (hAUS : ∀ t, 0 < t → ∀ r ∈ Set.Icc 0 t, ∀ x,
      ‖Torus.grad (propagator (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) (mfPath ρc) r t A) x -
        Torus.grad (equilibriumSemigroup (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρβ (t - r) A) x‖ ≤
          CA * Real.exp (-m * t))
    (hCB : 0 ≤ CB)
    (hBU : ∀ t, 0 < t → ∀ r ∈ Set.Icc 0 t, ∀ x,
      ‖Torus.grad (propagator (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) (mfPath ρc) r t B) x‖ ≤
        CB * Real.exp (-m * (t - r)))
    (hB2 : ∀ v, 0 ≤ v → Torus.IsCk 2 (equilibriumSemigroup (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρβ v B))
    (hBS : ∀ v, 0 ≤ v → ∀ x, ‖Torus.grad (equilibriumSemigroup
      (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρβ v B) x‖ ≤ CB * Real.exp (-m * v))
    (hBUS : ∀ t, 0 < t → ∀ r ∈ Set.Icc 0 t, ∀ x,
      ‖Torus.grad (propagator (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) (mfPath ρc) r t B) x -
        Torus.grad (equilibriumSemigroup (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρβ (t - r) B) x‖ ≤
          CB * Real.exp (-m * t))
    (δ : ℝ) (hδ : 0 ≤ δ) (t : ℝ) (ht : 0 ≤ t) :
    |2 * β⁻¹ * (∫ r in Set.Ioc 0 t,
        Eint (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρc A B t (t + δ) r) -
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β A
        (equilibriumSemigroup (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρβ δ B)| ≤
      2 * β⁻¹ * ((2 / m) * (CA * CB * (2 + Cρ)) + CA * CB / m) * Real.exp (-(m / 2) * t) := by
  set D := mfData d s Hz.hs0 Hz.hsd V β Hz.hβ with hD
  have hν : 0 < β⁻¹ := inv_pos.mpr Hz.hβ
  have hm := hF.m_pos
  have hAc : Continuous A := continuous_of_isSmooth hA
  have hBc : Continuous B := continuous_of_isSmooth hB
  have hA4 : MemSobolev ((mStar d : ℝ) + 4) A := MFSemigroup.memSobolev_of_isSmooth hA _
  have hB4 : MemSobolev ((mStar d : ℝ) + 4) B := MFSemigroup.memSobolev_of_isSmooth hB _
  have hSBc : Continuous (equilibriumSemigroup D ρβ δ B) :=
    MFAux.continuous_of_isCk ((hB2 δ hδ).of_le (by norm_num))
  have hSBm := S_memSobolev_mStar hd Hz hBc hB4 hδ
  obtain ⟨hint, hcov⟩ := susceptibilityCov_eq_integral hd s νm νp c₀ Λ₀ β V ρβ Hz A
    (equilibriumSemigroup D ρβ δ B) hAc hA4 hSBc hSBm
  -- rewrite the semigroup composition
  have hcomp : ∀ v, 0 ≤ v → equilibriumSemigroup D ρβ v (equilibriumSemigroup D ρβ δ B) =
      equilibriumSemigroup D ρβ (v + δ) B := fun v hv =>
    MFAdjoint.equilibriumSemigroup_add hd s νm νp c₀ Λ₀ β V ρβ Hz B hBc hB4 v δ hv hδ
  set w : ℝ → ℝ := fun v => ∫ x, inner ℝ (Torus.grad (equilibriumSemigroup D ρβ v A) x)
    (Torus.grad (equilibriumSemigroup D ρβ (v + δ) B) x) * ρβ x with hw
  have hwint : IntegrableOn w (Set.Ici 0) := by
    refine hint.congr_fun (fun v hv => ?_) measurableSet_Ici
    simp only [hw]
    rw [hcomp v hv]
  have hcov' : susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β A
      (equilibriumSemigroup D ρβ δ B) = 2 * β⁻¹ * ∫ v in Set.Ici (0 : ℝ), w v := by
    rw [hcov]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ici (fun v hv => ?_)
    simp only [hw]
    rw [hcomp v hv]
  rw [hcov', ← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * β⁻¹)]
  have hbd := fun v (hv : 0 ≤ v) =>
    abs_energy_le_sup (f := equilibriumSemigroup D ρβ v A)
      (g := equilibriumSemigroup D ρβ (v + δ) B) (ρ := ρβ)
      ((hA2 v hv).of_le (by norm_num)) ((hB2 (v + δ) (by linarith)).of_le (by norm_num))
      hF.rhoβ_cont hF.rhoβ_nonneg hF.rhoβ_one _ _ (hAS v hv) (hBS (v + δ) (by linarith))
  have hwb : ∀ v, 0 ≤ v → |w v| ≤ CA * CB * Real.exp (-m * v) := by
    intro v hv
    refine (hbd v hv).trans ?_
    have e3 : Real.exp (-m * (v + δ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h0 : 0 ≤ Real.exp (-m * v) := (Real.exp_pos _).le
    have : Real.exp (-m * v) * Real.exp (-m * (v + δ)) ≤ Real.exp (-m * v) := by nlinarith
    nlinarith [mul_nonneg hCA hCB]
  have key : |(∫ r in Set.Ioc 0 t, Eint D ρc A B t (t + δ) r) -
      ∫ v in Set.Ici (0 : ℝ), w v| ≤
      t * (CA * CB * (2 + Cρ) * Real.exp (-m * t)) + CA * CB / m * Real.exp (-m * t) := by
    rcases ht.eq_or_lt with h0 | htpos
    · subst h0
      have := entry_real 0 le_rfl (fun _ : ℝ => (0 : ℝ)) w (CA * CB) (CA * CB) m m hm
        continuousOn_const hwint (fun v hv => by
          have hv0 : v = 0 := le_antisymm hv.2 hv.1
          subst hv0
          simpa using hwb 0 le_rfl) hwb
      simpa using this
    · refine entry_abstract (fun r t => propagator D (mfPath ρc) r t A)
        (fun r t => propagator D (mfPath ρc) r t B) (fun v => equilibriumSemigroup D ρβ v A)
        (fun v => equilibriumSemigroup D ρβ v B) (mfPath ρc) ρβ m Cρ CA CB hm hF.Cρ_nonneg hCA
        hCB hF.rhoβ_cont hF.rhoβ_nonneg hF.rhoβ_one hF.mu_cont hF.mu_nonneg hF.mu_one hF.rho_dec
        ?_ ?_ (fun v hv => (hA2 v hv).of_le (by norm_num))
        (fun v hv => (hB2 v hv).of_le (by norm_num)) hAUS hAS hBU hBUS hBS δ hδ t htpos ?_ ?_
      · intro t' ht' r hr
        obtain ⟨F, hF', hFp⟩ := hF.classical A hA t' ht'
        rw [hFp r hr]; exact (hF'.c2 r hr).of_le (by norm_num)
      · intro t' ht' r hr
        obtain ⟨F, hF', hFp⟩ := hF.classical B hB t' ht'
        rw [hFp r hr]; exact (hF'.c2 r hr).of_le (by norm_num)
      · exact continuousOn_energy_prop hF hA hB htpos le_rfl (by linarith)
      · exact hwint
  refine (mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * β⁻¹)).trans ?_
  have hB0 : 0 ≤ CA * CB * (2 + Cρ) :=
    mul_nonneg (mul_nonneg hCA hCB) (by linarith [hF.Cρ_nonneg])
  have e1 := mul_exp_neg_le hm ht
  have e2 : Real.exp (-m * t) ≤ Real.exp (-(m / 2) * t) := Real.exp_le_exp.2 (by nlinarith)
  have hfin : t * (CA * CB * (2 + Cρ) * Real.exp (-m * t)) + CA * CB / m * Real.exp (-m * t) ≤
      ((2 / m) * (CA * CB * (2 + Cρ)) + CA * CB / m) * Real.exp (-(m / 2) * t) := by
    calc t * (CA * CB * (2 + Cρ) * Real.exp (-m * t)) + CA * CB / m * Real.exp (-m * t)
        = (CA * CB * (2 + Cρ)) * (t * Real.exp (-m * t)) + CA * CB / m * Real.exp (-m * t) := by
          ring
      _ ≤ (CA * CB * (2 + Cρ)) * ((2 / m) * Real.exp (-(m / 2) * t)) +
          CA * CB / m * Real.exp (-(m / 2) * t) := by
          have : 0 ≤ CA * CB / m := by positivity
          gcongr
      _ = ((2 / m) * (CA * CB * (2 + Cρ)) + CA * CB / m) * Real.exp (-(m / 2) * t) := by ring
  calc 2 * β⁻¹ * (t * (CA * CB * (2 + Cρ) * Real.exp (-m * t)) + CA * CB / m * Real.exp (-m * t))
      ≤ 2 * β⁻¹ * (((2 / m) * (CA * CB * (2 + Cρ)) + CA * CB / m) * Real.exp (-(m / 2) * t)) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = 2 * β⁻¹ * ((2 / m) * (CA * CB * (2 + Cρ)) + CA * CB / m) * Real.exp (-(m / 2) * t) := by
        ring



theorem posSemidef_of_approx {p : ℕ} (Sg : Matrix (Fin p) (Fin p) ℝ)
    (M : ℝ → Matrix (Fin p) (Fin p) ℝ) (hM : ∀ u, 0 ≤ u → (M u).PosSemidef) (C c : ℝ)
    (hc : 0 < c) (hap : ∀ u, 0 ≤ u → ∀ a b, |M u a b - Sg a b| ≤ C * Real.exp (-c * u)) :
    Sg.PosSemidef := by
  have hexp : Tendsto (fun u : ℝ => C * Real.exp (-c * u)) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hc)).const_mul C
    rw [mul_zero] at h
    refine h.congr fun u => ?_
    simp [neg_mul]
  have hent : ∀ a b, Tendsto (fun u => M u a b) atTop (𝓝 (Sg a b)) := by
    intro a b
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _) ?_ hexp
    filter_upwards [eventually_ge_atTop 0] with u hu
    rw [Real.norm_eq_abs]; exact hap u hu a b
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext a b
    simp only [Matrix.conjTranspose_apply, star_trivial]
    have h1 : Tendsto (fun u => M u b a) atTop (𝓝 (Sg b a)) := hent b a
    have h2 : ∀ᶠ u in atTop, M u b a = M u a b := by
      filter_upwards [eventually_ge_atTop 0] with u hu
      have h := congrFun (congrFun (hM u hu).1 a) b
      simpa [Matrix.conjTranspose_apply] using h
    exact tendsto_nhds_unique (h1.congr' h2) (hent a b)
  · intro ξ
    have hq : Tendsto (fun u => dotProduct (star ξ) (Matrix.mulVec (M u) ξ)) atTop
        (𝓝 (dotProduct (star ξ) (Matrix.mulVec Sg ξ))) := by
      simp only [dotProduct, Matrix.mulVec]
      exact tendsto_finsetSum _ fun a _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ fun b _ => (hent a b).mul tendsto_const_nhds)
    refine ge_of_tendsto hq ?_
    filter_upwards [eventually_ge_atTop 0] with u hu
    exact (Matrix.posSemidef_iff_dotProduct_mulVec.1 (hM u hu)).2 ξ

theorem Mcov_posSemidef {D : DynData d} {ρc : ℝ → Coeff d} {ρβ : Torus d → ℝ} {m Cρ : ℝ}
    (hF : LossFacts D ρc ρβ m Cρ) (hD : 0 ≤ D.invβ) {p : ℕ} (τ : Fin p → ℝ)
    (hτ : ∀ a, 0 ≤ τ a) (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) (u : ℝ)
    (hu : 0 ≤ u) : (Mcov D ρc τ φ u).PosSemidef := by
  refine gram_posSemidef (fun a => u + τ a)
    (fun a r => Torus.grad (propagator D (mfPath ρc) r (u + τ a) (φ a))) (mfPath ρc)
    (2 * D.invβ) (by positivity) ?_ (fun r hr => hF.mu_cont r hr.le)
    (fun r hr x => hF.mu_nonneg r hr.le x) ?_
  · intro a r hr
    obtain ⟨F, hF', hFp⟩ := hF.classical (φ a) (hφ a) (u + τ a) (lt_of_lt_of_le hr.1 hr.2)
    rw [hFp r ⟨hr.1.le, hr.2⟩]
    exact continuous_grad ((hF'.c2 r ⟨hr.1.le, hr.2⟩).of_le (by norm_num))
  · intro a b
    have hmm : 0 ≤ min (u + τ a) (u + τ b) :=
      le_min (by linarith [hτ a]) (by linarith [hτ b])
    rcases hmm.eq_or_lt with h0 | hpos
    · rw [← h0, Set.Ioc_self]
      exact integrableOn_empty
    · exact ((continuousOn_energy_prop hF (hφ a) (hφ b) hpos (min_le_left _ _)
        (min_le_right _ _)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self


abbrev mfD {s βm βp : ℝ} {K : ℕ} {V ρ₀ : Torus d → ℝ} (H : FiniteRegHyp d s βm βp K V ρ₀)
    {β : ℝ} (hβ : β ∈ Set.Icc βm βp) : DynData d :=
  mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)

theorem Mcov_entry (hd : 1 ≤ d) {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ}
    (Hz : MFAdjoint.FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ) {ρc : ℝ → Coeff d}
    {m Cρ : ℝ} (hF : LossFacts (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρc ρβ m Cρ)
    {p : ℕ} (τ : Fin p → ℝ) (hτ : ∀ a, 0 ≤ τ a) (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ a, Torus.IsSmooth (φ a)) (CA : Fin p → ℝ) (hCA0 : ∀ a, 0 ≤ CA a)
    (hA2 : ∀ a v, 0 ≤ v →
      Torus.IsCk 2 (equilibriumSemigroup (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρβ v (φ a)))
    (hAS : ∀ a v, 0 ≤ v → ∀ x, ‖Torus.grad (equilibriumSemigroup
      (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρβ v (φ a)) x‖ ≤ CA a * Real.exp (-m * v))
    (hAUS : ∀ a t, 0 < t → ∀ r ∈ Set.Icc 0 t, ∀ x,
      ‖Torus.grad (propagator (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) (mfPath ρc) r t (φ a)) x -
        Torus.grad (equilibriumSemigroup (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρβ (t - r)
          (φ a)) x‖ ≤ CA a * Real.exp (-m * t))
    (hAU : ∀ a t, 0 < t → ∀ r ∈ Set.Icc 0 t, ∀ x,
      ‖Torus.grad (propagator (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) (mfPath ρc) r t (φ a)) x‖ ≤
        CA a * Real.exp (-m * (t - r)))
    (u : ℝ) (hu : 0 ≤ u) (a b : Fin p) :
    |Mcov (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρc τ φ u a b -
        stationaryLagCov d s β (mfData d s Hz.hs0 Hz.hsd V β Hz.hβ) ρβ τ φ a b| ≤
      (2 * β⁻¹ * ((2 / m) * (CA a * CA b * (2 + Cρ)) + CA a * CA b / m)) *
        Real.exp (-(m / 2) * u) := by
  set D := mfData d s Hz.hs0 Hz.hsd V β Hz.hβ with hD
  have hinv : D.invβ = β⁻¹ := rfl
  have hν : 0 < β⁻¹ := inv_pos.mpr Hz.hβ
  have hm := hF.m_pos
  have hCρ := hF.Cρ_nonneg
  have hCab : 0 ≤ 2 * β⁻¹ * ((2 / m) * (CA a * CA b * (2 + Cρ)) + CA a * CA b / m) := by
    have := hCA0 a; have := hCA0 b
    positivity
  have hCab' : 0 ≤ 2 * β⁻¹ * ((2 / m) * (CA b * CA a * (2 + Cρ)) + CA b * CA a / m) := by
    have := hCA0 a; have := hCA0 b
    positivity
  by_cases hab : τ a ≤ τ b
  · have hmin : min (u + τ a) (u + τ b) = u + τ a := min_eq_left (by linarith)
    have hSig : stationaryLagCov d s β D ρβ τ φ a b = susceptibilityCov (periodicRiesz d s)
        (withDensityReal ρβ) β (φ a) (equilibriumSemigroup D ρβ (τ b - τ a) (φ b)) := by
      simp [stationaryLagCov, hab]
    have e : u + τ b = u + τ a + (τ b - τ a) := by ring
    have h1 := entry_ordered hd Hz hF (hφ a) (hφ b) (hCA0 a) (hA2 a) (hAS a) (hAUS a) (hCA0 b)
      (hAU b) (hA2 b) (hAS b) (hAUS b) (τ b - τ a) (by linarith) (u + τ a) (by linarith [hτ a])
    rw [← e] at h1
    have h2 : Mcov D ρc τ φ u a b = 2 * β⁻¹ * ∫ r in Set.Ioc 0 (u + τ a),
        Eint D ρc (φ a) (φ b) (u + τ a) (u + τ b) r := by
      simp only [Mcov, Matrix.of_apply, hmin, hinv]
      rw [integral_Icc_eq_integral_Ioc]
    rw [h2, hSig]
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hτ a])) hCab)
  · push_neg at hab
    have hmin : min (u + τ a) (u + τ b) = u + τ b := min_eq_right (by linarith)
    have hSig : stationaryLagCov d s β D ρβ τ φ a b = susceptibilityCov (periodicRiesz d s)
        (withDensityReal ρβ) β (equilibriumSemigroup D ρβ (τ a - τ b) (φ a)) (φ b) := by
      simp [stationaryLagCov, not_le.2 hab]
    have e : u + τ a = u + τ b + (τ a - τ b) := by ring
    have hφac : Continuous (φ a) := continuous_of_isSmooth (hφ a)
    have hφbc : Continuous (φ b) := continuous_of_isSmooth (hφ b)
    have hφa4 : MemSobolev ((mStar d : ℝ) + 4) (φ a) := MFSemigroup.memSobolev_of_isSmooth (hφ a) _
    have hφb4 : MemSobolev ((mStar d : ℝ) + 4) (φ b) := MFSemigroup.memSobolev_of_isSmooth (hφ b) _
    have hSc : Continuous (equilibriumSemigroup D ρβ (τ a - τ b) (φ a)) :=
      MFAux.continuous_of_isCk ((hA2 a (τ a - τ b) (by linarith)).of_le (by norm_num))
    have hSm := S_memSobolev_mStar hd Hz hφac hφa4 (τ := τ a - τ b) (by linarith)
    have hsym := cov_symm hd Hz hSc hSm hφbc hφb4
    have h1 := entry_ordered hd Hz hF (hφ b) (hφ a) (hCA0 b) (hA2 b) (hAS b) (hAUS b) (hCA0 a)
      (hAU a) (hA2 a) (hAS a) (hAUS a) (τ a - τ b) (by linarith) (u + τ b) (by linarith [hτ b])
    rw [← e] at h1
    have h2 : Mcov D ρc τ φ u a b = 2 * β⁻¹ * ∫ r in Set.Ioc 0 (u + τ b),
        Eint D ρc (φ b) (φ a) (u + τ b) (u + τ a) r := by
      simp only [Mcov, Matrix.of_apply, hmin, hinv]
      rw [integral_Icc_eq_integral_Ioc]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc (fun r _ => ?_)
      exact Eint_comm D ρc (φ a) (φ b) _ _ r
    rw [h2, hSig, hsym]
    refine h1.trans ?_
    have : CA b * CA a = CA a * CA b := mul_comm _ _
    rw [this]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hτ b])) hCab

theorem exists_cov_comparison (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (j : ℕ) (hjeven : Even j) (hj : (d : ℝ) / 2 + 4 < j)
    (hK : 2 * j + 4 * d + 20 ≤ K) (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρc : ℝ → Coeff d)
    (hρc : IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Continuous ρβ)
    (hpos : ∀ x, 0 < ρβ x) (p : ℕ) (τ : Fin p → ℝ) (hτ : ∀ a, 0 ≤ τ a)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    (stationaryLagCov d s β (mfD H hβ) ρβ τ φ).PosSemidef ∧
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ u : ℝ, 0 ≤ u →
      (Mcov (mfD H hβ) ρc τ φ u).PosSemidef ∧
      ∀ a b, |Mcov (mfD H hβ) ρc τ φ u a b -
        stationaryLagCov d s β (mfD H hβ) ρβ τ φ a b| ≤ C * Real.exp (-c * u) := by
  obtain ⟨m, Cρ, c₀, Λ₀, hF, Hz⟩ :=
    loss_facts hd s βm βp K V ρ₀ H j hjeven hj hK β hβ ρc hρc ρβ hρβ hρC hpos
  have hm := hF.m_pos
  have hν : 0 < β⁻¹ := inv_pos.2 (lt_of_lt_of_le H.hβm hβ.1)
  choose CA hCA0 hA2 hAS hAUS hAU using fun a => hF.grad (φ a) (hφ a)
  have hent := fun u (hu : 0 ≤ u) a b => Mcov_entry hd Hz hF τ hτ φ hφ CA hCA0 hA2 hAS hAUS hAU u hu a b
  set Cab : Fin p → Fin p → ℝ := fun a b =>
    2 * β⁻¹ * ((2 / m) * (CA a * CA b * (2 + Cρ)) + CA a * CA b / m) with hCab
  have hCab0 : ∀ a b, 0 ≤ Cab a b := by
    intro a b
    have := hCA0 a; have := hCA0 b; have := hF.Cρ_nonneg
    simp only [hCab]
    positivity
  set C : ℝ := 1 + ∑ a, ∑ b, Cab a b with hC
  have hCpos : 0 < C := by
    have : 0 ≤ ∑ a, ∑ b, Cab a b := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      hCab0 a b
    rw [hC]; linarith
  have hCle : ∀ a b, Cab a b ≤ C := by
    intro a b
    have h1 : Cab a b ≤ ∑ b', Cab a b' :=
      Finset.single_le_sum (f := fun b' => Cab a b') (fun b' _ => hCab0 a b') (Finset.mem_univ b)
    have h2 : ∑ b', Cab a b' ≤ ∑ a', ∑ b', Cab a' b' :=
      Finset.single_le_sum (f := fun a' => ∑ b', Cab a' b')
        (fun a' _ => Finset.sum_nonneg fun b' _ => hCab0 a' b') (Finset.mem_univ a)
    rw [hC]; linarith
  have hbound : ∀ u, 0 ≤ u → ∀ a b, |Mcov (mfD H hβ) ρc τ φ u a b -
      stationaryLagCov d s β (mfD H hβ) ρβ τ φ a b| ≤ C * Real.exp (-(m / 2) * u) := by
    intro u hu a b
    refine (hent u hu a b).trans ?_
    exact mul_le_mul_of_nonneg_right (hCle a b) (Real.exp_pos _).le
  have hMpsd : ∀ u, 0 ≤ u → (Mcov (mfD H hβ) ρc τ φ u).PosSemidef := fun u hu =>
    Mcov_posSemidef hF (by exact hν.le) τ hτ φ hφ u hu
  refine ⟨posSemidef_of_approx _ (fun u => Mcov (mfD H hβ) ρc τ φ u) hMpsd C (m / 2)
    (by linarith) hbound, C, m / 2, hCpos, by linarith, fun u hu => ⟨hMpsd u hu, hbound u hu⟩⟩



/-! ### I. The transported initial part -/

theorem summable_of_memSobolev_sub_const {m : ℝ} {f : Torus d → ℝ} {c : ℝ}
    (hmem : MemSobolev m (fun x => f x - c)) :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff f k ^ 2 := by
  have hf2 : MemLp f 2 volume := by
    have := hmem.1.add (memLp_const (c : ℝ) : MemLp (fun _ : Torus d => c) 2 volume)
    have e : ((fun x => f x - c) + fun _ : Torus d => c) = f := by
      funext x; simp
    rwa [e] at this
  have hcoef : ∀ k : NonzeroLattice d, Torus.funRealCoeff (fun x => f x - c) k =
      Torus.funRealCoeff f k := by
    intro k
    unfold Torus.funRealCoeff
    have hL : MemLp (Torus.realMode k) 2 volume :=
      (continuous_realMode' k).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hrm : Integrable (fun x => Torus.realMode k x * f x) := hL.integrable_mul hf2
    have hrc : Integrable (fun x => Torus.realMode k x * c) :=
      ((continuous_realMode' k).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).mul_const c
    have : (fun x => Torus.realMode k x * (f x - c)) =
        fun x => Torus.realMode k x * f x - Torus.realMode k x * c := by
      funext x; ring
    rw [this, integral_sub hrm hrc, integral_mul_const, Torus.integral_realMode]
    ring
  have h := hmem.2
  simp only [hcoef] at h
  exact h

theorem norm_euclid_le_sum {p : ℕ} (x : EuclideanSpace ℝ (Fin p)) : ‖x‖ ≤ ∑ a, |x a| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  simp only [Real.norm_eq_abs]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => abs_nonneg _)

theorem exists_initial_part_bound (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (j : ℕ) (hjeven : Even j) (hj : (d : ℝ) / 2 + 4 < j)
    (hK : 2 * j + 4 * d + 20 ≤ K) (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρc : ℝ → Coeff d)
    (hρc : IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Continuous ρβ)
    (hpos : ∀ x, 0 < ρβ x) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      MemSobolev (j : ℝ) (fun x => propagator (mfD H hβ) (mfPath ρc) 0 t φ x -
          pair (withDensityReal ρβ) (propagator (mfD H hβ) (mfPath ρc) 0 t φ)) ∧
      ∀ F : NegSobolev d (j : ℝ),
        |NegSobolev.eval F (propagator (mfD H hβ) (mfPath ρc) 0 t φ)| ≤
          C * Real.exp (-c * t) * ‖F‖ := by
  obtain ⟨C5, c5, κ5, hC5, hc5, hκ5, h52⟩ :=
    MFAdjoint.adjoint_decay_comparison_wiring hd s βm βp K V ρ₀ H j hjeven hj hK
  have hφc := continuous_of_isSmooth hφ
  have hφj : MemSobolev (j : ℝ) φ := MFSemigroup.memSobolev_of_isSmooth hφ _
  set N : ℝ := sobolevNorm (j : ℝ) (projMean (withDensityReal ρβ) φ) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  refine ⟨C5 * N + 1, c5, by positivity, hc5, fun t ht => ?_⟩
  obtain ⟨hm1, hn1, -⟩ := h52 β hβ ρc hρc ρβ hρβ hρC hpos φ hφc hφj 0 t le_rfl ht
  refine ⟨hm1, fun F => ?_⟩
  have h1 := abs_eval_le_sobolev F (propagator (mfD H hβ) (mfPath ρc) 0 t φ)
    (pair (withDensityReal ρβ) (propagator (mfD H hβ) (mfPath ρc) 0 t φ)) hm1
  refine h1.trans ?_
  have hn1' : sobolevNorm (j : ℝ) (fun x => propagator (mfD H hβ) (mfPath ρc) 0 t φ x -
      pair (withDensityReal ρβ) (propagator (mfD H hβ) (mfPath ρc) 0 t φ)) ≤
      C5 * Real.exp (-c5 * t) * N := by
    have := hn1
    simp only [sub_zero] at this
    exact this
  have hF0 : 0 ≤ ‖F‖ := norm_nonneg _
  have hE : 0 ≤ Real.exp (-c5 * t) := (Real.exp_pos _).le
  calc ‖F‖ * sobolevNorm (j : ℝ) (fun x => propagator (mfD H hβ) (mfPath ρc) 0 t φ x -
        pair (withDensityReal ρβ) (propagator (mfD H hβ) (mfPath ρc) 0 t φ))
      ≤ ‖F‖ * (C5 * Real.exp (-c5 * t) * N) := mul_le_mul_of_nonneg_left hn1' hF0
    _ ≤ ‖F‖ * ((C5 * N + 1) * Real.exp (-c5 * t)) := by
        refine mul_le_mul_of_nonneg_left ?_ hF0
        nlinarith [mul_nonneg hC5.le hN0]
    _ = (C5 * N + 1) * Real.exp (-c5 * t) * ‖F‖ := by ring



/-! ### J. Corollary 5.3 -/

theorem linear_loss_of_initial_law_aux (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (j : ℕ) (hjeven : Even j) (hj : (d : ℝ) / 2 + 4 < j)
    (hK : 2 * j + 4 * d + 20 ≤ K) (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρc : ℝ → Coeff d)
    (hρc : IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Continuous ρβ)
    (hpos : ∀ x, 0 < ρβ x) (p : ℕ) (τ : Fin p → ℝ) (hτ : ∀ a, 0 ≤ τ a)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η₀ : Ω → NegSobolev d j) (η : ℝ → Ω → NegSobolev d j),
        Measurable η₀ → Integrable (fun ω => ‖η₀ ω‖) P →
        IsLinearSPDESolution P (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) (mfPath ρc) j
          η₀ η →
        ∀ u : ℝ, 0 ≤ u →
          smoothDist 2
            (law P fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (η (u + τ a) ω) (φ a) :
              EuclideanSpace ℝ (Fin p)))
            (ProbabilityTheory.multivariateGaussian 0
              (stationaryLagCov d s β (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) ρβ τ φ)) ≤
          C * (1 + ∫ ω, ‖η₀ ω‖ ∂P) * Real.exp (-c * u) := by
  obtain ⟨hSig, C₁, c₁, hC₁, hc₁, hcov⟩ :=
    exists_cov_comparison hd s βm βp K V ρ₀ H j hjeven hj hK β hβ ρc hρc ρβ hρβ hρC hpos p τ hτ
      φ hφ
  choose C₂ c₂ hC₂ hc₂ hinit using fun a =>
    exists_initial_part_bound hd s βm βp K V ρ₀ H j hjeven hj hK β hβ ρc hρc ρβ hρβ hρC hpos
      (φ a) (hφ a)
  have hS0 : 0 ≤ ∑ a, 1 / c₂ a := Finset.sum_nonneg fun a _ => (one_div_pos.2 (hc₂ a)).le
  set c₀ : ℝ := 1 / (1 + ∑ a, 1 / c₂ a) with hc₀
  have hc₀pos : 0 < c₀ := one_div_pos.2 (by linarith)
  have hc₀le : ∀ a, c₀ ≤ c₂ a := by
    intro a
    have hS : 1 / c₂ a ≤ ∑ b, 1 / c₂ b :=
      Finset.single_le_sum (f := fun b => 1 / c₂ b) (fun b _ => (one_div_pos.2 (hc₂ b)).le)
        (Finset.mem_univ a)
    have h1 : 1 / (1 + ∑ b, 1 / c₂ b) ≤ 1 / (1 / c₂ a) :=
      one_div_le_one_div_of_le (one_div_pos.2 (hc₂ a)) (by linarith)
    rwa [one_div_one_div] at h1
  set c : ℝ := min c₁ c₀ with hc
  have hcpos : 0 < c := lt_min hc₁ hc₀pos
  have hc_c₁ : c ≤ c₁ := min_le_left _ _
  have hc_c₂ : ∀ a, c ≤ c₂ a := fun a => (min_le_right _ _).trans (hc₀le a)
  set S₂ : ℝ := ∑ a, C₂ a with hS₂
  have hS₂0 : 0 ≤ S₂ := Finset.sum_nonneg fun a _ => (hC₂ a).le
  have hq0 : 0 ≤ (p : ℝ) ^ 2 * C₁ := by positivity
  set C : ℝ := S₂ + (p : ℝ) ^ 2 * C₁ + 1 with hC
  have hCpos : 0 < C := by rw [hC]; linarith
  refine ⟨C, c, hCpos, hcpos, ?_⟩
  intro Ω _ P _ η₀ η hη₀ hη₀i hsol u hu
  obtain ⟨hindep, hlaw⟩ :=
    hsol.gaussian_part p (fun a => u + τ a) φ (fun a => add_nonneg hu (hτ a)) hφ
  obtain ⟨hMpsd, hcovu⟩ := hcov u hu
  set D := mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1) with hD
  set ψ : Fin p → Torus d → ℝ := fun a => propagator D (mfPath ρc) 0 (u + τ a) (φ a) with hψ
  set Gf : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval (η (u + τ a) ω) (φ a) - NegSobolev.eval (η₀ ω) (ψ a) with hGf
  set Xf : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval (η (u + τ a) ω) (φ a) with hXf
  set Yf : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval (η₀ ω) (ψ a) with hYf
  have hlaw' : law P Gf = ProbabilityTheory.multivariateGaussian 0 (Mcov D ρc τ φ u) := hlaw
  -- summability of the Sobolev series of the test functions
  have hsumφ : ∀ a, Summable fun k : NonzeroLattice d =>
      Lattice.jp k.1 ^ (2 * (j : ℝ)) * Torus.funRealCoeff (φ a) k ^ 2 := fun a =>
    (MFSemigroup.memSobolev_of_isSmooth (hφ a) (j : ℝ)).2
  have hsumψ : ∀ a, Summable fun k : NonzeroLattice d =>
      Lattice.jp k.1 ^ (2 * (j : ℝ)) * Torus.funRealCoeff (ψ a) k ^ 2 := fun a =>
    summable_of_memSobolev_sub_const ((hinit a (u + τ a) (by linarith [hτ a])).1)
  have hmeas_eval : ∀ (t : ℝ) (ψ' : Torus d → ℝ), (Summable fun k : NonzeroLattice d =>
      Lattice.jp k.1 ^ (2 * (j : ℝ)) * Torus.funRealCoeff ψ' k ^ 2) →
      Measurable fun ω => NegSobolev.eval (η t ω) ψ' := fun t ψ' hs =>
    (continuous_eval_const ψ' hs).measurable.comp (hsol.meas t)
  have hmeas_eval0 : ∀ ψ' : Torus d → ℝ, (Summable fun k : NonzeroLattice d =>
      Lattice.jp k.1 ^ (2 * (j : ℝ)) * Torus.funRealCoeff ψ' k ^ 2) →
      Measurable fun ω => NegSobolev.eval (η₀ ω) ψ' := fun ψ' hs =>
    (continuous_eval_const ψ' hs).measurable.comp hη₀
  have hXm : Measurable Xf := (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
    (measurable_pi_iff.2 fun a => hmeas_eval (u + τ a) (φ a) (hsumφ a))
  have hYm : Measurable Yf := (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
    (measurable_pi_iff.2 fun a => hmeas_eval0 (ψ a) (hsumψ a))
  have hGm : Measurable Gf := (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
    (measurable_pi_iff.2 fun a =>
      (hmeas_eval (u + τ a) (φ a) (hsumφ a)).sub (hmeas_eval0 (ψ a) (hsumψ a)))
  -- the transported initial part
  set Kc : ℝ := S₂ * Real.exp (-c * u) with hKc
  have hYb : ∀ ω, ‖Yf ω‖ ≤ Kc * ‖η₀ ω‖ := by
    intro ω
    refine (norm_euclid_le_sum _).trans ?_
    calc ∑ a, |(Yf ω) a| ≤ ∑ a, C₂ a * Real.exp (-c * u) * ‖η₀ ω‖ := by
          refine Finset.sum_le_sum fun a _ => ?_
          have h1 := (hinit a (u + τ a) (by linarith [hτ a])).2 (η₀ ω)
          have h2 : Real.exp (-c₂ a * (u + τ a)) ≤ Real.exp (-c * u) :=
            Real.exp_le_exp.2 (by
              have := mul_le_mul_of_nonneg_right (hc_c₂ a) hu
              have := mul_nonneg (hc₂ a).le (hτ a)
              nlinarith)
          have h3 : |(Yf ω) a| ≤ C₂ a * Real.exp (-c₂ a * (u + τ a)) * ‖η₀ ω‖ := h1
          refine h3.trans ?_
          have := (hC₂ a).le
          have := norm_nonneg (η₀ ω)
          gcongr
      _ = Kc * ‖η₀ ω‖ := by rw [hKc, hS₂, Finset.sum_mul, Finset.sum_mul]
  have hYi : Integrable (fun ω => ‖Yf ω‖) P :=
    (hη₀i.const_mul Kc).mono' hYm.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hYb ω)
  have hGi : Integrable (fun ω => ‖Gf ω‖) P :=
    integrable_norm_of_law_gaussian P Gf hGm (Mcov D ρc τ φ u) hlaw'
  have hXG : ∀ ω, Xf ω = Gf ω + Yf ω := by
    intro ω; ext a; simp [hXf, hGf, hYf]
  have hXi : Integrable (fun ω => ‖Xf ω‖) P :=
    (hGi.add hYi).mono' hXm.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hXG ω]; exact norm_add_le _ _)
  have hXGY : ∀ ω, Xf ω - Gf ω = Yf ω := by
    intro ω; rw [hXG ω]; abel
  have key := smoothDist_le_of_gaussian_part P Xf Gf hXm hGm hXi hGi (Mcov D ρc τ φ u)
    (stationaryLagCov d s β D ρβ τ φ) hMpsd hSig hlaw'
  refine key.trans ?_
  -- the two error terms
  set E : ℝ := ∫ ω, ‖η₀ ω‖ ∂P with hE
  have hE0 : 0 ≤ E := integral_nonneg fun ω => norm_nonneg _
  have t1 : ∫ ω, ‖Xf ω - Gf ω‖ ∂P ≤ Kc * E := by
    calc ∫ ω, ‖Xf ω - Gf ω‖ ∂P = ∫ ω, ‖Yf ω‖ ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω => by
            show ‖Xf ω - Gf ω‖ = ‖Yf ω‖
            rw [hXGY ω])
      _ ≤ ∫ ω, Kc * ‖η₀ ω‖ ∂P := integral_mono hYi (hη₀i.const_mul Kc) hYb
      _ = Kc * E := integral_const_mul _ _
  have t2 : (1 / 2 : ℝ) * traceNormMatrix (Mcov D ρc τ φ u - stationaryLagCov d s β D ρβ τ φ) ≤
      (1 / 2) * ((p : ℝ) ^ 2 * C₁ * Real.exp (-c * u)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (traceNormMatrix_le_sum _).trans ?_
    have hent : ∀ a b, |(Mcov D ρc τ φ u - stationaryLagCov d s β D ρβ τ φ) a b| ≤
        C₁ * Real.exp (-c * u) := by
      intro a b
      rw [Matrix.sub_apply]
      refine (hcovu a b).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hC₁.le
    calc ∑ a, ∑ b, |(Mcov D ρc τ φ u - stationaryLagCov d s β D ρβ τ φ) a b|
        ≤ ∑ _a : Fin p, ∑ _b : Fin p, C₁ * Real.exp (-c * u) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hent a b
      _ = (p : ℝ) ^ 2 * C₁ * Real.exp (-c * u) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  refine (add_le_add t1 t2).trans ?_
  have hexp : 0 ≤ Real.exp (-c * u) := (Real.exp_pos _).le
  have : Kc * E + (1 / 2) * ((p : ℝ) ^ 2 * C₁ * Real.exp (-c * u)) ≤
      C * (1 + E) * Real.exp (-c * u) := by
    rw [hKc, hC]
    nlinarith [mul_nonneg hS₂0 hE0, mul_nonneg hq0 hE0, mul_nonneg hq0 hexp,
      mul_nonneg (mul_nonneg hS₂0 hE0) hexp, mul_nonneg hS₂0 hexp, mul_nonneg hE0 hexp,
      mul_nonneg (mul_nonneg hq0 hE0) hexp]
  exact this


end HRS.PDE.MFLinear
