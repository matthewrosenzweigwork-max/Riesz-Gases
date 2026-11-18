import HRS.Commutator.Torus.TPOSAux3

/-!
# T-POS helpers, part 4: lattice sums and the periodisation `perio`

Summability of `∑_m h(y+m)` for decaying `h`, measurability/integrability of `perio f`, its mean and its
Fourier coefficients (`fcoef (perio f) k = 𝓕 f (k)`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tpos_finite_norm_le (R : ℝ) : {m : Lattice d | ‖Lattice.toEuc m‖ ≤ R}.Finite := by
  refine (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-⌈R⌉) ⌈R⌉) : Finset (Lattice d)).finite_toSet.subset ?_
  intro m hm
  simp only [Set.mem_setOf_eq] at hm
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h1 := KernelAux.abs_coord_le_enorm m i
  have h2 : |((m i : ℤ) : ℝ)| ≤ R := h1.trans hm
  have h3 := abs_le.1 h2
  constructor
  · have : (-(⌈R⌉ : ℝ)) ≤ (m i : ℝ) := by
      have := Int.le_ceil R
      linarith [h3.1]
    exact_mod_cast this
  · have : (m i : ℝ) ≤ (⌈R⌉ : ℝ) := by
      have := Int.le_ceil R
      linarith [h3.2]
    exact_mod_cast this

lemma tpos_summable_rpow {r : ℝ} (hr : (d : ℝ) < r) :
    Summable (fun m : Lattice d => ‖Lattice.toEuc m‖ ^ (-r)) := by
  have h := summable_enorm_rpow_aux (d := d) (-r) (by linarith)
  have h2 : Summable (Set.indicator {k : Lattice d | k ≠ 0} (fun m : Lattice d => ‖Lattice.toEuc m‖ ^ (-r))) :=
    (summable_subtype_iff_indicator (s := {k : Lattice d | k ≠ 0})).1 h
  have hr0 : -r ≠ 0 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    intro h0; linarith
  have : Set.indicator {k : Lattice d | k ≠ 0} (fun m : Lattice d => ‖Lattice.toEuc m‖ ^ (-r)) =
      fun m : Lattice d => ‖Lattice.toEuc m‖ ^ (-r) := by
    funext m
    by_cases hm : m = 0
    · subst hm
      have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
      simp [this, Real.zero_rpow hr0]
    · simp [hm]
  rwa [this] at h2

lemma tpos_summable_shift {h : Euc d → ℝ} {C r : ℝ} (hC : 0 ≤ C) (hr : (d : ℝ) < r)
    (hb : ∀ z, z ≠ 0 → |h z| ≤ C * ‖z‖ ^ (-r)) (y : Euc d) :
    Summable (fun m : Lattice d => h (y + Lattice.toEuc m)) := by
  have hs := (tpos_summable_rpow (d := d) hr).mul_left (C * 2 ^ r)
  refine Summable.of_norm_bounded_eventually hs ?_
  have hfin := tpos_finite_norm_le (d := d) (2 * ‖y‖)
  refine Filter.eventually_cofinite.2 (hfin.subset ?_)
  intro m hm
  simp only [Set.mem_setOf_eq]
  by_contra hlt
  push Not at hlt
  apply hm
  have hmpos : 0 < ‖Lattice.toEuc m‖ := lt_of_le_of_lt (by positivity) hlt
  have hlow : ‖Lattice.toEuc m‖ / 2 ≤ ‖y + Lattice.toEuc m‖ := by
    have := norm_sub_norm_le (Lattice.toEuc m) (-y)
    rw [sub_neg_eq_add, add_comm, norm_neg] at this
    linarith
  have hz : y + Lattice.toEuc m ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hlow
    linarith
  have h1 := hb _ hz
  have h2 : ‖y + Lattice.toEuc m‖ ^ (-r) ≤ (‖Lattice.toEuc m‖ / 2) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith)
  have h3 : (‖Lattice.toEuc m‖ / 2) ^ (-r) = 2 ^ r * ‖Lattice.toEuc m‖ ^ (-r) := by
    rw [Real.div_rpow hmpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) r,
      div_inv_eq_mul, mul_comm]
  rw [Real.norm_eq_abs]
  calc |h (y + Lattice.toEuc m)| ≤ C * ‖y + Lattice.toEuc m‖ ^ (-r) := h1
    _ ≤ C * (2 ^ r * ‖Lattice.toEuc m‖ ^ (-r)) := by rw [← h3]; exact mul_le_mul_of_nonneg_left h2 hC
    _ = _ := by ring

lemma tpos_measurable_rep : Measurable (Torus.rep : Torus d → Euc d) := by
  unfold Torus.rep
  refine (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp (measurable_pi_iff.mpr fun i => ?_)
  exact measurable_subtype_coe.comp ((AddCircle.measurableEquivIco 1 0).measurable.comp (measurable_pi_apply i))

lemma tpos_perio_mk (f : Euc d → ℝ) (y : Euc d) :
    perio f (Torus.mk y) = ∑' m : Lattice d, f (y + Lattice.toEuc m) := by
  obtain ⟨n, hn⟩ := Torus.rep_mk y
  unfold perio
  rw [hn, ← (Equiv.addLeft n).tsum_eq (fun m : Lattice d => f (y + Lattice.toEuc m))]
  refine tsum_congr fun m => ?_
  simp only [Equiv.coe_addLeft, KernelAux.toEuc_add, add_assoc]

lemma tpos_perio_measurable {f : Euc d → ℝ} (hf : Measurable f) : Measurable (perio f : Torus d → ℝ) := by
  unfold perio
  exact Measurable.tsum fun m => hf.comp (tpos_measurable_rep.add_const _)

lemma tpos_perio_nonneg {f : Euc d → ℝ} (hnn : ∀ z, 0 ≤ f z) (x : Torus d) : 0 ≤ perio f x :=
  tsum_nonneg fun m => hnn _

lemma tpos_lintegral_perio {f : Euc d → ℝ} (hf : Measurable f) (hnn : ∀ z, 0 ≤ f z)
    (hsum : ∀ y, Summable fun m : Lattice d => f (y + Lattice.toEuc m)) :
    ∫⁻ x, ENNReal.ofReal (perio f x) = ∫⁻ y, ENNReal.ofReal (f y) := by
  rw [tpos_torus_lintegral (fun x => ENNReal.ofReal (perio f x)), tpos_lintegral_unfold (fun y => ENNReal.ofReal (f y))]
  have h1 : ∀ y : Euc d, ENNReal.ofReal (perio f (Torus.mk y)) =
      ∑' m : Lattice d, ENNReal.ofReal (f (y + Lattice.toEuc m)) := by
    intro y
    rw [tpos_perio_mk, ENNReal.ofReal_tsum_of_nonneg (fun m => hnn _) (hsum y)]
  simp_rw [h1]
  rw [lintegral_tsum]
  intro m
  exact (ENNReal.measurable_ofReal.comp (hf.comp (measurable_id.add_const _))).aemeasurable

lemma tpos_integrable_perio {f : Euc d → ℝ} (hf : Measurable f) (hint : Integrable f)
    (hnn : ∀ z, 0 ≤ f z) (hsum : ∀ y, Summable fun m : Lattice d => f (y + Lattice.toEuc m)) :
    Integrable (perio f : Torus d → ℝ) := by
  refine ⟨(tpos_perio_measurable hf).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have h : ∀ x : Torus d, ‖perio f x‖ₑ = ENNReal.ofReal (perio f x) := fun x => by
    rw [Real.enorm_of_nonneg (tpos_perio_nonneg hnn x)]
  simp_rw [h]
  rw [tpos_lintegral_perio hf hnn hsum]
  have := hint.hasFiniteIntegral
  unfold HasFiniteIntegral at this
  have h2 : ∀ y : Euc d, ‖f y‖ₑ = ENNReal.ofReal (f y) := fun y => by
    rw [Real.enorm_of_nonneg (hnn y)]
  simp_rw [h2] at this
  exact this

lemma tpos_integral_perio {f : Euc d → ℝ} (hf : Measurable f) (hint : Integrable f)
    (hsum : ∀ y, Summable fun m : Lattice d => f (y + Lattice.toEuc m)) :
    ∫ x : Torus d, perio f x = ∫ y : Euc d, f y := by
  rw [tpos_torus_integral, tpos_integral_unfold hint]
  refine setIntegral_congr_fun tpos_measurableSet_cell0 fun y _ => ?_
  exact tpos_perio_mk f y

lemma tpos_mode_mk_neg (k : Lattice d) (y : Euc d) :
    Torus.mode (-k) (Torus.mk y) =
      Complex.exp ((↑(-2 * Real.pi * inner ℝ y (Lattice.toEuc k)) * Complex.I)) := by
  rw [Torus.mode_mk]
  congr 2
  have : Lattice.dot (-k) y = -inner ℝ y (Lattice.toEuc k) := by
    simp only [Lattice.dot, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, neg_inj]
    simp [PiLp.inner_apply, Lattice.toEuc, mul_comm]
  rw [this]
  push_cast
  ring

lemma tpos_mode_mk_add (k : Lattice d) (y : Euc d) (m : Lattice d) :
    Torus.mode k (Torus.mk (y + Lattice.toEuc m)) = Torus.mode k (Torus.mk y) := by
  rw [Torus.mk_add, Torus.mk_toEuc, add_zero]

lemma tpos_fcoef_perio {f : Euc d → ℝ} (hf : Measurable f) (hint : Integrable f)
    (hsum : ∀ y, Summable fun m : Lattice d => f (y + Lattice.toEuc m)) (k : Lattice d) :
    Torus.fcoef (perio f : Torus d → ℝ) k = 𝓕 (fun y : Euc d => ((f y : ℝ) : ℂ)) (Lattice.toEuc k) := by
  unfold Torus.fcoef
  rw [tpos_torus_integral]
  set F : Euc d → ℂ := fun y => Torus.mode (-k) (Torus.mk y) * ((f y : ℝ) : ℂ) with hF
  have hFint : Integrable F := by
    have hc : Continuous (fun y : Euc d => Torus.mode (-k) (Torus.mk y)) :=
      (Torus.continuous_mode (-k)).comp Torus.continuous_mk
    exact hint.ofReal.bdd_mul hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => (Torus.norm_mode (-k) _).le)
  have h1 : ∀ y : Euc d, Torus.mode (-k) (Torus.mk y) * ((perio f (Torus.mk y) : ℝ) : ℂ) =
      ∑' m : Lattice d, F (y + Lattice.toEuc m) := by
    intro y
    rw [tpos_perio_mk, Complex.ofReal_tsum, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    simp only [hF, tpos_mode_mk_add]
  simp_rw [h1]
  rw [← tpos_integral_unfold hFint, Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hF, smul_eq_mul, tpos_mode_mk_neg]

end HRS.Commutator.TorusNote
