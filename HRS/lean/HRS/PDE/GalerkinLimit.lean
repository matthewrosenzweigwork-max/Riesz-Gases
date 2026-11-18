import HRS.PDE.ForwardEq
import HRS.PDE.Compactness
import HRS.PDE.TorusCalculus
import HRS.PDE.HsAnalysis

/-!
# Passage to the limit in the Fourier–Galerkin scheme (Proposition 3.9, Steps 3–4)

Helper file for `galerkin_limit` in `HRS/PDE/WellPosed.lean`: uniform `ℓ²` bounds on the
coefficients of the drift and of the density, the bound of a single coefficient of the forward
generator by the `H¹` norm of its argument, weak convergence of the generator under coordinatewise
convergence with uniform `H¹` bounds, continuity in time of the coefficients of `μ`, and the
continuity of the Galerkin integrand.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-! ### Parseval bounds for bounded functions and their derivatives -/

lemma memHs_zero_coeffOf_le (φ : Torus d → ℝ) (hφ : Continuous φ) (B : ℝ)
    (hB : ∀ x, |φ x| ≤ B) :
    MemHs 0 (coeffOf φ) ∧ hsNormSq 0 (coeffOf φ) ≤ B ^ 2 := by
  set P : Measure (Torus d) := Measure.pi fun _ : Fin d =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle) with hP
  have : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hH : MemLp (fun x => (φ x : ℂ)) 2 P :=
    MemLp.of_bound (Complex.continuous_ofReal.comp hφ).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by simpa using hB x)
  set f := hH.toLp (fun x => (φ x : ℂ)) with hf
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff (d := Fin d) f
  have e1 : ∀ n : Lattice d, UnitAddTorus.mFourierCoeff f n = coeffOf φ n := by
    intro n
    unfold UnitAddTorus.mFourierCoeff coeffOf Torus.funFourierCoeff UnitAddTorus.mFourierCoeff
    refine integral_congr_ae ?_
    filter_upwards [hH.coeFn_toLp] with x hx
    rw [hx]
  have e2 : ∫ t : Torus d, ‖f t‖ ^ 2 ∂P ≤ B ^ 2 := by
    have h1 : ∫ t : Torus d, ‖f t‖ ^ 2 ∂P = ∫ t : Torus d, ‖(φ t : ℂ)‖ ^ 2 ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hH.coeFn_toLp] with x hx
      rw [hx]
    rw [h1]
    refine (le_abs_self _).trans ?_
    have := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun t => ‖(φ t : ℂ)‖ ^ 2) (C := B ^ 2)
      (Filter.Eventually.of_forall fun t => by
        have : ‖(φ t : ℂ)‖ = |φ t| := by simp
        rw [Real.norm_eq_abs, abs_pow, this, abs_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hB t) 2)
    simpa using this
  have h' : HasSum (fun n : Lattice d => ‖coeffOf φ n‖ ^ 2) (∫ t : Torus d, ‖f t‖ ^ 2 ∂P) := by
    convert h using 1
    funext n
    rw [e1 n]
  have hs : MemHs 0 (coeffOf φ) := by
    refine h'.summable.congr fun k => ?_
    rw [sobWeight_zero, one_mul]
  refine ⟨hs, ?_⟩
  have : hsNormSq 0 (coeffOf φ) = ∫ t : Torus d, ‖f t‖ ^ 2 ∂P := by
    rw [← h'.tsum_eq]
    unfold hsNormSq
    exact tsum_congr fun k => by rw [sobWeight_zero, one_mul]
  rw [this]; exact e2

lemma sq_enorm_eq_sum (k : Lattice d) :
    Lattice.enorm k ^ 2 = ∑ j, ((k j : ℤ) : ℝ) ^ 2 := by
  unfold Lattice.enorm
  rw [EuclideanSpace.norm_sq_eq]
  simp [Lattice.toEuc]

lemma abs_coord_le_enorm (k : Lattice d) (j : Fin d) : |((k j : ℤ) : ℝ)| ≤ Lattice.enorm k := by
  have := PiLp.norm_apply_le (Lattice.toEuc k) j
  simpa [Lattice.toEuc, Lattice.enorm] using this

lemma norm_derivCoeff (j : Fin d) (c : Coeff d) (k : Lattice d) :
    ‖derivCoeff j c k‖ = 2 * Real.pi * |((k j : ℤ) : ℝ)| * ‖c k‖ := by
  simp only [derivCoeff, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast,
    Real.norm_eq_abs, Complex.norm_ofNat, mul_one]
  rw [abs_of_pos Real.pi_pos]

lemma sobWeight_one_eq_sum (k : Lattice d) :
    sobWeight 1 k = 1 + ∑ j, (2 * Real.pi * ((k j : ℤ) : ℝ)) ^ 2 := by
  rw [sobWeight_one, sq_enorm_eq_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => by ring

/-- `H¹` bound of the coefficients of a `C¹` function in terms of the sup norms of the function and
its partial derivatives (Parseval for `φ` and each `∂_jφ`). -/
lemma memHs_one_coeffOf_le (φ : Torus d → ℝ) (hφ : Torus.IsCk 1 φ) (B : ℝ)
    (hB : ∀ x, |φ x| ≤ B) (hB1 : ∀ j x, |Torus.partialDeriv j φ x| ≤ B) :
    MemHs 1 (coeffOf φ) ∧ hsNormSq 1 (coeffOf φ) ≤ (1 + d) * B ^ 2 := by
  have hc : Continuous φ := Torus.continuous_of_continuous_lift hφ.continuous
  obtain ⟨-, h0⟩ := memHs_zero_coeffOf_le φ hc B hB
  have h0' : Summable fun k => ‖coeffOf φ k‖ ^ 2 :=
    (memHs_zero_coeffOf_le φ hc B hB).1.congr fun k => by rw [sobWeight_zero, one_mul]
  have hj : ∀ j, Summable (fun k => ‖derivCoeff j (coeffOf φ) k‖ ^ 2) ∧
      ∑' k, ‖derivCoeff j (coeffOf φ) k‖ ^ 2 ≤ B ^ 2 := by
    intro j
    have hcoef : coeffOf (Torus.partialDeriv j φ) = derivCoeff j (coeffOf φ) := by
      funext k
      exact funFourierCoeff_partialDeriv j φ hφ k
    have := memHs_zero_coeffOf_le (Torus.partialDeriv j φ) (continuous_partialDeriv j φ hφ) B
      (hB1 j)
    rw [hcoef] at this
    refine ⟨this.1.congr fun k => by rw [sobWeight_zero, one_mul], ?_⟩
    have h2 := this.2
    unfold hsNormSq at h2
    simpa [sobWeight_zero] using h2
  have hpt : ∀ k, sobWeight 1 k * ‖coeffOf φ k‖ ^ 2 =
      ‖coeffOf φ k‖ ^ 2 + ∑ j, ‖derivCoeff j (coeffOf φ) k‖ ^ 2 := by
    intro k
    rw [sobWeight_one_eq_sum, add_mul, one_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_derivCoeff]
    have := sq_abs (((k j : ℤ) : ℝ))
    calc (2 * Real.pi * ((k j : ℤ) : ℝ)) ^ 2 * ‖coeffOf φ k‖ ^ 2
        = (2 * Real.pi) ^ 2 * (((k j : ℤ) : ℝ)) ^ 2 * ‖coeffOf φ k‖ ^ 2 := by ring
      _ = _ := by rw [← this]; ring
  refine memHs_of_sum_le (fun S => ?_)
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have e1 : ∑ k ∈ S, ‖coeffOf φ k‖ ^ 2 ≤ B ^ 2 :=
    (h0'.sum_le_tsum S fun k _ => sq_nonneg _).trans (by simpa [hsNormSq, sobWeight_zero] using h0)
  have e2 : ∀ j, ∑ k ∈ S, ‖derivCoeff j (coeffOf φ) k‖ ^ 2 ≤ B ^ 2 := fun j =>
    ((hj j).1.sum_le_tsum S fun k _ => sq_nonneg _).trans (hj j).2
  calc _ ≤ B ^ 2 + ∑ j : Fin d, B ^ 2 := add_le_add e1 (Finset.sum_le_sum fun j _ => e2 j)
    _ = (1 + d) * B ^ 2 := by simp; ring


/-! ### Sup-norm bounds from `cbNorm` -/

lemma norm_iteratedFDeriv_le_cbNorm (k j : ℕ) (hj : j ≤ k) (φ : Torus d → ℝ)
    (hφ : Torus.IsCk (k : WithTop ℕ∞) φ) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ ≤ Torus.cbNorm k φ := by
  have hj' : ContDiff ℝ (j : WithTop ℕ∞) (Torus.lift φ) :=
    hφ.of_le (by exact_mod_cast hj)
  have hb := Torus.bddAbove_norm_iteratedFDeriv_lift j φ hj'
  unfold Torus.cbNorm
  refine le_trans ?_ (Finset.single_le_sum (f := fun j => ⨆ x : Euc d,
    ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖) (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  exact le_ciSup hb x

lemma abs_le_cbNorm (k : ℕ) (φ : Torus d → ℝ) (hφ : Torus.IsCk (k : WithTop ℕ∞) φ) (x : Torus d) :
    |φ x| ≤ Torus.cbNorm k φ := by
  have := norm_iteratedFDeriv_le_cbNorm k 0 (Nat.zero_le _) φ hφ (Torus.rep x)
  rw [norm_iteratedFDeriv_zero] at this
  simpa [Torus.lift, Torus.mk_rep] using this

lemma abs_partialDeriv_le_cbNorm (k : ℕ) (hk : 1 ≤ k) (φ : Torus d → ℝ)
    (hφ : Torus.IsCk (k : WithTop ℕ∞) φ) (j : Fin d) (x : Torus d) :
    |Torus.partialDeriv j φ x| ≤ Torus.cbNorm k φ := by
  have h1 := norm_iteratedFDeriv_le_cbNorm k 1 hk φ hφ (Torus.rep x)
  rw [norm_iteratedFDeriv_one] at h1
  have h2 : |Torus.partialDeriv j φ x| ≤ ‖fderiv ℝ (Torus.lift φ) (Torus.rep x)‖ := by
    unfold Torus.partialDeriv
    have := (fderiv ℝ (Torus.lift φ) (Torus.rep x)).le_opNorm (EuclideanSpace.single j (1 : ℝ))
    simpa [PiLp.norm_single] using this
  exact h2.trans h1

/-- `H¹` bound of the coefficients of a `C^k` function (`k ≥ 1`) by its `cbNorm`. -/
lemma memHs_one_coeffOf_cbNorm (k : ℕ) (hk : 1 ≤ k) (φ : Torus d → ℝ)
    (hφ : Torus.IsCk (k : WithTop ℕ∞) φ) :
    MemHs 1 (coeffOf φ) ∧ hsNormSq 1 (coeffOf φ) ≤ (1 + d) * Torus.cbNorm k φ ^ 2 :=
  memHs_one_coeffOf_le φ (hφ.of_le (by exact_mod_cast hk)) _ (abs_le_cbNorm k φ hφ)
    (abs_partialDeriv_le_cbNorm k hk φ hφ)


/-! ### `ℓ²` bound for the drift coefficients -/

lemma one_le_enorm_of_ne_zero {k : Lattice d} (hk : k ≠ 0) : 1 ≤ Lattice.enorm k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  have h1 : (1 : ℝ) ≤ |((k i : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
    rw [← Int.cast_abs]; exact_mod_cast this
  exact h1.trans (abs_coord_le_enorm k i)

lemma two_pi_abs_coord_le_jp (k : Lattice d) (i : Fin d) :
    2 * Real.pi * |((k i : ℤ) : ℝ)| ≤ Lattice.jp k :=
  (mul_le_mul_of_nonneg_left (abs_coord_le_enorm k i) (by positivity)).trans
    (Torus.two_pi_enorm_le_jp k)

lemma abs_rieszCoeff_mul_le (s : ℝ) (hsd : s ≤ d) (k : Lattice d) (i : Fin d) :
    |rieszCoeff d s k| * (2 * Real.pi * |((k i : ℤ) : ℝ)|) ≤ |rieszConst d s| * Lattice.jp k := by
  by_cases hk : k = 0
  · subst hk
    simp [rieszCoeff]
    exact mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  · have he := one_le_enorm_of_ne_zero hk
    have hx : 1 ≤ 2 * Real.pi * Lattice.enorm k := by nlinarith [Real.pi_gt_three]
    have hx0 : 0 < 2 * Real.pi * Lattice.enorm k := by linarith
    have h1 : |rieszCoeff d s k| = |rieszConst d s| * (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ)) := by
      simp only [rieszCoeff, hk, ite_false, abs_mul]
      rw [abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have h2 : 2 * Real.pi * |((k i : ℤ) : ℝ)| ≤ 2 * Real.pi * Lattice.enorm k :=
      mul_le_mul_of_nonneg_left (abs_coord_le_enorm k i) (by positivity)
    have h3 : (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ)) * (2 * Real.pi * Lattice.enorm k) ≤
        2 * Real.pi * Lattice.enorm k := by
      have : (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ)) * (2 * Real.pi * Lattice.enorm k) =
          (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ) + 1) := by
        rw [Real.rpow_add_one hx0.ne']
      rw [this]
      calc _ ≤ (2 * Real.pi * Lattice.enorm k) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx (by linarith)
        _ = _ := Real.rpow_one _
    rw [h1]
    calc |rieszConst d s| * (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ)) *
          (2 * Real.pi * |((k i : ℤ) : ℝ)|)
        ≤ |rieszConst d s| * (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ)) *
          (2 * Real.pi * Lattice.enorm k) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hx0.le _))
      _ = |rieszConst d s| * ((2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ)) *
          (2 * Real.pi * Lattice.enorm k)) := by ring
      _ ≤ |rieszConst d s| * (2 * Real.pi * Lattice.enorm k) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ ≤ |rieszConst d s| * Lattice.jp k :=
          mul_le_mul_of_nonneg_left (Torus.two_pi_enorm_le_jp k) (abs_nonneg _)

lemma norm_gradRieszCoeff (s : ℝ) (i : Fin d) (c : Coeff d) (k : Lattice d) :
    ‖gradRieszCoeff d s i c k‖ =
      2 * Real.pi * |((k i : ℤ) : ℝ)| * (|rieszCoeff d s k| * ‖c k‖) := by
  unfold gradRieszCoeff
  rw [norm_derivCoeff]
  simp [rieszMult]

lemma jp_sq (k : Lattice d) : Lattice.jp k ^ 2 = sobWeight 1 k := by
  rw [sobWeight_one]
  unfold Lattice.jp
  exact Real.sq_sqrt (by have := one_le_sobBase k; linarith)

/-- Pointwise bound of the drift coefficients. -/
lemma norm_driftCoeff_le (D : DynData d) (ρ : Torus d → ℝ) (j : Fin d) (k : Lattice d) :
    ‖driftCoeff D ρ j k‖ ≤ Lattice.jp k *
      ((|rieszConst d D.s| * ∑ i, |D.M j i|) * ‖coeffOf ρ k‖ + ‖coeffOf D.V k‖) := by
  have hsd : D.s ≤ d := D.hsd.le
  unfold driftCoeff
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖∑ i : Fin d, ((D.M j i : ℝ) : ℂ) * gradRieszCoeff d D.s i (coeffOf ρ) k‖ ≤
      Lattice.jp k * ((|rieszConst d D.s| * ∑ i, |D.M j i|) * ‖coeffOf ρ k‖) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : Fin d, ‖((D.M j i : ℝ) : ℂ) * gradRieszCoeff d D.s i (coeffOf ρ) k‖
        ≤ ∑ i : Fin d, |D.M j i| * (|rieszConst d D.s| * Lattice.jp k * ‖coeffOf ρ k‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_gradRieszCoeff]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have := abs_rieszCoeff_mul_le D.s hsd k i
          calc 2 * Real.pi * |((k i : ℤ) : ℝ)| * (|rieszCoeff d D.s k| * ‖coeffOf ρ k‖)
              = (|rieszCoeff d D.s k| * (2 * Real.pi * |((k i : ℤ) : ℝ)|)) * ‖coeffOf ρ k‖ := by
                ring
            _ ≤ (|rieszConst d D.s| * Lattice.jp k) * ‖coeffOf ρ k‖ :=
                mul_le_mul_of_nonneg_right this (norm_nonneg _)
            _ = _ := by ring
      _ = Lattice.jp k * ((|rieszConst d D.s| * ∑ i, |D.M j i|) * ‖coeffOf ρ k‖) := by
          rw [← Finset.sum_mul]
          ring
  have h2 : ‖derivCoeff j (coeffOf D.V) k‖ ≤ Lattice.jp k * ‖coeffOf D.V k‖ := by
    rw [norm_derivCoeff]
    exact mul_le_mul_of_nonneg_right (two_pi_abs_coord_le_jp k j) (norm_nonneg _)
  calc _ ≤ Lattice.jp k * ((|rieszConst d D.s| * ∑ i, |D.M j i|) * ‖coeffOf ρ k‖) +
        Lattice.jp k * ‖coeffOf D.V k‖ := add_le_add h1 h2
    _ = _ := by ring


lemma driftCoeff_memHs0 (D : DynData d) (ρ : Torus d → ℝ) (hρ : MemHs 1 (coeffOf ρ))
    (hV : MemHs 1 (coeffOf D.V)) (j : Fin d) :
    MemHs 0 (driftCoeff D ρ j) ∧ hsNormSq 0 (driftCoeff D ρ j) ≤
      2 * ((|rieszConst d D.s| * ∑ i, |D.M j i|) ^ 2 * hsNormSq 1 (coeffOf ρ) +
        hsNormSq 1 (coeffOf D.V)) := by
  set a : ℝ := |rieszConst d D.s| * ∑ i, |D.M j i| with ha
  have hpt : ∀ k, sobWeight 0 k * ‖driftCoeff D ρ j k‖ ^ 2 ≤
      2 * (a ^ 2 * (sobWeight 1 k * ‖coeffOf ρ k‖ ^ 2) + sobWeight 1 k * ‖coeffOf D.V k‖ ^ 2) := by
    intro k
    rw [sobWeight_zero, one_mul]
    have h := norm_driftCoeff_le D ρ j k
    have hn := norm_nonneg (driftCoeff D ρ j k)
    have h2 : ‖driftCoeff D ρ j k‖ ^ 2 ≤ (Lattice.jp k *
        (a * ‖coeffOf ρ k‖ + ‖coeffOf D.V k‖)) ^ 2 := pow_le_pow_left₀ hn h 2
    refine h2.trans ?_
    rw [mul_pow, jp_sq]
    have hw := (sobWeight_pos (d := d) 1 k).le
    have : (a * ‖coeffOf ρ k‖ + ‖coeffOf D.V k‖) ^ 2 ≤
        2 * (a ^ 2 * ‖coeffOf ρ k‖ ^ 2 + ‖coeffOf D.V k‖ ^ 2) := by
      nlinarith [sq_nonneg (a * ‖coeffOf ρ k‖ - ‖coeffOf D.V k‖)]
    nlinarith [mul_le_mul_of_nonneg_left this hw]
  have hS : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight 0 k * ‖driftCoeff D ρ j k‖ ^ 2 ≤
      2 * (a ^ 2 * hsNormSq 1 (coeffOf ρ) + hsNormSq 1 (coeffOf D.V)) := by
    intro S
    calc _ ≤ ∑ k ∈ S, 2 * (a ^ 2 * (sobWeight 1 k * ‖coeffOf ρ k‖ ^ 2) +
          sobWeight 1 k * ‖coeffOf D.V k‖ ^ 2) := Finset.sum_le_sum fun k _ => hpt k
      _ = 2 * (a ^ 2 * ∑ k ∈ S, sobWeight 1 k * ‖coeffOf ρ k‖ ^ 2 +
          ∑ k ∈ S, sobWeight 1 k * ‖coeffOf D.V k‖ ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ _ := by
          have h1 := sum_le_hsNormSq hρ S
          have h2 := sum_le_hsNormSq hV S
          have : 0 ≤ a ^ 2 := sq_nonneg _
          nlinarith [mul_le_mul_of_nonneg_left h1 this]
  exact memHs_of_sum_le hS

/-! ### Convolution estimates and the bound of a coefficient of the generator -/

lemma summable_sq_subLeft {a : Coeff d} (ha : MemHs 0 a) (k : Lattice d) :
    Summable (fun l => ‖a (k - l)‖ ^ 2) ∧ ∑' l, ‖a (k - l)‖ ^ 2 = hsNormSq 0 a := by
  have h : Summable (fun l => ‖a l‖ ^ 2) := ha.congr fun l => by rw [sobWeight_zero, one_mul]
  refine ⟨(Equiv.subLeft k).summable_iff.mpr h, ?_⟩
  unfold hsNormSq
  rw [← (Equiv.subLeft k).tsum_eq (fun l => sobWeight 0 l * ‖a l‖ ^ 2)]
  exact tsum_congr fun l => by simp [sobWeight_zero]

lemma norm_derivCoeff_sq_le (j : Fin d) (c : Coeff d) (l : Lattice d) :
    ‖derivCoeff j c l‖ ^ 2 ≤ sobWeight 1 l * ‖c l‖ ^ 2 := by
  rw [norm_derivCoeff, mul_pow, ← jp_sq]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) (two_pi_abs_coord_le_jp l j) 2) (sq_nonneg _)

lemma mulCoeff_deriv_bound {a c : Coeff d} (ha : MemHs 0 a) (hc : MemHs 1 c) (j : Fin d)
    (k : Lattice d) :
    ‖mulCoeff a (derivCoeff j c) k‖ ≤ Real.sqrt (hsNormSq 0 a) * Real.sqrt (hsNormSq 1 c) := by
  obtain ⟨hs, htsum⟩ := summable_sq_subLeft ha k
  have := (norm_tsum_mul_le_split (fun l => a (k - l)) (derivCoeff j c) ∅
    (Real.sqrt (hsNormSq 0 a)) (Real.sqrt (hsNormSq 1 c)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (fun T => by
      rw [Real.sq_sqrt (hsNormSq_nonneg _ _), ← htsum]
      exact hs.sum_le_tsum T fun l _ => sq_nonneg _)
    (fun T _ => by
      rw [Real.sq_sqrt (hsNormSq_nonneg _ _)]
      refine le_trans (Finset.sum_le_sum fun l _ => norm_derivCoeff_sq_le j c l) ?_
      exact sum_le_hsNormSq hc T)).2
  simpa [mulCoeff] using this

lemma norm_le_sqrt_hsNormSq_one {F : Coeff d} (hF : MemHs 1 F) (k : Lattice d) :
    ‖F k‖ ≤ Real.sqrt (hsNormSq 1 F) := by
  refine Real.le_sqrt_of_sq_le ?_
  have h1 := sobWeight_mul_sq_le_hsNormSq hF k
  have h2 : 1 ≤ sobWeight (d := d) 1 k := by rw [sobWeight_one]; exact one_le_sobBase k
  nlinarith [sq_nonneg ‖F k‖]

/-- The bound for a single coefficient of the forward generator. -/
def genBound (D : DynData d) (K : ℝ) (k : Lattice d) : ℝ :=
  |D.invβ| * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) + d * Real.sqrt K +
    (∑ i, ∑ j, |D.M j i|) * (2 * Real.pi * Lattice.enorm k * |rieszCoeff d D.s k|) * Real.sqrt K

lemma norm_forwardGen_le (D : DynData d) (ρ : Torus d → ℝ) (K : ℝ)
    (hρ0 : MemHs 0 (coeffOf ρ)) (hρK : hsNormSq 0 (coeffOf ρ) ≤ K)
    (hb : ∀ j, MemHs 0 (driftCoeff D ρ j)) (hbK : ∀ j, hsNormSq 0 (driftCoeff D ρ j) ≤ K)
    (F : Coeff d) (hF : MemHs 1 F) (k : Lattice d) :
    ‖forwardGen D ρ F k‖ ≤ genBound D K k * Real.sqrt (hsNormSq 1 F) := by
  set H := Real.sqrt (hsNormSq 1 F) with hH
  have hH0 : 0 ≤ H := Real.sqrt_nonneg _
  unfold forwardGen
  refine (norm_sub_le _ _).trans ?_
  have hlap : ‖((D.invβ : ℝ) : ℂ) * laplaceCoeff F k‖ ≤
      |D.invβ| * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * H := by
    have hl : ‖laplaceCoeff F k‖ = 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 * ‖F k‖ := by
      unfold laplaceCoeff
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    have hc : 0 ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hl]
    calc |D.invβ| * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 * ‖F k‖)
        ≤ |D.invβ| * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 * H) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (norm_le_sqrt_hsNormSq_one hF k) hc) (abs_nonneg _)
      _ = _ := by ring
  have htr : ‖transportCoeff D ρ F k‖ ≤ d * Real.sqrt K * H := by
    unfold transportCoeff
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j : Fin d, ‖mulCoeff (driftCoeff D ρ j) (derivCoeff j F) k‖
        ≤ ∑ j : Fin d, Real.sqrt K * H := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine (mulCoeff_deriv_bound (hb j) hF j k).trans ?_
          exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hbK j)) hH0
      _ = d * Real.sqrt K * H := by simp [mul_assoc]
  have hnl : ‖nonlocalCoeff D ρ F k‖ ≤
      (∑ i, ∑ j, |D.M j i|) * (2 * Real.pi * Lattice.enorm k * |rieszCoeff d D.s k|) *
        Real.sqrt K * H := by
    unfold nonlocalCoeff
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i j : Fin d, ‖((D.M j i : ℝ) : ℂ) *
        gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j F)) k‖ ≤
        |D.M j i| * (2 * Real.pi * Lattice.enorm k * |rieszCoeff d D.s k|) *
          (Real.sqrt K * H) := by
      intro i j
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_gradRieszCoeff]
      have hX := (mulCoeff_deriv_bound hρ0 hF j k).trans
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hρK) hH0)
      have hg : 2 * Real.pi * |((k i : ℤ) : ℝ)| ≤ 2 * Real.pi * Lattice.enorm k :=
        mul_le_mul_of_nonneg_left (abs_coord_le_enorm k i) (by positivity)
      have hg0 : 0 ≤ |rieszCoeff d D.s k| := abs_nonneg _
      calc |D.M j i| * (2 * Real.pi * |((k i : ℤ) : ℝ)| *
            (|rieszCoeff d D.s k| * ‖mulCoeff (coeffOf ρ) (derivCoeff j F) k‖))
          ≤ |D.M j i| * (2 * Real.pi * Lattice.enorm k *
            (|rieszCoeff d D.s k| * (Real.sqrt K * H))) := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact mul_le_mul hg (mul_le_mul_of_nonneg_left hX hg0) (mul_nonneg hg0 (norm_nonneg _))
              (mul_nonneg (by positivity) (norm_nonneg _))
        _ = _ := by ring
    calc ∑ i : Fin d, ‖∑ j : Fin d, ((D.M j i : ℝ) : ℂ) *
          gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j F)) k‖
        ≤ ∑ i : Fin d, ∑ j : Fin d, |D.M j i| *
            (2 * Real.pi * Lattice.enorm k * |rieszCoeff d D.s k|) * (Real.sqrt K * H) :=
          Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun j _ => hterm i j)
      _ = _ := by
          simp_rw [← Finset.sum_mul]
          ring
  unfold genBound
  calc _ ≤ (‖((D.invβ : ℝ) : ℂ) * laplaceCoeff F k‖ + ‖transportCoeff D ρ F k‖) +
        ‖nonlocalCoeff D ρ F k‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := by nlinarith [hlap, htr, hnl]


/-! ### Weak convergence of the generator -/

lemma sqrt_sobWeight_one (k : Lattice d) : Real.sqrt (sobWeight 1 k) = Lattice.jp k := by
  rw [sobWeight_one]; rfl

lemma tendsto_mulCoeff_deriv {α : Type*} {l : Filter α} [l.NeBot] {a : Coeff d} (ha : MemHs 0 a)
    (Fa : α → Coeff d) (G : Coeff d) (B : ℝ) (hB0 : 0 ≤ B)
    (hbd : ∀ᶠ x in l, ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight 1 k * ‖Fa x k‖ ^ 2 ≤ B ^ 2)
    (hc : ∀ k, Tendsto (fun x => Fa x k) l (𝓝 (G k))) (j : Fin d) (k : Lattice d) :
    Tendsto (fun x => mulCoeff a (derivCoeff j (Fa x)) k) l
      (𝓝 (mulCoeff a (derivCoeff j G) k)) := by
  set v : Lattice d → ℂ := fun q => a (k - q) *
    (2 * Real.pi * Complex.I * ((q j : ℤ) : ℂ)) * (((Lattice.jp q : ℝ) : ℂ))⁻¹ with hv
  have hjp : ∀ q : Lattice d, ((Lattice.jp q : ℝ) : ℂ) ≠ 0 := fun q => by
    exact_mod_cast (Torus.jp_pos q).ne'
  have hvsq : Summable fun q => ‖v q‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_)
      (summable_sq_subLeft ha k).1
    have hn : ‖v q‖ = ‖a (k - q)‖ * (2 * Real.pi * |((q j : ℤ) : ℝ)| / Lattice.jp q) := by
      have h2 : ‖(2 * (Real.pi : ℂ) * Complex.I * ((q j : ℤ) : ℂ))‖ =
          2 * Real.pi * |((q j : ℤ) : ℝ)| := by
        have := norm_derivCoeff j (fun _ => (1 : ℂ)) q
        simpa using this
      show ‖a (k - q) * (2 * (Real.pi : ℂ) * Complex.I * ((q j : ℤ) : ℂ)) *
        (((Lattice.jp q : ℝ) : ℂ))⁻¹‖ = _
      rw [norm_mul, norm_mul, h2, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Torus.jp_pos q)]
      ring
    have hle : 2 * Real.pi * |((q j : ℤ) : ℝ)| / Lattice.jp q ≤ 1 :=
      (div_le_one (Torus.jp_pos q)).mpr (two_pi_abs_coord_le_jp q j)
    rw [hn, mul_pow]
    have h0 : 0 ≤ 2 * Real.pi * |((q j : ℤ) : ℝ)| / Lattice.jp q :=
      div_nonneg (by positivity) (Torus.jp_pos q).le
    calc ‖a (k - q)‖ ^ 2 * (2 * Real.pi * |((q j : ℤ) : ℝ)| / Lattice.jp q) ^ 2
        ≤ ‖a (k - q)‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ h0 hle) (sq_nonneg _)
      _ = _ := mul_one _
  have hprod : ∀ F : Coeff d, ∀ q, wseq 1 F q * v q = a (k - q) * derivCoeff j F q := by
    intro F q
    have hs : (Real.sqrt (sobWeight 1 q) : ℂ) = ((Lattice.jp q : ℝ) : ℂ) := by
      rw [sqrt_sobWeight_one]
    simp only [wseq, hv, derivCoeff, hs]
    field_simp [hjp q]
  have key := tendsto_tsum_mul (l := l) (fun x => wseq 1 (Fa x)) (wseq 1 G) v B hB0 ?_ hvsq ?_
  · simp only [hprod] at key
    exact key
  · filter_upwards [hbd] with x hx S
    calc ∑ q ∈ S, ‖wseq 1 (Fa x) q‖ ^ 2 = ∑ q ∈ S, sobWeight 1 q * ‖Fa x q‖ ^ 2 :=
          Finset.sum_congr rfl fun q _ => norm_wseq_sq 1 _ q
      _ ≤ B ^ 2 := hx S
  · intro q
    simp only [wseq]
    exact (hc q).const_mul _

lemma tendsto_forwardGen {α : Type*} {l : Filter α} [l.NeBot] (D : DynData d) (ρ : Torus d → ℝ)
    (hρ0 : MemHs 0 (coeffOf ρ)) (hb : ∀ j, MemHs 0 (driftCoeff D ρ j))
    (Fa : α → Coeff d) (G : Coeff d) (B : ℝ) (hB0 : 0 ≤ B)
    (hbd : ∀ᶠ x in l, ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight 1 k * ‖Fa x k‖ ^ 2 ≤ B ^ 2)
    (hc : ∀ k, Tendsto (fun x => Fa x k) l (𝓝 (G k))) (k : Lattice d) :
    Tendsto (fun x => forwardGen D ρ (Fa x) k) l (𝓝 (forwardGen D ρ G k)) := by
  unfold forwardGen
  refine Tendsto.sub (Tendsto.add ?_ ?_) ?_
  · simp only [laplaceCoeff]
    exact ((hc k).const_mul _).const_mul _
  · unfold transportCoeff
    exact tendsto_finsetSum _ fun j _ => tendsto_mulCoeff_deriv (hb j) Fa G B hB0 hbd hc j k
  · unfold nonlocalCoeff
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    have := tendsto_mulCoeff_deriv hρ0 Fa G B hB0 hbd hc j k
    simp only [gradRieszCoeff, derivCoeff, rieszMult]
    exact (this.const_mul _).const_mul _ |>.const_mul _


/-! ### Continuity in time of the Fourier coefficients of the density path -/

private lemma funFourierCoeff_eq' (f : Torus d → ℂ) (k : Lattice d) :
    Torus.funFourierCoeff f k = ∫ x, UnitAddTorus.mFourier (-k) x * f x := by
  unfold Torus.funFourierCoeff UnitAddTorus.mFourierCoeff
  have hm : (@volume (UnitAddTorus (Fin d))
      (@MeasureSpace.pi (Fin d) _ (fun _ => UnitAddCircle) fun _ => instMeasureSpaceUnitAddCircle)) =
      (volume : Measure (Torus d)) := by
    show Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) =
      Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))
    congr 1
    funext i
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [hm]
  simp [smul_eq_mul]

lemma continuousOn_coeffOf_family {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hc : ∀ r ∈ Set.Icc 0 T, Continuous (ρ r))
    (hcont : ∀ ψ : Torus d → ℝ, Continuous ψ →
      ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Set.Icc 0 T)) (k : Lattice d) :
    ContinuousOn (fun r => coeffOf (ρ r) k) (Set.Icc 0 T) := by
  have hm : Continuous (fun x : Torus d => UnitAddTorus.mFourier (-k) x) :=
    (UnitAddTorus.mFourier (-k)).continuous
  have hre : Continuous (fun x : Torus d => (UnitAddTorus.mFourier (-k) x).re) :=
    Complex.continuous_re.comp hm
  have him : Continuous (fun x : Torus d => (UnitAddTorus.mFourier (-k) x).im) :=
    Complex.continuous_im.comp hm
  have e : ∀ r ∈ Set.Icc 0 T, coeffOf (ρ r) k =
      ((∫ x, (UnitAddTorus.mFourier (-k) x).re * ρ r x : ℝ) : ℂ) +
        ((∫ x, (UnitAddTorus.mFourier (-k) x).im * ρ r x : ℝ) : ℂ) * Complex.I := by
    intro r hr
    unfold coeffOf
    rw [funFourierCoeff_eq']
    have hcr : Continuous (fun x : Torus d => ((ρ r x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hc r hr)
    have hint : Integrable (fun x : Torus d => UnitAddTorus.mFourier (-k) x * ((ρ r x : ℝ) : ℂ)) :=
      (hm.mul hcr).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have := integral_re_add_im (𝕜 := ℂ) hint
    simp only [RCLike.re_to_complex, RCLike.im_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im, zero_add, RCLike.I_to_complex] at this
    rw [← this]
    simp [mul_comm]
  refine ContinuousOn.congr ?_ e
  exact (Complex.continuous_ofReal.comp_continuousOn (hcont _ hre)).add
    ((Complex.continuous_ofReal.comp_continuousOn (hcont _ him)).mul continuousOn_const)


/-! ### Trigonometric polynomials and continuity of the Galerkin integrand -/

lemma finite_inBox (n : ℕ) : {k : Lattice d | InBox n k}.Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin d => Set.Icc (-(n : ℤ)) n)
    (fun _ => Set.finite_Icc _ _)).subset ?_
  intro k hk i _
  exact abs_le.mp (hk i)

/-- The box `{|k|_∞ ≤ n}` as a finset. -/
def boxFinsetL (n : ℕ) : Finset (Lattice d) := (finite_inBox (d := d) n).toFinset

lemma mem_boxFinsetL {n : ℕ} {k : Lattice d} : k ∈ boxFinsetL n ↔ InBox n k := by
  unfold boxFinsetL
  rw [Set.Finite.mem_toFinset]; rfl

lemma memHs_of_isTrigPoly {n : ℕ} {c : Coeff d} (h : IsTrigPoly n c) (m : ℝ) : MemHs m c := by
  refine summable_of_ne_finset_zero (s := boxFinsetL n) fun k hk => ?_
  have : c k = 0 := by
    by_contra hne
    exact hk (mem_boxFinsetL.mpr (h k hne))
  simp [this]

lemma truncCoeff_of_isTrigPoly {n : ℕ} {c : Coeff d} (h : IsTrigPoly n c) :
    truncCoeff n c = c := by
  funext k
  unfold truncCoeff
  split_ifs with hk
  · rfl
  · by_contra hne
    exact hk (h k (Ne.symm hne))

lemma mulCoeff_trig {n : ℕ} (a c : Coeff d) (h : IsTrigPoly n c) (j : Fin d) (k : Lattice d) :
    mulCoeff a (derivCoeff j c) k = ∑ l ∈ boxFinsetL n, a (k - l) * derivCoeff j c l := by
  unfold mulCoeff
  refine tsum_eq_sum fun l hl => ?_
  have : c l = 0 := by
    by_contra hne
    exact hl (mem_boxFinsetL.mpr (h l hne))
  simp [derivCoeff, this]

lemma continuousOn_drift {S : Set ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ q, ContinuousOn (fun σ => coeffOf (ρ σ) q) S) (j : Fin d) (q : Lattice d) :
    ContinuousOn (fun σ => driftCoeff D (ρ σ) j q) S := by
  unfold driftCoeff
  refine ContinuousOn.sub (continuousOn_finsetSum _ fun i _ => ?_) continuousOn_const
  simp only [gradRieszCoeff, derivCoeff, rieszMult]
  exact continuousOn_const.mul (continuousOn_const.mul (continuousOn_const.mul (hρ q)))

lemma continuousOn_forwardGen {S : Set ℝ} {n : ℕ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (c : ℝ → Coeff d) (hρ : ∀ q, ContinuousOn (fun σ => coeffOf (ρ σ) q) S)
    (hc : ∀ σ, IsTrigPoly n (c σ)) (hcc : ∀ q, ContinuousOn (fun σ => c σ q) S) (k : Lattice d) :
    ContinuousOn (fun σ => forwardGen D (ρ σ) (c σ) k) S := by
  have hder : ∀ (j : Fin d) (q : Lattice d), ContinuousOn (fun σ => derivCoeff j (c σ) q) S := by
    intro j q
    simp only [derivCoeff]
    exact continuousOn_const.mul (hcc q)
  unfold forwardGen
  refine ContinuousOn.sub (ContinuousOn.add ?_ ?_) ?_
  · simp only [laplaceCoeff]
    exact continuousOn_const.mul (continuousOn_const.mul (hcc k))
  · unfold transportCoeff
    refine continuousOn_finsetSum _ fun j _ => ?_
    simp_rw [mulCoeff_trig _ _ (hc _)]
    exact continuousOn_finsetSum _ fun l _ =>
      (continuousOn_drift D ρ hρ j (k - l)).mul (hder j l)
  · unfold nonlocalCoeff
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    have e : ∀ σ, ((D.M j i : ℝ) : ℂ) *
        gradRieszCoeff d D.s i (mulCoeff (coeffOf (ρ σ)) (derivCoeff j (c σ))) k =
        ((D.M j i : ℝ) : ℂ) * ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) *
          (((rieszCoeff d D.s k : ℝ) : ℂ) *
            ∑ l ∈ boxFinsetL n, coeffOf (ρ σ) (k - l) * derivCoeff j (c σ) l)) := by
      intro σ
      show ((D.M j i : ℝ) : ℂ) * ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) *
        (((rieszCoeff d D.s k : ℝ) : ℂ) * mulCoeff (coeffOf (ρ σ)) (derivCoeff j (c σ)) k)) = _
      rw [mulCoeff_trig _ _ (hc σ)]
    refine ContinuousOn.congr ?_ (fun σ _ => e σ)
    refine continuousOn_const.mul (continuousOn_const.mul (continuousOn_const.mul ?_))
    exact continuousOn_finsetSum _ fun l _ => (hρ (k - l)).mul (hder j l)


/-! ### Uniform `ℓ²` bounds from the coefficient hypothesis -/

lemma cbNorm_nonneg' (k : ℕ) (φ : Torus d → ℝ) : 0 ≤ Torus.cbNorm k φ :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

lemma isCk_cast {m : ℕ} {φ : Torus d → ℝ} (h : Torus.IsCk (m + 3) φ) :
    Torus.IsCk (((m + 3 : ℕ)) : WithTop ℕ∞) φ := by
  exact_mod_cast h

lemma exists_coeff_bound (D : DynData d) (μ : ℝ → Torus d → ℝ) (m : ℕ) (Λ VB T : ℝ)
    (hμ : CoeffHyp m Λ T μ) (hV : VHyp m VB D.V) :
    ∃ K : ℝ, ∀ r ∈ Set.Icc 0 T, MemHs 0 (coeffOf (μ r)) ∧ hsNormSq 0 (coeffOf (μ r)) ≤ K ∧
      ∀ j, MemHs 0 (driftCoeff D (μ r) j) ∧ hsNormSq 0 (driftCoeff D (μ r) j) ≤ K := by
  set K0 : ℝ := (1 + d) * Λ ^ 2 with hK0
  set KV : ℝ := (1 + d) * VB ^ 2 with hKV
  set Cmax : ℝ := |rieszConst d D.s| * ∑ j, ∑ i, |D.M j i| with hCmax
  refine ⟨K0 + 2 * (Cmax ^ 2 * K0 + KV), fun r hr => ?_⟩
  have hρ := memHs_one_coeffOf_cbNorm (m + 3) (by omega) (μ r) (isCk_cast (hμ.smooth r hr))
  have hVV := memHs_one_coeffOf_cbNorm (m + 3) (by omega) D.V (isCk_cast hV.1)
  have hcb : Torus.cbNorm (m + 3) (μ r) ^ 2 ≤ Λ ^ 2 :=
    pow_le_pow_left₀ (cbNorm_nonneg' _ _) (hμ.bound r hr) 2
  have hcbV : Torus.cbNorm (m + 3) D.V ^ 2 ≤ VB ^ 2 :=
    pow_le_pow_left₀ (cbNorm_nonneg' _ _) hV.2 2
  have hd0 : (0 : ℝ) ≤ 1 + d := by positivity
  have hρK : hsNormSq 1 (coeffOf (μ r)) ≤ K0 :=
    hρ.2.trans (mul_le_mul_of_nonneg_left hcb hd0)
  have hVK : hsNormSq 1 (coeffOf D.V) ≤ KV :=
    hVV.2.trans (mul_le_mul_of_nonneg_left hcbV hd0)
  have hK0nn : 0 ≤ K0 := by
    have := (hsNormSq_nonneg 1 (coeffOf (μ r))).trans hρK
    exact this
  have hCnn : 0 ≤ Cmax := mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hKVnn : 0 ≤ KV := (hsNormSq_nonneg 1 (coeffOf D.V)).trans hVK
  have hnn : 0 ≤ 2 * (Cmax ^ 2 * K0 + KV) := by positivity
  refine ⟨hρ.1.mono (by norm_num), ?_, fun j => ?_⟩
  · have := (hsNormSq_mono (m := 1) (m' := 0) (by norm_num) hρ.1).trans hρK
    linarith
  · obtain ⟨h1, h2⟩ := driftCoeff_memHs0 D (μ r) hρ.1 hVV.1 j
    refine ⟨h1, h2.trans ?_⟩
    have hle : |rieszConst d D.s| * ∑ i, |D.M j i| ≤ Cmax := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact Finset.single_le_sum (f := fun j => ∑ i, |D.M j i|)
        (fun j _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ j)
    have hle0 : 0 ≤ |rieszConst d D.s| * ∑ i, |D.M j i| :=
      mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _)
    have hsq : (|rieszConst d D.s| * ∑ i, |D.M j i|) ^ 2 ≤ Cmax ^ 2 :=
      pow_le_pow_left₀ hle0 hle 2
    have : 2 * ((|rieszConst d D.s| * ∑ i, |D.M j i|) ^ 2 * hsNormSq 1 (coeffOf (μ r)) +
        hsNormSq 1 (coeffOf D.V)) ≤ 2 * (Cmax ^ 2 * K0 + KV) := by
      have h3 : (|rieszConst d D.s| * ∑ i, |D.M j i|) ^ 2 * hsNormSq 1 (coeffOf (μ r)) ≤
          Cmax ^ 2 * K0 :=
        mul_le_mul hsq hρK (hsNormSq_nonneg _ _) (sq_nonneg _)
      linarith
    linarith


/-! ### The passage to the limit -/

lemma genBound_nonneg (D : DynData d) (K : ℝ) (k : Lattice d) : 0 ≤ genBound D K k := by
  unfold genBound
  have h1 : 0 ≤ Lattice.enorm k := norm_nonneg _
  have h2 : 0 ≤ ∑ i : Fin d, ∑ j : Fin d, |D.M j i| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  positivity

lemma sobWeight_ge_one {m : ℝ} (hm : 0 ≤ m) (k : Lattice d) : 1 ≤ sobWeight m k :=
  Real.one_le_rpow (one_le_sobBase k) hm

lemma exists_inBox (k : Lattice d) : ∃ N : ℕ, ∀ n, N ≤ n → InBox n k := by
  refine ⟨Finset.univ.sup fun i => (k i).natAbs, fun n hn i => ?_⟩
  have h1 : (k i).natAbs ≤ n :=
    (Finset.le_sup (f := fun i => (k i).natAbs) (Finset.mem_univ i)).trans hn
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h1

/-- Coordinatewise bound and uniform Lipschitz bound in time for the Galerkin coefficients. -/
lemma galerkin_coord_bounds (D : DynData d) (μ : ℝ → Torus d → ℝ) (m : ℕ) (hm : 1 ≤ m)
    (T t : ℝ) (ht : t ∈ Set.Ioc 0 T) (K : ℝ)
    (hK : ∀ r ∈ Set.Icc 0 T, MemHs 0 (coeffOf (μ r)) ∧ hsNormSq 0 (coeffOf (μ r)) ≤ K ∧
      ∀ j, MemHs 0 (driftCoeff D (μ r) j) ∧ hsNormSq 0 (driftCoeff D (μ r) j) ≤ K)
    (hρc : ∀ q, ContinuousOn (fun σ => coeffOf (μ (t - σ)) q) (Set.Icc 0 t))
    (φc : Coeff d) (F : ℕ → ℝ → Coeff d)
    (htrig : ∀ n τ, IsTrigPoly n (F n τ))
    (hcont : ∀ n k, ContinuousOn (fun τ => F n τ k) (Set.Icc 0 t))
    (heq : ∀ n k, ∀ τ ∈ Set.Icc 0 t, F n τ k = truncCoeff n φc k +
      ∫ σ in (0 : ℝ)..τ, truncCoeff n (forwardGen D (μ (t - σ)) (truncCoeff n (F n σ))) k)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hBsq : ∀ n, ∀ τ ∈ Set.Icc (0 : ℝ) t, hsNormSq m (F n τ) ≤ B ^ 2) :
    (∀ n k, ∀ τ ∈ Set.Icc (0 : ℝ) t, ‖F n τ k‖ ≤ B) ∧
    (∀ n k, ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ σ ∈ Set.Icc (0 : ℝ) t,
      ‖F n τ k - F n σ k‖ ≤ (genBound D K k * B) * |τ - σ|) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmem : ∀ n τ, MemHs (m : ℝ) (F n τ) := fun n τ => memHs_of_isTrigPoly (htrig n τ) _
  have hcoord : ∀ n k, ∀ τ ∈ Set.Icc (0 : ℝ) t, ‖F n τ k‖ ≤ B := by
    intro n k τ hτ
    have h1 := sobWeight_mul_sq_le_hsNormSq (hmem n τ) k
    have h2 := sobWeight_ge_one (m := (m : ℝ)) (by positivity) k
    have h3 : ‖F n τ k‖ ^ 2 ≤ B ^ 2 := by
      have := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖F n τ k‖)
      linarith [hBsq n τ hτ]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB0 two_ne_zero).mp h3
  refine ⟨hcoord, ?_⟩
  intro n k τ hτ σ hσ
  -- the integrand
  set g : ℝ → ℂ := fun σ' => truncCoeff n (forwardGen D (μ (t - σ')) (truncCoeff n (F n σ'))) k
    with hg
  have hg2 : ∀ σ', g σ' = if InBox n k then forwardGen D (μ (t - σ')) (F n σ') k else 0 := by
    intro σ'
    simp only [hg, truncCoeff_of_isTrigPoly (htrig n σ')]
    unfold truncCoeff
    rfl
  have hgc : ContinuousOn g (Set.Icc 0 t) := by
    have hfc := continuousOn_forwardGen (n := n) D (fun σ' => μ (t - σ')) (F n) hρc
      (htrig n) (hcont n) k
    have : g = fun σ' => if InBox n k then forwardGen D (μ (t - σ')) (F n σ') k else 0 :=
      funext hg2
    rw [this]
    by_cases hk : InBox n k
    · simpa [hk] using hfc
    · simpa [hk] using continuousOn_const
  have hgb : ∀ σ' ∈ Set.Icc (0 : ℝ) t, ‖g σ'‖ ≤ genBound D K k * B := by
    intro σ' hσ'
    have hr : t - σ' ∈ Set.Icc 0 T := ⟨by linarith [hσ'.2], by linarith [hσ'.1, ht.2]⟩
    obtain ⟨h0, hK0, hb⟩ := hK (t - σ') hr
    have hH1 : hsNormSq 1 (F n σ') ≤ B ^ 2 :=
      (hsNormSq_mono hm1 (hmem n σ')).trans (hBsq n σ' hσ')
    have hmain := norm_forwardGen_le D (μ (t - σ')) K h0 hK0 (fun j => (hb j).1)
      (fun j => (hb j).2) (F n σ') ((hmem n σ').mono hm1) k
    have hsq : Real.sqrt (hsNormSq 1 (F n σ')) ≤ B := Real.sqrt_le_iff.mpr ⟨hB0, hH1⟩
    rw [hg2]
    by_cases hk : InBox n k
    · simp only [hk, ite_true]
      exact hmain.trans (mul_le_mul_of_nonneg_left hsq (genBound_nonneg D K k))
    · simp only [hk, ite_false, norm_zero]
      exact mul_nonneg (genBound_nonneg D K k) hB0
  have hii : ∀ a ∈ Set.Icc (0 : ℝ) t, IntervalIntegrable g MeasureTheory.volume 0 a := by
    intro a ha
    refine (hgc.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le ha.1]
    exact Set.Icc_subset_Icc le_rfl ha.2
  have hdiff : F n τ k - F n σ k = ∫ x in σ..τ, g x := by
    rw [heq n k τ hτ, heq n k σ hσ]
    have := intervalIntegral.integral_interval_sub_left (hii τ hτ) (hii σ hσ)
    rw [add_sub_add_left_eq_sub, this]
  rw [hdiff]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := genBound D K k * B) ?_).trans
    (le_of_eq (by rw [abs_sub_comm]))
  intro x hx
  exact hgb x (Set.uIcc_subset_Icc hσ hτ (Set.uIoc_subset_uIcc hx))


/-- **Passage to the limit** (core statement of `galerkin_limit`, in terms of the integral
equations): a uniformly `H^m`-bounded sequence of Galerkin coefficient paths has a subsequence
converging uniformly on `[0,t]` in every coordinate to a forward solution in `C_w([0,t];H^m)`
obeying the same bound. -/
theorem galerkin_limit_core (D : DynData d) (μ : ℝ → Torus d → ℝ) (m : ℕ) (hm : 1 ≤ m)
    (Λ VB T : ℝ) (hμ : CoeffHyp m Λ T μ) (hV : VHyp m VB D.V) (t : ℝ) (ht : t ∈ Set.Ioc 0 T)
    (φc : Coeff d) (F : ℕ → ℝ → Coeff d)
    (htrig : ∀ n τ, IsTrigPoly n (F n τ))
    (hcont : ∀ n k, ContinuousOn (fun τ => F n τ k) (Set.Icc 0 t))
    (heq : ∀ n k, ∀ τ ∈ Set.Icc 0 t, F n τ k = truncCoeff n φc k +
      ∫ σ in (0 : ℝ)..τ, truncCoeff n (forwardGen D (μ (t - σ)) (truncCoeff n (F n σ))) k)
    (B : ℝ) (hB : ∀ n, ∀ τ ∈ Set.Icc 0 t, hsNorm (m : ℝ) (F n τ) ≤ B) :
    ∃ (ψ : ℕ → ℕ) (G : ℝ → Coeff d), StrictMono ψ ∧
      (∀ k, TendstoUniformlyOn (fun n τ => F (ψ n) τ k) (fun τ => G τ k) atTop
        (Set.Icc 0 t)) ∧
      IsForwardSolution D μ t φc G ∧ WeakContinuousInHs (m : ℝ) G t ∧
      ∀ τ ∈ Set.Icc 0 t, hsNorm (m : ℝ) (G τ) ≤ B := by
  classical
  have ht0 : 0 < t := ht.1
  have htT : t ≤ T := ht.2
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 t := ⟨le_rfl, ht0.le⟩
  have hB0 : 0 ≤ B := (Real.sqrt_nonneg _).trans (hB 0 0 h0mem)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmem : ∀ n τ, MemHs (m : ℝ) (F n τ) := fun n τ => memHs_of_isTrigPoly (htrig n τ) _
  have hBsq : ∀ n, ∀ τ ∈ Set.Icc (0 : ℝ) t, hsNormSq (m : ℝ) (F n τ) ≤ B ^ 2 :=
    fun n τ hτ => (Real.sqrt_le_iff.mp (hB n τ hτ)).2
  obtain ⟨K, hK⟩ := exists_coeff_bound D μ m Λ VB T hμ hV
  have hcontμ : ∀ r ∈ Set.Icc 0 T, Continuous (μ r) := fun r hr =>
    Torus.continuous_of_continuous_lift (hμ.smooth r hr).continuous
  have hkr : ∀ σ ∈ Set.Icc (0 : ℝ) t, t - σ ∈ Set.Icc 0 T := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hρc : ∀ q, ContinuousOn (fun σ => coeffOf (μ (t - σ)) q) (Set.Icc 0 t) := fun q =>
    (continuousOn_coeffOf_family hcontμ hμ.cont q).comp
      (continuous_const.sub continuous_id).continuousOn hkr
  obtain ⟨hcoord, hlip⟩ := galerkin_coord_bounds D μ m hm T t ht K hK hρc φc F htrig hcont heq
    B hB0 hBsq
  obtain ⟨ψ, hψ, G, hG⟩ := exists_subseq_tendstoUniformlyOn_coord
    (fun n τ k => F n τ k) t (fun _ => B) (fun k => genBound D K k * B)
    (fun n k τ hτ => hcoord n k τ hτ) (fun n k τ hτ σ hσ => hlip n k τ hτ σ hσ)
  have hconv : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) t, Tendsto (fun n => F (ψ n) τ k) atTop (𝓝 (G τ k)) :=
    fun k τ hτ => (hG k).tendsto_at hτ
  have hGb : ∀ τ ∈ Set.Icc (0 : ℝ) t, MemHs (m : ℝ) (G τ) ∧ hsNormSq (m : ℝ) (G τ) ≤ B ^ 2 := by
    intro τ hτ
    refine memHs_of_sum_le fun S => ?_
    have hlim : Tendsto (fun n => ∑ k ∈ S, sobWeight (m : ℝ) k * ‖F (ψ n) τ k‖ ^ 2) atTop
        (𝓝 (∑ k ∈ S, sobWeight (m : ℝ) k * ‖G τ k‖ ^ 2)) :=
      tendsto_finsetSum S fun k _ => (((hconv k τ hτ).norm).pow 2).const_mul _
    exact le_of_tendsto hlim (Filter.Eventually.of_forall fun n =>
      (sum_le_hsNormSq (hmem _ τ) S).trans (hBsq _ τ hτ))
  have hGc : ∀ k, ContinuousOn (fun τ => G τ k) (Set.Icc 0 t) := fun k =>
    (hG k).continuousOn (Filter.Eventually.of_forall fun n => hcont (ψ n) k).frequently
  have hweak : WeakContinuousInHs (m : ℝ) G t :=
    weakContinuous_of_bdd (fun τ hτ => (hGb τ hτ).1) B hB0 (fun τ hτ => (hGb τ hτ).2) hGc
  have hH1 : ∀ n, ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ S : Finset (Lattice d),
      ∑ k ∈ S, sobWeight 1 k * ‖F n τ k‖ ^ 2 ≤ B ^ 2 := fun n τ hτ S =>
    (sum_le_hsNormSq ((hmem n τ).mono hm1) S).trans
      ((hsNormSq_mono hm1 (hmem n τ)).trans (hBsq n τ hτ))
  have hconvG : ∀ k, ∀ σ ∈ Set.Icc (0 : ℝ) t, Tendsto
      (fun n => forwardGen D (μ (t - σ)) (F (ψ n) σ) k) atTop
      (𝓝 (forwardGen D (μ (t - σ)) (G σ) k)) := by
    intro k σ hσ
    obtain ⟨h0, -, hb⟩ := hK (t - σ) (hkr σ hσ)
    exact tendsto_forwardGen D (μ (t - σ)) h0 (fun j => (hb j).1) (fun n => F (ψ n) σ) (G σ) B
      hB0 (Filter.Eventually.of_forall fun n => hH1 _ σ hσ) (fun q => hconv q σ hσ) k
  have hmeas : ∀ n k, AEStronglyMeasurable (fun σ => forwardGen D (μ (t - σ)) (F n σ) k)
      (volume.restrict (Set.Icc 0 t)) := fun n k =>
    (continuousOn_forwardGen D (fun σ' => μ (t - σ')) (F n) hρc (htrig n) (hcont n)
      k).aestronglyMeasurable measurableSet_Icc
  have hmeasG : ∀ k, AEStronglyMeasurable (fun σ => forwardGen D (μ (t - σ)) (G σ) k)
      (volume.restrict (Set.Icc 0 t)) := fun k =>
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => hmeas (ψ n) k)
      ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun σ hσ =>
        hconvG k σ hσ))
  have hgen : ∀ H : Coeff d, MemHs 1 H → hsNormSq 1 H ≤ B ^ 2 → ∀ k, ∀ σ ∈ Set.Icc (0 : ℝ) t,
      ‖forwardGen D (μ (t - σ)) H k‖ ≤ genBound D K k * B := by
    intro H hH hHB k σ hσ
    obtain ⟨h0, hK0, hb⟩ := hK (t - σ) (hkr σ hσ)
    have := norm_forwardGen_le D (μ (t - σ)) K h0 hK0 (fun j => (hb j).1) (fun j => (hb j).2)
      H hH k
    exact this.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨hB0, hHB⟩)
      (genBound_nonneg D K k))
  have hGgen : ∀ k, ∀ σ ∈ Set.Icc (0 : ℝ) t,
      ‖forwardGen D (μ (t - σ)) (G σ) k‖ ≤ genBound D K k * B := fun k σ hσ =>
    hgen (G σ) ((hGb σ hσ).1.mono hm1)
      ((hsNormSq_mono hm1 (hGb σ hσ).1).trans (hGb σ hσ).2) k σ hσ
  have hFgen : ∀ n k, ∀ σ ∈ Set.Icc (0 : ℝ) t,
      ‖forwardGen D (μ (t - σ)) (F n σ) k‖ ≤ genBound D K k * B := fun n k σ hσ =>
    hgen (F n σ) ((hmem n σ).mono hm1)
      ((hsNormSq_mono hm1 (hmem n σ)).trans (hBsq n σ hσ)) k σ hσ
  refine ⟨ψ, G, hψ, hG, ⟨fun τ hτ => (hGb τ hτ).1.mono hm1, fun k => ?_, fun k τ hτ => ?_⟩,
    hweak, fun τ hτ => ?_⟩
  · -- integrability
    refine Integrable.of_bound (hmeasG k) (genBound D K k * B) ?_
    exact (ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall fun σ hσ => hGgen k σ hσ)
  · -- the integral equation
    have hsub : Set.uIoc 0 τ ⊆ Set.Icc 0 t :=
      Set.uIoc_subset_uIcc.trans (Set.uIcc_subset_Icc h0mem hτ)
    obtain ⟨N, hN⟩ := exists_inBox k
    have hlim2 : Tendsto (fun n => truncCoeff (ψ n) φc k +
        ∫ σ in (0 : ℝ)..τ, forwardGen D (μ (t - σ)) (F (ψ n) σ) k) atTop
        (𝓝 (φc k + ∫ σ in (0 : ℝ)..τ, forwardGen D (μ (t - σ)) (G σ) k)) := by
      refine Tendsto.add ?_ ?_
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [hψ.tendsto_atTop.eventually_ge_atTop N] with n hn
        simp [truncCoeff, hN _ hn]
      · refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
          (fun _ => genBound D K k * B) (Filter.Eventually.of_forall fun n => ?_)
          (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun x hx => ?_)
          intervalIntegrable_const (Filter.Eventually.of_forall fun x hx => ?_)
        · exact (hmeas (ψ n) k).mono_measure (Measure.restrict_mono hsub le_rfl)
        · exact hFgen (ψ n) k x (hsub hx)
        · exact hconvG k x (hsub hx)
    have heq' : ∀ᶠ n in atTop, F (ψ n) τ k = truncCoeff (ψ n) φc k +
        ∫ σ in (0 : ℝ)..τ, forwardGen D (μ (t - σ)) (F (ψ n) σ) k := by
      filter_upwards [hψ.tendsto_atTop.eventually_ge_atTop N] with n hn
      rw [heq (ψ n) k τ hτ]
      congr 2
      funext σ
      rw [truncCoeff_of_isTrigPoly (htrig _ σ)]
      simp [truncCoeff, hN _ hn]
    exact tendsto_nhds_unique ((hconv k τ hτ).congr' heq') hlim2
  · exact Real.sqrt_le_iff.mpr ⟨hB0, (hGb τ hτ).2⟩

end HRS.PDE
