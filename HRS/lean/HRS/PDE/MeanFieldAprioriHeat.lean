import HRS.PDE.MeanFieldDefs

/-!
# A priori bounds for the mean-field equation, packet AP2a: the heat kernel on the torus

The torus heat kernel `H_t(x) = ∑_k e^{-4π²|k|²t} cos(2πk·x)` (nonnegative by the Jacobi identity,
which is `theta_nonneg`), its Fourier coefficients, convolution, tail sums, and the two
symmetrisation inequalities (`∫ φ (f - H ⋆ f) ≥ 0` and Chebyshev's inequality for monotone
couplings).  Package MF-01.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFApriori

variable {d : ℕ}

/-- Heat multiplier `e^{-4π²|k|² t}`. -/
def heatMult (t : ℝ) (k : Lattice d) : ℝ := Real.exp (-(4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * t)

/-- The heat kernel `H_t(x) = ∑_k e^{-4π²|k|²t} cos(2πk·x)`. -/
def heatKer (t : ℝ) (x : Torus d) : ℝ := ∑' k : Lattice d, heatMult t k * Torus.cosMode k x

/-- Tail `∑_{k ≠ 0} e^{-4π²|k|²t}`. -/
def heatTail (d : ℕ) (t : ℝ) : ℝ := ∑' k : NonzeroLattice d, heatMult t k.1

theorem heatMult_pos (t : ℝ) (k : Lattice d) : 0 < heatMult t k := Real.exp_pos _

theorem heatMult_summable {t : ℝ} (ht : 0 < t) : Summable (heatMult (d := d) t) := by
  have h := summable_gauss_lattice d (4 * Real.pi ^ 2 * t) (by positivity)
  refine h.congr fun k => ?_
  unfold heatMult
  congr 1
  ring

theorem heatMult_neg (t : ℝ) (k : Lattice d) : heatMult t (-k) = heatMult t k := by
  have : Lattice.enorm (-k) = Lattice.enorm k := by
    unfold Lattice.enorm Lattice.toEuc
    rw [← norm_neg]
    congr 1
    ext i
    simp
  unfold heatMult
  rw [this]

theorem heatKer_nonneg (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) (x : Torus d) : 0 ≤ heatKer t x := by
  have h := theta_nonneg x (u := 4 * Real.pi ^ 2 * t) (by positivity)
  have e : ∀ k : Lattice d, heatMult t k = Real.exp (-(4 * Real.pi ^ 2 * t) * Lattice.enorm k ^ 2) := by
    intro k; unfold heatMult; congr 1; ring
  unfold heatKer
  simpa only [e] using h

theorem heatKer_continuous {t : ℝ} (ht : 0 < t) : Continuous (heatKer (d := d) t) := by
  unfold heatKer
  refine continuous_tsum (u := heatMult t) (fun k => continuous_const.mul (Torus.continuous_cosMode k))
    (heatMult_summable ht) fun k x => ?_
  rw [norm_mul, Real.norm_of_nonneg (heatMult_pos t k).le]
  calc heatMult t k * ‖Torus.cosMode k x‖ ≤ heatMult t k * 1 :=
        mul_le_mul_of_nonneg_left (Torus.norm_cosMode_le k x) (heatMult_pos t k).le
    _ = heatMult t k := mul_one _

theorem heatKer_neg (t : ℝ) (x : Torus d) : heatKer t (-x) = heatKer t x := by
  unfold heatKer
  refine tsum_congr fun k => ?_
  congr 1
  unfold Torus.cosMode
  rw [Fried.mode_neg_arg, Complex.conj_re]

/-- The heat kernel as a complex Fourier series. -/
theorem heatKer_ofReal {t : ℝ} (ht : 0 < t) (x : Torus d) :
    (heatKer t x : ℂ) = ∑' k : Lattice d, (heatMult t k : ℂ) * Torus.mode k x := by
  have hs : Summable fun k : Lattice d => (heatMult t k : ℂ) * Torus.mode k x := by
    refine Summable.of_norm ?_
    refine (heatMult_summable ht).congr fun k => ?_
    rw [norm_mul, Torus.norm_mode, mul_one, Complex.norm_real, Real.norm_of_nonneg (heatMult_pos t k).le]
  have hs' : Summable fun k : Lattice d => (heatMult t (-k) : ℂ) * Torus.mode (-k) x :=
    hs.comp_injective (neg_injective (G := Lattice d))
  have h1 : ∑' k : Lattice d, (heatMult t (-k) : ℂ) * Torus.mode (-k) x =
      ∑' k : Lattice d, (heatMult t k : ℂ) * Torus.mode k x :=
    Equiv.tsum_eq (Equiv.neg (Lattice d)) (fun k => (heatMult t k : ℂ) * Torus.mode k x)
  have h2 : ∀ k : Lattice d, ((heatMult t k * Torus.cosMode k x : ℝ) : ℂ) =
      ((heatMult t k : ℂ) * Torus.mode k x + (heatMult t (-k) : ℂ) * Torus.mode (-k) x) / 2 := by
    intro k
    rw [heatMult_neg, Torus.mode_neg]
    push_cast
    have := Complex.add_conj (Torus.mode k x)
    push_cast at this
    unfold Torus.cosMode
    linear_combination ((heatMult t k : ℂ) / 2) * this.symm
  unfold heatKer
  rw [Complex.ofReal_tsum]
  simp_rw [h2]
  rw [tsum_div_const, Summable.tsum_add hs hs', h1]
  ring

theorem integral_mode_heatKer {t : ℝ} (ht : 0 < t) (k : Lattice d) :
    ∫ x, Torus.mode (-k) x * (heatKer (d := d) t x : ℂ) = (heatMult t k : ℂ) := by
  simp_rw [heatKer_ofReal ht]
  have hF : ∀ j : Lattice d, Integrable (fun x : Torus d => Torus.mode (-k) x *
      ((heatMult t j : ℂ) * Torus.mode j x)) := fun j =>
    ((Torus.continuous_mode (-k)).mul (continuous_const.mul (Torus.continuous_mode j))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hn : ∀ j : Lattice d, ∫ x : Torus d, ‖Torus.mode (-k) x * ((heatMult t j : ℂ) * Torus.mode j x)‖ =
      heatMult t j := by
    intro j
    have : ∀ x : Torus d, ‖Torus.mode (-k) x * ((heatMult t j : ℂ) * Torus.mode j x)‖ = heatMult t j := by
      intro x
      rw [norm_mul, norm_mul, Torus.norm_mode, Torus.norm_mode, Complex.norm_real,
        Real.norm_of_nonneg (heatMult_pos t j).le]
      ring
    rw [show (fun x : Torus d => ‖Torus.mode (-k) x * ((heatMult t j : ℂ) * Torus.mode j x)‖) =
      fun _ => heatMult t j from funext this]
    simp
  have hsum : Summable fun j : Lattice d => ∫ x : Torus d, ‖Torus.mode (-k) x * ((heatMult t j : ℂ) * Torus.mode j x)‖ := by
    simp_rw [hn]; exact heatMult_summable ht
  have key := integral_tsum_of_summable_integral_norm hF hsum
  have e : ∀ x : Torus d, Torus.mode (-k) x * ∑' j : Lattice d, (heatMult t j : ℂ) * Torus.mode j x =
      ∑' j : Lattice d, Torus.mode (-k) x * ((heatMult t j : ℂ) * Torus.mode j x) := by
    intro x; rw [tsum_mul_left]
  simp_rw [e]
  rw [← key]
  have e2 : ∀ j : Lattice d, ∫ x : Torus d, Torus.mode (-k) x * ((heatMult t j : ℂ) * Torus.mode j x) =
      if j = k then (heatMult t j : ℂ) else 0 := by
    intro j
    have : ∀ x : Torus d, Torus.mode (-k) x * ((heatMult t j : ℂ) * Torus.mode j x) =
        (heatMult t j : ℂ) * (Torus.mode (-k) x * Torus.mode j x) := fun x => by ring
    simp_rw [this]
    rw [integral_const_mul, Torus.integral_mode_mul]
    by_cases h : j = k
    · subst h; simp
    · have : ¬ (-k + j = 0) := fun h' => h (by rw [neg_add_eq_zero] at h'; exact h'.symm)
      simp [this, h]
  simp_rw [e2]
  rw [tsum_ite_eq]

theorem coeffOf_heatKer {t : ℝ} (ht : 0 < t) (k : Lattice d) :
    coeffOf (heatKer t) k = (heatMult t k : ℂ) := by
  unfold coeffOf
  rw [funFourierCoeff_eq_int]
  exact integral_mode_heatKer ht k

theorem integral_heatKer {t : ℝ} (ht : 0 < t) : ∫ x, heatKer (d := d) t x = 1 := by
  have h := coeffOf_heatKer ht (0 : Lattice d)
  unfold coeffOf at h
  rw [funFourierCoeff_eq_int] at h
  have h0 : ∀ x : Torus d, UnitAddTorus.mFourier (-(0 : Lattice d)) x = 1 := fun x => by
    simpa [Torus.mode] using Torus.mode_zero (d := d) x
  simp_rw [h0, one_mul] at h
  have hm : heatMult t (0 : Lattice d) = 1 := by
    have : Lattice.enorm (0 : Lattice d) = 0 := by
      unfold Lattice.enorm Lattice.toEuc
      have : (WithLp.toLp 2 fun i : Fin d => (((0 : Lattice d) i : ℤ) : ℝ)) = 0 := by ext i; simp
      rw [this, norm_zero]
    unfold heatMult
    rw [this]; simp
  rw [hm, integral_complex_ofReal] at h
  exact_mod_cast h

theorem integrable_heatKer {t : ℝ} (ht : 0 < t) : Integrable (heatKer (d := d) t) :=
  (heatKer_continuous ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem coeffOf_convFun_heatKer {t : ℝ} (ht : 0 < t) {f : Torus d → ℝ} (hf : Continuous f)
    (k : Lattice d) : coeffOf (convFun (heatKer t) f) k = (heatMult t k : ℂ) * coeffOf f k := by
  unfold coeffOf
  rw [MFAux.funFourierCoeff_convFun (integrable_heatKer ht) hf k]
  congr 1
  exact coeffOf_heatKer ht k

theorem convFun_heatKer_nonneg (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) {f : Torus d → ℝ}
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (x : Torus d) : 0 ≤ convFun (heatKer t) f x := by
  unfold convFun
  exact integral_nonneg fun y => mul_nonneg (heatKer_nonneg hd ht _) (hf0 y)

/-- A continuous function on a compact space is integrable for any measure finite on compacts. -/
theorem integrable_of_continuous_compact {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {g : X → ℝ} (hg : Continuous g) : Integrable g μ :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_mul_sub_conv_nonneg {H : Torus d → ℝ} (hH : Continuous H) (hH0 : ∀ x, 0 ≤ H x)
    (hHe : ∀ x, H (-x) = H x) (hH1 : ∫ x, H x = 1) {f φ : Torus d → ℝ} (hf : Continuous f)
    (hφ : Continuous φ) (hmono : ∀ x y, 0 ≤ (φ x - φ y) * (f x - f y)) :
    0 ≤ ∫ x, φ x * (f x - convFun H f x) := by
  set D : Torus d → Torus d → ℝ := fun x y => H (x - y) * (φ x * (f x - f y)) with hD
  set D' : Torus d → Torus d → ℝ := fun x y => H (x - y) * (φ y * (f y - f x)) with hD'
  have hDc : Continuous (Function.uncurry D) := by
    simp only [hD, Function.uncurry]
    fun_prop
  have hD'c : Continuous (Function.uncurry D') := by
    simp only [hD', Function.uncurry]
    fun_prop
  have hDi : Integrable (Function.uncurry D) (volume.prod volume) := integrable_of_continuous_compact hDc
  have hD'i : Integrable (Function.uncurry D') (volume.prod volume) := integrable_of_continuous_compact hD'c
  -- the first expression
  have hmass : ∀ x : Torus d, ∫ y, H (x - y) = 1 := fun x => by
    rw [integral_sub_left_eq_self (fun z => H z) volume x, hH1]
  have h1 : ∀ x, φ x * (f x - convFun H f x) = ∫ y, D x y := by
    intro x
    have hi1 : Integrable (fun y => H (x - y) * (φ x * f x)) :=
      integrable_of_continuous_compact (by fun_prop)
    have hi2 : Integrable (fun y => H (x - y) * (φ x * f y)) :=
      integrable_of_continuous_compact (by fun_prop)
    have e : ∀ y, D x y = H (x - y) * (φ x * f x) - φ x * (H (x - y) * f y) := fun y => by
      simp only [hD]; ring
    simp_rw [e]
    rw [integral_sub hi1 (by simpa [mul_left_comm] using hi2), integral_mul_const, integral_const_mul, hmass]
    unfold convFun
    ring
  have hI : ∫ x, φ x * (f x - convFun H f x) = ∫ x, ∫ y, D x y := integral_congr_ae
    (Filter.Eventually.of_forall h1)
  -- swap
  have hI' : ∫ x, ∫ y, D x y = ∫ x, ∫ y, D' x y := by
    rw [integral_integral_swap hDi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hD, hD']
    rw [← hHe (y - x), neg_sub]
  have a1 : Integrable (fun x => ∫ y, D x y) := hDi.integral_prod_left
  have a2 : Integrable (fun x => ∫ y, D' x y) := hD'i.integral_prod_left
  have hsum : (∫ x, ∫ y, D x y) + (∫ x, ∫ y, D' x y) = ∫ x, ∫ y, (D x y + D' x y) := by
    rw [← integral_add a1 a2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    refine (integral_add ?_ ?_).symm
    · exact integrable_of_continuous_compact (by simp only [hD]; fun_prop)
    · exact integrable_of_continuous_compact (by simp only [hD']; fun_prop)
  have hnn : 0 ≤ ∫ x, ∫ y, (D x y + D' x y) := by
    refine integral_nonneg fun x => integral_nonneg fun y => ?_
    have : D x y + D' x y = H (x - y) * ((φ x - φ y) * (f x - f y)) := by
      simp only [hD, hD']; ring
    rw [this]
    exact mul_nonneg (hH0 _) (hmono x y)
  rw [hI]
  linarith [hsum, hI']

theorem integral_mul_ge_mul_integral {f φ : Torus d → ℝ} (hf : Continuous f) (hφ : Continuous φ)
    (hmono : ∀ x y, 0 ≤ (φ x - φ y) * (f x - f y)) :
    (∫ x, φ x) * (∫ x, f x) ≤ ∫ x, φ x * f x := by
  have h := integral_mul_sub_conv_nonneg (d := d) (H := fun _ => (1 : ℝ)) continuous_const
    (fun _ => zero_le_one) (fun _ => rfl) (by simp) hf hφ hmono
  have hc : ∀ x, convFun (fun _ : Torus d => (1 : ℝ)) f x = ∫ y, f y := fun x => by
    unfold convFun; simp
  simp_rw [hc] at h
  have e : ∀ x, φ x * (f x - ∫ y, f y) = φ x * f x - (∫ y, f y) * φ x := fun x => by ring
  simp_rw [e] at h
  have i1 : Integrable (fun x => φ x * f x) := integrable_of_continuous_compact (hφ.mul hf)
  have i2 : Integrable (fun x => (∫ y, f y) * φ x) := (integrable_of_continuous_compact hφ).const_mul _
  rw [integral_sub i1 i2, integral_const_mul] at h
  linarith

theorem heatTail_summable (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    Summable fun k : NonzeroLattice d => heatMult t k.1 :=
  (heatMult_summable ht).comp_injective Subtype.val_injective

theorem heatTail_le (hd : 1 ≤ d) {t : ℝ} (ht : 1 ≤ t) :
    heatTail d t ≤ heatTail d 1 * Real.exp (-(4 * Real.pi ^ 2) * (t - 1)) := by
  unfold heatTail
  rw [← tsum_mul_right]
  refine Summable.tsum_le_tsum (fun k => ?_) (heatTail_summable hd (by linarith))
    ((heatTail_summable hd one_pos).mul_right _)
  have h1 := one_le_enorm k.1 k.2
  unfold heatMult
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hp : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  nlinarith [mul_nonneg (mul_nonneg hp (sub_nonneg.mpr ht)) (sub_nonneg.mpr (show (1:ℝ) ≤ Lattice.enorm k.1 ^ 2 by nlinarith))]

end HRS.PDE.MFApriori
