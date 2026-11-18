import HRS.MS.R2QtAux1
import HRS.MS.WrRowAux3

/-!
# HRS.MS.R2PolyAux1 -- Step A of `round2_polynomial_moments` (S9.5): analysis on `μ = ρ dx`

Packet S95, namespace `HRS.MS.R2Poly`, helper prefix `s95_`.  Infrastructure statements (not manuscript rows).

* Gaussian tail `μ(|x| > t) ≤ G e^{-c₀t²/2}`, weighted moments `∫ (⟨y⟩^P)² dμ`, row `L²` bound of `1 + W_s`.
* the section bound `∫ ⟨y⟩^P (1 + W_s(x-y)) dμ(y) ≤ C`, hence integrability of polynomial-envelope kernels.
* the annular cuts `cut lo hi g = 1_{lo < max(|x|,|y|) ≤ hi} g` and their bounded-class property.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Poly

open HRS.Whole HRS.MS.Wr HRS.MS.R2Mt

variable {d : ℕ}

/-! ### Scalar and Gaussian lemmas -/

theorem s95_pow_le_exp {a : ℝ} (ha : 0 ≤ a) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 ≤ u → (1 + u) ^ a ≤ C * Real.exp (ε * u) := by
  set n : ℕ := max ⌈a⌉₊ 1 with hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_max_right _ _
  have han : a ≤ n := (Nat.le_ceil a).trans (by exact_mod_cast le_max_left _ _)
  have hn0 : (0 : ℝ) < n := by linarith
  set lam : ℝ := min 1 (ε / n) with hlam
  have hlam0 : 0 < lam := lt_min one_pos (by positivity)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hlamn : (n : ℝ) * lam ≤ ε := by
    calc (n : ℝ) * lam ≤ n * (ε / n) := by gcongr; exact min_le_right _ _
      _ = ε := by field_simp
  refine ⟨(lam ^ n)⁻¹, by positivity, fun u hu => ?_⟩
  have h1 : (1 + u) ^ a ≤ (1 + u) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) han
  rw [Real.rpow_natCast] at h1
  have h2 : 1 + u ≤ lam⁻¹ * Real.exp (lam * u) := by
    have h3 : 1 + lam * u ≤ Real.exp (lam * u) := by linarith [Real.add_one_le_exp (lam * u)]
    have h4 : lam * (1 + u) ≤ 1 + lam * u := by nlinarith
    calc 1 + u = lam⁻¹ * (lam * (1 + u)) := by field_simp
      _ ≤ lam⁻¹ * Real.exp (lam * u) := by
          gcongr
          linarith
  calc (1 + u) ^ a ≤ (1 + u) ^ n := h1
    _ ≤ (lam⁻¹ * Real.exp (lam * u)) ^ n := pow_le_pow_left₀ (by linarith) h2 n
    _ = (lam ^ n)⁻¹ * Real.exp (n * (lam * u)) := by
        rw [mul_pow, inv_pow, ← Real.exp_nat_mul]
    _ ≤ (lam ^ n)⁻¹ * Real.exp (ε * u) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (by positivity)

theorem s95_gauss_int (d : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Euc d => Real.exp (-(b * ‖x‖ ^ 2))) (volume : Measure (Euc d)) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc d) (b := (b : ℂ))
    (by simpa using hb) 0 0).norm
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp
  left
  rw [← Complex.ofReal_pow]
  exact Complex.ofReal_re _


theorem s95_jb_meas : Measurable (fun x : Euc d => jbracket x) := by
  unfold jbracket; fun_prop

theorem s95_one_le_jb (x : Euc d) : 1 ≤ jbracket x := by
  unfold jbracket
  rw [Real.le_sqrt' one_pos]
  nlinarith [sq_nonneg ‖x‖]

theorem s95_jb_sq (x : Euc d) : jbracket x ^ 2 = 1 + ‖x‖ ^ 2 := by
  unfold jbracket
  rw [Real.sq_sqrt (by positivity)]

theorem s95_jbpow_sq (x : Euc d) (Pw : ℝ) : (jbracket x ^ Pw) ^ 2 = (1 + ‖x‖ ^ 2) ^ Pw := by
  have h0 : 0 ≤ jbracket x := (zero_le_one.trans (s95_one_le_jb x))
  rw [sq, ← Real.mul_rpow h0 h0, ← sq, s95_jb_sq]

theorem s95_ofReal_rpow_two {a : ℝ} (ha : 0 ≤ a) : ENNReal.ofReal a ^ (2 : ℝ) = ENNReal.ofReal (a ^ 2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg ha (by norm_num), Real.rpow_two]

/-- Gaussian tail of `μ`: `μ(|x| > t) ≤ G e^{-c₀ t²/2}`. -/
theorem s95_tail (d : ℕ) (C₀ c₀ : ℝ) (hc : 0 < c₀) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ ρ : Euc d → ℝ, (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) →
      ∀ t : ℝ, 0 ≤ t → HRS.Whole.withDensityReal ρ {x | t < ‖x‖} ≤ ENNReal.ofReal (G * Real.exp (-(c₀ * t ^ 2 / 2))) := by
  have hint := s95_gauss_int d (b := c₀ / 2) (by positivity)
  refine ⟨max C₀ 0 * ∫ x : Euc d, Real.exp (-(c₀ / 2 * ‖x‖ ^ 2)),
    mul_nonneg (le_max_right _ _) (integral_nonneg fun x => (Real.exp_pos _).le), fun ρ hG t ht => ?_⟩
  have hAm : MeasurableSet {x : Euc d | t < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  set K : ℝ := max C₀ 0 * Real.exp (-(c₀ * t ^ 2 / 2)) with hK
  have hK0 : 0 ≤ K := by positivity
  unfold HRS.Whole.withDensityReal
  rw [withDensity_apply _ hAm]
  calc ∫⁻ x in {x : Euc d | t < ‖x‖}, ENNReal.ofReal (ρ x)
      ≤ ∫⁻ x in {x : Euc d | t < ‖x‖}, ENNReal.ofReal (K * Real.exp (-(c₀ / 2 * ‖x‖ ^ 2))) := by
        refine setLIntegral_mono' hAm fun x hx => ENNReal.ofReal_le_ofReal ?_
        have hx' : t < ‖x‖ := hx
        have h1 := hG x
        have h2 : C₀ * Real.exp (-c₀ * ‖x‖ ^ 2) ≤ max C₀ 0 * Real.exp (-c₀ * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
        have h3 : Real.exp (-c₀ * ‖x‖ ^ 2) ≤ Real.exp (-(c₀ * t ^ 2 / 2)) * Real.exp (-(c₀ / 2 * ‖x‖ ^ 2)) := by
          rw [← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          have h4 : t ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ ht hx'.le 2
          nlinarith [mul_le_mul_of_nonneg_left h4 hc.le]
        calc ρ x ≤ _ := h1
          _ ≤ _ := h2
          _ ≤ max C₀ 0 * (Real.exp (-(c₀ * t ^ 2 / 2)) * Real.exp (-(c₀ / 2 * ‖x‖ ^ 2))) :=
              mul_le_mul_of_nonneg_left h3 (le_max_right _ _)
          _ = _ := by rw [hK]; ring
    _ ≤ ∫⁻ x, ENNReal.ofReal (K * Real.exp (-(c₀ / 2 * ‖x‖ ^ 2))) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ x : Euc d, K * Real.exp (-(c₀ / 2 * ‖x‖ ^ 2))) :=
        (ofReal_integral_eq_lintegral_ofReal (hint.const_mul K)
          (Filter.Eventually.of_forall fun x => mul_nonneg hK0 (Real.exp_pos _).le)).symm
    _ = _ := by
        rw [integral_const_mul, hK]
        congr 1
        ring

/-- Polynomial weights are `μ`-square integrable. -/
theorem s95_moment (d : ℕ) (C₀ c₀ : ℝ) (hc : 0 < c₀) {Pw : ℝ} (hP : 0 ≤ Pw) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) →
      ∫⁻ y, ENNReal.ofReal ((jbracket y ^ Pw) ^ 2) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal C := by
  obtain ⟨C', hC', hexp⟩ := s95_pow_le_exp hP (show 0 < c₀ / 2 by positivity)
  have hint := s95_gauss_int d (b := c₀ / 2) (by positivity)
  refine ⟨max C₀ 0 * C' * ∫ x : Euc d, Real.exp (-(c₀ / 2 * ‖x‖ ^ 2)),
    mul_nonneg (by positivity) (integral_nonneg fun x => (Real.exp_pos _).le), fun ρ hρ hG => ?_⟩
  have hm : Measurable (fun y : Euc d => ENNReal.ofReal ((jbracket y ^ Pw) ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((s95_jb_meas.pow_const Pw).pow_const 2)
  rw [HRS.Whole.Q34.lintegral_nu hρ _ hm]
  set K : ℝ := max C₀ 0 * C' with hK
  have hK0 : 0 ≤ K := by positivity
  calc ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal ((jbracket y ^ Pw) ^ 2)
      ≤ ∫⁻ y : Euc d, ENNReal.ofReal (K * Real.exp (-(c₀ / 2 * ‖y‖ ^ 2))) := by
        refine lintegral_mono fun y => ?_
        rw [← ENNReal.ofReal_mul (hρ.nonneg y)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [s95_jbpow_sq]
        have h1 := hexp (‖y‖ ^ 2) (by positivity)
        have h2 : ρ y ≤ max C₀ 0 * Real.exp (-c₀ * ‖y‖ ^ 2) :=
          (hG y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
        calc ρ y * (1 + ‖y‖ ^ 2) ^ Pw ≤ (max C₀ 0 * Real.exp (-c₀ * ‖y‖ ^ 2)) * (C' * Real.exp (c₀ / 2 * ‖y‖ ^ 2)) :=
              mul_le_mul h2 h1 (by positivity) (by positivity)
          _ = K * (Real.exp (-c₀ * ‖y‖ ^ 2) * Real.exp (c₀ / 2 * ‖y‖ ^ 2)) := by rw [hK]; ring
          _ = K * Real.exp (-(c₀ / 2 * ‖y‖ ^ 2)) := by
              rw [← Real.exp_add]
              congr 2
              ring
    _ = ENNReal.ofReal (∫ x : Euc d, K * Real.exp (-(c₀ / 2 * ‖x‖ ^ 2))) :=
        (ofReal_integral_eq_lintegral_ofReal (hint.const_mul K)
          (Filter.Eventually.of_forall fun x => mul_nonneg hK0 (Real.exp_pos _).le)).symm
    _ = _ := by
        rw [integral_const_mul, hK]

/-- Row `L²` bound of `1 + W_s`. -/
theorem s95_row_sq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ x : Euc d,
      ∫⁻ y, ENNReal.ofReal ((1 + HRS.Whole.rieszWeight s (x - y)) ^ 2) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal A := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Ca, Cb, hCa, hCb, H⟩ := wr3_row_bounds_real hd hs0 hsd 1 M
  refine ⟨Cb, hCb, fun ρ hρ hM x => ?_⟩
  have hq0 : ∀ x y : Euc d, 0 ≤ 1 + HRS.Whole.rieszWeight s (x - y) := fun x y => by
    have := wr3_rieszWeight_nonneg (d := d) s (x - y)
    linarith
  obtain ⟨-, h2⟩ := H ρ hρ hM (fun x y => 1 + HRS.Whole.rieszWeight s (x - y)) hq0 (fun x y _ => by simp) x
  have hWm : Measurable (fun y : Euc d => 1 + HRS.Whole.rieszWeight s (x - y)) :=
    measurable_const.add ((wr3_measurable_rieszWeight s).comp (measurable_const.sub measurable_id))
  set f : ℕ → Euc d → ℝ≥0∞ := fun n y => ENNReal.ofReal ((min (1 + HRS.Whole.rieszWeight s (x - y)) ((n : ℝ) + 1)) ^ 2) with hf
  have hfm : ∀ n, Measurable (f n) := fun n =>
    ENNReal.measurable_ofReal.comp ((hWm.min measurable_const).pow_const 2)
  have hmono : Monotone f := fun m n hmn y => by
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (le_min (hq0 x y) (by positivity)) ?_ 2)
    exact min_le_min_left _ (by gcongr)
  have hsup : ∀ y, ENNReal.ofReal ((1 + HRS.Whole.rieszWeight s (x - y)) ^ 2) = ⨆ n, f n y := fun y => by
    refine le_antisymm ?_ (iSup_le fun n => ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (le_min (hq0 x y) (by positivity)) (min_le_left _ _) 2))
    obtain ⟨n, hn⟩ := exists_nat_ge (1 + HRS.Whole.rieszWeight s (x - y))
    refine le_iSup_of_le n ?_
    simp only [hf]
    rw [min_eq_left (hn.trans (by linarith))]
  simp_rw [hsup]
  rw [lintegral_iSup hfm hmono]
  refine iSup_le fun n => ?_
  have := h2 ((n : ℝ) + 1) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hp : HRS.WeakRef.psi2 d s ((n : ℝ) + 1) = 1 := by
    unfold HRS.WeakRef.psi2; simp [hs]
  rw [hp, mul_one] at this
  exact this


/-- The section bound `∫ ⟨y⟩^P (1 + W_s(x-y)) dμ(y) ≤ A₁`, uniformly in `x` (Cauchy--Schwarz). -/
theorem s95_section (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M C₀ c₀ : ℝ) (hc : 0 < c₀)
    {Pw : ℝ} (hP : 0 ≤ Pw) :
    ∃ A₁ : ℝ, 0 ≤ A₁ ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) → ∀ x : Euc d,
      ∫⁻ y, ENNReal.ofReal (jbracket y ^ Pw * (1 + HRS.Whole.rieszWeight s (x - y))) ∂(HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal A₁ := by
  obtain ⟨CM, hCM, hmom⟩ := s95_moment d C₀ c₀ hc hP
  obtain ⟨AW, hAW, hrow⟩ := s95_row_sq hd hs0 hs M
  refine ⟨CM ^ (1 / (2 : ℝ)) * AW ^ (1 / (2 : ℝ)), by positivity, fun ρ hρ hM hG x => ?_⟩
  have hW0 : ∀ y : Euc d, 0 ≤ 1 + HRS.Whole.rieszWeight s (x - y) := fun y => by
    have := wr3_rieszWeight_nonneg (d := d) s (x - y)
    linarith
  have hJ0 : ∀ y : Euc d, 0 ≤ jbracket y ^ Pw := fun y => Real.rpow_nonneg (zero_le_one.trans (s95_one_le_jb y)) _
  have hF : Measurable (fun y : Euc d => ENNReal.ofReal (jbracket y ^ Pw)) :=
    ENNReal.measurable_ofReal.comp (s95_jb_meas.pow_const Pw)
  have hG' : Measurable (fun y : Euc d => ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.add
      ((wr3_measurable_rieszWeight s).comp (measurable_const.sub measurable_id)))
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (HRS.Whole.withDensityReal ρ) Real.HolderConjugate.two_two
    hF.aemeasurable hG'.aemeasurable
  have e1 : ∀ y : Euc d, ENNReal.ofReal (jbracket y ^ Pw * (1 + HRS.Whole.rieszWeight s (x - y))) =
      ENNReal.ofReal (jbracket y ^ Pw) * ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) :=
    fun y => ENNReal.ofReal_mul (hJ0 y)
  simp_rw [e1]
  refine h.trans ?_
  have e2 : ∫⁻ y, ENNReal.ofReal (jbracket y ^ Pw) ^ (2 : ℝ) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal CM := by
    refine le_trans (le_of_eq (lintegral_congr fun y => s95_ofReal_rpow_two (hJ0 y))) (hmom ρ hρ hG)
  have e3 : ∫⁻ y, ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) ^ (2 : ℝ) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal AW := by
    refine le_trans (le_of_eq (lintegral_congr fun y => s95_ofReal_rpow_two (hW0 y))) (hrow ρ hρ hM x)
  calc _ ≤ (ENNReal.ofReal CM) ^ (1 / (2 : ℝ)) * (ENNReal.ofReal AW) ^ (1 / (2 : ℝ)) :=
        mul_le_mul' (ENNReal.rpow_le_rpow e2 (by norm_num)) (ENNReal.rpow_le_rpow e3 (by norm_num))
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg hCM (by norm_num), ENNReal.ofReal_rpow_of_nonneg hAW (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]


/-! ### Annular cuts and integrability of polynomial-envelope kernels -/

/-- `1_{lo < max(|x|,|y|) ≤ hi} g`. -/
def s95_cut (lo hi : ℝ) (g : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  if lo < max ‖x‖ ‖y‖ ∧ max ‖x‖ ‖y‖ ≤ hi then g x y else 0

theorem s95_cut_meas {g : Euc d → Euc d → ℝ} (hg : Measurable fun p : Euc d × Euc d => g p.1 p.2) (lo hi : ℝ) :
    Measurable fun p : Euc d × Euc d => s95_cut lo hi g p.1 p.2 := by
  unfold s95_cut
  refine Measurable.ite ?_ hg measurable_const
  exact (measurableSet_lt measurable_const (measurable_fst.norm.max measurable_snd.norm)).inter
    (measurableSet_le (measurable_fst.norm.max measurable_snd.norm) measurable_const)

theorem s95_cut_symm {g : Euc d → Euc d → ℝ} (hs : ∀ x y, g x y = g y x) (lo hi : ℝ) (x y : Euc d) :
    s95_cut lo hi g x y = s95_cut lo hi g y x := by
  unfold s95_cut
  rw [max_comm ‖y‖ ‖x‖, hs x y]

theorem s95_jb_le (x : Euc d) : jbracket x ≤ 1 + ‖x‖ := by
  unfold jbracket
  exact Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [norm_nonneg x]⟩

theorem s95_cut_bounded {s Pw Bg : ℝ} (hP : 0 ≤ Pw) {g : Euc d → Euc d → ℝ}
    (hg : IsR2PolyPairKernel s Pw Bg g) (lo : ℝ) {hi : ℝ} (hhi : 0 ≤ hi) (hB : 0 ≤ Bg) :
    IsBoundedPairKernel s (Bg * 2 ^ Pw * (1 + hi) ^ Pw) (s95_cut lo hi g) where
  measurable := s95_cut_meas hg.measurable lo hi
  symm := s95_cut_symm hg.symm lo hi
  bound x y hxy := by
    have hW := wr3_rieszWeight_nonneg (d := d) s (x - y)
    unfold s95_cut
    split_ifs with h
    · have hx : ‖x‖ ≤ hi := (le_max_left _ _).trans h.2
      have hy : ‖y‖ ≤ hi := (le_max_right _ _).trans h.2
      have h1 := hg.bound x y hxy
      have h2 : (jbracket x + jbracket y) ^ Pw ≤ 2 ^ Pw * (1 + hi) ^ Pw := by
        rw [← Real.mul_rpow (by norm_num) (by linarith)]
        exact Real.rpow_le_rpow (by linarith [s95_one_le_jb x, s95_one_le_jb y])
          (by linarith [s95_jb_le x, s95_jb_le y]) hP
      calc |g x y| ≤ Bg * (jbracket x + jbracket y) ^ Pw * (1 + HRS.Whole.rieszWeight s (x - y)) := h1
        _ ≤ Bg * (2 ^ Pw * (1 + hi) ^ Pw) * (1 + HRS.Whole.rieszWeight s (x - y)) := by gcongr
        _ = _ := by ring
    · simp only [abs_zero]
      positivity

/-- Sections, and the pair integral, of a polynomial-envelope kernel. -/
theorem s95_poly_int (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M C₀ c₀ : ℝ) (hc : 0 < c₀)
    {Pw : ℝ} (hP : 0 ≤ Pw) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) → ∀ B : ℝ, 0 ≤ B → ∀ g : Euc d → Euc d → ℝ,
      IsR2PolyPairKernel s Pw B g →
      (∀ x, ∫⁻ y, ‖g x y‖ₑ ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal (A * B * jbracket x ^ Pw)) ∧
      ∫⁻ p : Euc d × Euc d, ‖g p.1 p.2‖ₑ ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) ≤
        ENNReal.ofReal (A * B) := by
  obtain ⟨A₁, hA₁, hsec⟩ := s95_section hd hs0 hs M C₀ c₀ hc hP
  obtain ⟨CM, hCM, hmom⟩ := s95_moment d C₀ c₀ hc hP
  set A₂ : ℝ := 2 ^ Pw * A₁ with hA₂
  have hA₂0 : 0 ≤ A₂ := by positivity
  refine ⟨A₂ * (1 + CM), by positivity, fun ρ hρ hM hG B hB g hg => ?_⟩
  have hsecx : ∀ x, ∫⁻ y, ‖g x y‖ₑ ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal (A₂ * B * jbracket x ^ Pw) := by
    intro x
    have hJ0 : ∀ y : Euc d, 0 ≤ jbracket y ^ Pw := fun y => Real.rpow_nonneg (zero_le_one.trans (s95_one_le_jb y)) _
    have hpt : ∀ y : Euc d, y ≠ x → ‖g x y‖ₑ ≤ ENNReal.ofReal (B * 2 ^ Pw * jbracket x ^ Pw) *
        ENNReal.ofReal (jbracket y ^ Pw * (1 + HRS.Whole.rieszWeight s (x - y))) := by
      intro y hy
      have hW := wr3_rieszWeight_nonneg (d := d) s (x - y)
      have hJx : 0 ≤ jbracket x ^ Pw := Real.rpow_nonneg (zero_le_one.trans (s95_one_le_jb x)) _
      rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hB (by positivity)) hJx), Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := hg.bound x y (Ne.symm hy)
      have hx1 := s95_one_le_jb x
      have hy1 := s95_one_le_jb y
      have h2 : (jbracket x + jbracket y) ^ Pw ≤ 2 ^ Pw * (jbracket x ^ Pw * jbracket y ^ Pw) := by
        rw [← Real.mul_rpow (by linarith) (by linarith), ← Real.mul_rpow (by norm_num) (by positivity)]
        exact Real.rpow_le_rpow (by linarith) (by nlinarith) hP
      calc |g x y| ≤ B * (jbracket x + jbracket y) ^ Pw * (1 + HRS.Whole.rieszWeight s (x - y)) := h1
        _ ≤ B * (2 ^ Pw * (jbracket x ^ Pw * jbracket y ^ Pw)) * (1 + HRS.Whole.rieszWeight s (x - y)) := by gcongr
        _ = _ := by ring
    calc ∫⁻ y, ‖g x y‖ₑ ∂(HRS.Whole.withDensityReal ρ)
        ≤ ∫⁻ y, ENNReal.ofReal (B * 2 ^ Pw * jbracket x ^ Pw) *
          ENNReal.ofReal (jbracket y ^ Pw * (1 + HRS.Whole.rieszWeight s (x - y))) ∂(HRS.Whole.withDensityReal ρ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [wr3_ae_ne hd ρ x] with y hy
          exact hpt y hy
      _ = ENNReal.ofReal (B * 2 ^ Pw * jbracket x ^ Pw) * ∫⁻ y,
          ENNReal.ofReal (jbracket y ^ Pw * (1 + HRS.Whole.rieszWeight s (x - y))) ∂(HRS.Whole.withDensityReal ρ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (B * 2 ^ Pw * jbracket x ^ Pw) * ENNReal.ofReal A₁ := by
          gcongr
          exact hsec ρ hρ hM hG x
      _ = _ := by
          have hJx : 0 ≤ jbracket x ^ Pw := Real.rpow_nonneg (zero_le_one.trans (s95_one_le_jb x)) _
          rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hB (by positivity)) hJx)]
          congr 1
          rw [hA₂]; ring
  refine ⟨fun x => (hsecx x).trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · have : 0 ≤ B * jbracket x ^ Pw := mul_nonneg hB (Real.rpow_nonneg (zero_le_one.trans (s95_one_le_jb x)) _)
    nlinarith [mul_nonneg hA₂0 hCM, mul_nonneg hA₂0 this]
  · have := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
    have hm : AEMeasurable (fun p : Euc d × Euc d => ‖g p.1 p.2‖ₑ)
        ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := hg.measurable.enorm.aemeasurable
    rw [lintegral_prod _ hm]
    calc ∫⁻ x, ∫⁻ y, ‖g x y‖ₑ ∂(HRS.Whole.withDensityReal ρ) ∂(HRS.Whole.withDensityReal ρ)
        ≤ ∫⁻ x, ENNReal.ofReal (A₂ * B) * ENNReal.ofReal (jbracket x ^ Pw) ∂(HRS.Whole.withDensityReal ρ) := by
          refine lintegral_mono fun x => (hsecx x).trans (le_of_eq ?_)
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (A₂ * B) * ∫⁻ x, ENNReal.ofReal (jbracket x ^ Pw) ∂(HRS.Whole.withDensityReal ρ) :=
          lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (s95_jb_meas.pow_const Pw))
      _ ≤ ENNReal.ofReal (A₂ * B) * ENNReal.ofReal CM := by
          gcongr
          refine le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_) (hmom ρ hρ hG)
          have h1 : 1 ≤ jbracket x ^ Pw := Real.one_le_rpow (s95_one_le_jb x) hP
          nlinarith
      _ = ENNReal.ofReal (A₂ * B * CM) := (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [mul_nonneg hA₂0 hB, mul_nonneg (mul_nonneg hA₂0 hB) hCM]


/-! ### Interpolation between an `L²(ν)` bound and a higher moment under `ν.withDensity ψ` -/

theorem s95_sqrt_pow4 {t : ℝ} (ht : 0 ≤ t) : (t ^ 4) ^ (1 / (2 : ℝ)) = t ^ 2 := by
  rw [← Real.sqrt_eq_rpow, show t ^ 4 = (t ^ 2) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

theorem s95_interp {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν] {ψ : α → ℝ≥0∞}
    (hψ : Measurable ψ) [IsProbabilityMeasure (ν.withDensity ψ)] {X : α → ℝ} (hX : Measurable X) {m : ℕ}
    (hm : 1 ≤ m) {C2 Aψ σ : ℝ} (hC2 : 0 ≤ C2) (hA : 0 ≤ Aψ) (hσ : 0 < σ)
    (hC2' : ∫⁻ x, ‖X x‖ₑ ^ (2 * m) ∂(ν.withDensity ψ) ≤ ENNReal.ofReal C2)
    (hAψ : (∫⁻ x, ψ x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal Aψ)
    (hs : ∫⁻ x, ‖X x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal σ) :
    ∫⁻ x, ‖X x‖ₑ ^ m ∂(ν.withDensity ψ) ≤
      ENNReal.ofReal ((1 + C2 + Real.sqrt C2 * Real.sqrt Aψ) * σ ^ (1 / 8 : ℝ)) := by
  set τ : ℝ := σ ^ (1 / 8 : ℝ) with hτ
  have hτ0 : 0 < τ := Real.rpow_pos_of_pos hσ _
  have hτ8 : τ ^ 8 = σ := by
    rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul hσ.le]; norm_num
  have hC : 0 ≤ Real.sqrt C2 * Real.sqrt Aψ := by positivity
  rcases le_or_gt σ 1 with h1 | h1
  · have hτ1 : τ ≤ 1 := Real.rpow_le_one hσ.le h1 (by norm_num)
    set ε : ℝ := τ ^ 2 with hε
    have hε0 : 0 < ε := by positivity
    have h := s92_tail_Q ν hψ hX m hε0 hC2' hAψ hs
    refine h.trans ?_
    have e1 : ENNReal.ofReal (ε ^ (-2 : ℤ)) * ENNReal.ofReal σ = ENNReal.ofReal (τ ^ 4) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [hε, ← hτ8, zpow_neg, zpow_two]
      field_simp
      try ring
    rw [e1, ENNReal.ofReal_rpow_of_nonneg (x := τ ^ 4) (by positivity) (by norm_num), s95_sqrt_pow4 hτ0.le,
      ← ENNReal.ofReal_mul hA, ENNReal.ofReal_rpow_of_nonneg (x := Aψ * τ ^ 2) (by positivity) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (x := C2) hC2 (by norm_num), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_pow hε0.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h3 : (Aψ * τ ^ 2) ^ (1 / (2 : ℝ)) = Real.sqrt Aψ * τ := by
      rw [Real.mul_rpow hA (by positivity), ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq hτ0.le]
    rw [h3, ← Real.sqrt_eq_rpow]
    have h4 : ε ^ m ≤ τ := by
      calc ε ^ m = τ ^ (2 * m) := by rw [hε, ← pow_mul]
        _ ≤ τ ^ 1 := pow_le_pow_of_le_one hτ0.le hτ1 (by omega)
        _ = τ := pow_one τ
    nlinarith [mul_nonneg hC hτ0.le, mul_nonneg hC2 hτ0.le]
  · have hτ1 : 1 ≤ τ := Real.one_le_rpow h1.le (by norm_num)
    have hpt : ∀ x, ‖X x‖ₑ ^ m ≤ 1 + ‖X x‖ₑ ^ (2 * m) := fun x => by
      rcases le_or_gt ‖X x‖ₑ 1 with h | h
      · exact (pow_le_one' h m).trans le_self_add
      · exact (pow_le_pow_right' h.le (by omega)).trans le_add_self
    calc ∫⁻ x, ‖X x‖ₑ ^ m ∂(ν.withDensity ψ) ≤ ∫⁻ x, (1 + ‖X x‖ₑ ^ (2 * m)) ∂(ν.withDensity ψ) :=
          lintegral_mono hpt
      _ = 1 + ∫⁻ x, ‖X x‖ₑ ^ (2 * m) ∂(ν.withDensity ψ) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ 1 + ENNReal.ofReal C2 := by gcongr
      _ = ENNReal.ofReal (1 + C2) := by rw [ENNReal.ofReal_add (by norm_num) hC2, ENNReal.ofReal_one]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [mul_nonneg hC hτ0.le, mul_nonneg hC2 hτ0.le]


/-! ### The quantitative `L^r(P_N)` bound for a bounded-class kernel with small `L²(μ⊗μ)` mass -/

theorem s95_F_small (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L b p K r : ℝ)
    (hb : 0 < b) (hp : 1 < p) (hr : 1 ≤ r) :
    ∃ Cr κ : ℝ, 0 ≤ Cr ∧ 0 < κ ∧ ∀ ρ : Euc d → ℝ, IsRound2Density d s M L ρ → ∀ N : ℕ, 2 ≤ N →
      ∀ P : Measure (EucConfig d N), HasR2ActualDensity s b p K (HRS.Whole.withDensityReal ρ) P →
      ∀ k : Euc d → Euc d → ℝ, IsBoundedPairKernel s 1 k → ∀ σ : ℝ, 0 < σ →
      ∫⁻ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂(HRS.Whole.withDensityReal ρ) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal σ →
      eLpNorm (fun X : EucConfig d N => (N : ℝ) * pairEnergy k X (HRS.Whole.withDensityReal ρ))
        (ENNReal.ofReal r) P ≤ ENNReal.ofReal (Cr * σ ^ κ) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hd1 : 1 ≤ d := by omega
  have hcp : 1 < Real.conjExponent p := (Real.HolderConjugate.conjExponent hp).symm.lt
  set t : ℝ := r * Real.conjExponent p with ht
  have ht0 : 0 < t := mul_pos (by linarith) (by linarith)
  set m : ℕ := ⌈t⌉₊ with hm
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_lt_of_le ht0 (Nat.le_ceil t)
    exact_mod_cast this
  obtain ⟨C2, hC2nn, hC2⟩ := s92_moment_Q hd hs0 hs M L b 1 hb (2 * m)
  obtain ⟨C0, hC0, hnorm⟩ := s92_normalizer_bounds hd hs0 hs M L b (2 * b) hb (by linarith)
  set K' : ℝ := max K 0 with hK'
  set Aψ : ℝ := Real.exp (3 * C0 / 2) with hAψ
  have hAψ0 : 0 ≤ Aψ := (Real.exp_pos _).le
  set Cint : ℝ := (1 + C2 + Real.sqrt C2 * Real.sqrt Aψ) * (100 : ℝ) ^ (1 / 8 : ℝ) with hCint
  have hCint0 : 0 ≤ Cint := by positivity
  refine ⟨K' ^ (1 / r) * Cint ^ (1 / (m : ℝ)), 1 / (8 * (m : ℝ)), by positivity, by positivity,
    fun ρ hρ N hN P hP k hk σ hσ hS => ?_⟩
  haveI hμ := s92_isProb_mu hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  have hN0 : 0 < N := by omega
  obtain ⟨hsec, hint, hHint⟩ := s92_kernel_integrable hd1 hs0 hsd M hρ.prob hρ.bdd hk
  have hW := (hnorm ρ hρ N hN b ⟨le_rfl, by linarith⟩).1
  have hW2 := (hnorm ρ hρ N hN (2 * b) ⟨by linarith, le_rfl⟩).1
  have hl1 := (hnorm ρ hρ N hN b ⟨le_rfl, by linarith⟩).2
  have hl2 := (hnorm ρ hρ N hN (2 * b) ⟨by linarith, le_rfl⟩).2
  haveI hQprob := s92_isProb_Q (N := N) hW
  haveI hPprob : IsProbabilityMeasure P := hP.1
  have hXm : Measurable (fun X : EucConfig d N => (N : ℝ) * pairEnergy k X μ) :=
    measurable_const.mul (wr9_measurable_pairEnergy hk.measurable)
  have h2 := s92_second_moment (N := N) hk.measurable hk.symm hsec hint hHint hN0
  have hs2 : ∫⁻ X : EucConfig d N, ‖(N : ℝ) * pairEnergy k X μ‖ₑ ^ 2 ∂(Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (100 * σ) := by
    calc _ ≤ 100 * ∫⁻ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂μ ∂μ := h2
      _ ≤ 100 * ENNReal.ofReal σ := by gcongr
      _ = ENNReal.ofReal (100 * σ) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num
  have hQeq : HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ =
      pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ := rfl
  have hGm := wr9_rieszKernel_pair_meas (d := d) s
  have hψm := s92_dens_meas (μ := μ) (N := N) hGm b
  have hdens := s92_pairGibbs_eq (N := N) hGm hW
  have hmom := hC2 ρ hρ k hk N hN
  rw [hQeq, hdens] at hmom
  have hA := s92_psi_L2 hW hW2 hl1 hl2
  haveI : IsProbabilityMeasure ((Measure.pi fun _ : Fin N => μ).withDensity
      (s92_dens (fun x y => rieszKernel d s (x - y)) N b μ)) := by
    rw [← hdens]; exact hQprob
  have hI := s95_interp (Measure.pi fun _ : Fin N => μ) hψm hXm hm1 hC2nn hAψ0 (by positivity : 0 < 100 * σ)
    hmom hA hs2
  have hE : (1 + C2 + Real.sqrt C2 * Real.sqrt Aψ) * (100 * σ) ^ (1 / 8 : ℝ) = Cint * σ ^ (1 / 8 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hσ.le, hCint]; ring
  rw [hE] at hI
  have hE0 : 0 ≤ Cint * σ ^ (1 / 8 : ℝ) := by positivity
  have hQb0 := s92_eLpNorm_le_of_moment ((Measure.pi fun _ : Fin N => μ).withDensity
    (s92_dens (fun x y => rieszKernel d s (x - y)) N b μ)) hXm ht0 m (Nat.le_ceil t) hE0 hI
  rw [← hdens, ← hQeq] at hQb0
  have hdensP : eLpNorm (fun X => ((P.rnDeriv (HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ) X).toReal))
      (ENNReal.ofReal p) (HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ) ≤ ENNReal.ofReal K' :=
    hP.2.2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hPb := s92_transfer _ P hP.2.1 hp (le_max_right _ _) hdensP hXm (by linarith : 0 < r) hQb0
  refine hPb.trans (le_of_eq ?_)
  congr 1
  rw [Real.mul_rpow hCint0 (by positivity), ← Real.rpow_mul hσ.le]
  have : (1 / 8 : ℝ) * (1 / (m : ℝ)) = 1 / (8 * (m : ℝ)) := by field_simp
  rw [this]
  ring


/-! ### `L²(μ⊗μ)` mass of an annular kernel -/

theorem s95_ann_core {s : ℝ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ] {A : ℝ}
    (hrow : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal ((1 + HRS.Whole.rieszWeight s (x - y)) ^ 2) ∂μ ≤ ENNReal.ofReal A)
    (hae : ∀ x : Euc d, ∀ᵐ y ∂μ, y ≠ x) (u : Euc d → Euc d → ℝ) (t : ℝ)
    (hu : ∀ x y, x ≠ y → |u x y| ≤ if t < max ‖x‖ ‖y‖ then 1 + HRS.Whole.rieszWeight s (x - y) else 0) :
    ∫⁻ x, ∫⁻ y, ‖u x y‖ₑ ^ 2 ∂μ ∂μ ≤ ENNReal.ofReal A * (2 * μ {x | t < ‖x‖}) := by
  obtain ⟨S, hS⟩ : ∃ S : Set (Euc d), S = {x | t < ‖x‖} := ⟨_, rfl⟩
  rw [← hS]
  have hSm : MeasurableSet S := hS ▸ measurableSet_lt measurable_const measurable_norm
  obtain ⟨ind, hind⟩ : ∃ ind : Euc d → ℝ≥0∞, ind = S.indicator (fun _ => (1 : ℝ≥0∞)) := ⟨_, rfl⟩
  have hindm : Measurable ind := hind ▸ measurable_const.indicator hSm
  obtain ⟨q, hq⟩ : ∃ q : Euc d → Euc d → ℝ≥0∞,
      q = fun x y => ENNReal.ofReal ((1 + HRS.Whole.rieszWeight s (x - y)) ^ 2) := ⟨_, rfl⟩
  have hqm : Measurable (fun p : Euc d × Euc d => q p.1 p.2) := by
    rw [hq]
    exact ENNReal.measurable_ofReal.comp ((measurable_const.add
      ((wr3_measurable_rieszWeight s).comp (measurable_fst.sub measurable_snd))).pow_const 2)
  have hqy : ∀ x, Measurable (q x) := fun x => hqm.comp measurable_prodMk_left
  have hqx : ∀ y, Measurable (fun x => q x y) := fun y => hqm.comp measurable_prodMk_right
  have hrow' : ∀ x, ∫⁻ y, q x y ∂μ ≤ ENNReal.ofReal A := fun x => by rw [hq]; exact hrow x
  have hpt : ∀ x y : Euc d, x ≠ y → ‖u x y‖ₑ ^ 2 ≤ ind x * q x y + ind y * q x y := by
    intro x y hxy
    have h1 := hu x y hxy
    have hW := wr3_rieszWeight_nonneg (d := d) s (x - y)
    rw [s92_enorm_sq]
    by_cases ht : t < max ‖x‖ ‖y‖
    · rw [if_pos ht] at h1
      have hb : 1 ≤ ind x + ind y := by
        rcases lt_max_iff.1 ht with h | h
        · rw [hind, Set.indicator_of_mem (show x ∈ S by rw [hS]; exact h)]; exact le_self_add
        · rw [hind, Set.indicator_of_mem (show y ∈ S by rw [hS]; exact h)]; exact le_add_self
      have hle : u x y ^ 2 ≤ (1 + HRS.Whole.rieszWeight s (x - y)) ^ 2 := by
        have := sq_abs (u x y)
        nlinarith [abs_nonneg (u x y)]
      calc ENNReal.ofReal (u x y ^ 2) ≤ q x y := by rw [hq]; exact ENNReal.ofReal_le_ofReal hle
        _ = 1 * q x y := (one_mul _).symm
        _ ≤ (ind x + ind y) * q x y := by gcongr
        _ = _ := add_mul _ _ _
    · rw [if_neg ht] at h1
      have : u x y = 0 := abs_nonpos_iff.1 h1
      simp [this]
  have hrowy : ∀ y : Euc d, ∫⁻ x, q x y ∂μ ≤ ENNReal.ofReal A := fun y => by
    refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) (hrow y)
    rw [hq]
    simp only
    rw [wr14a_W_sub_comm]
  have hint : ∫⁻ x, ind x * ENNReal.ofReal A ∂μ = ENNReal.ofReal A * μ S := by
    rw [lintegral_mul_const _ hindm, hind, lintegral_indicator_const hSm, one_mul, mul_comm]
  have hmy : Measurable fun p : Euc d × Euc d => ind p.1 * q p.1 p.2 := (hindm.comp measurable_fst).mul hqm
  have hmy2 : Measurable fun p : Euc d × Euc d => ind p.2 * q p.1 p.2 := (hindm.comp measurable_snd).mul hqm
  have P1 : ∫⁻ x, ∫⁻ y, ind x * q x y ∂μ ∂μ ≤ ENNReal.ofReal A * μ S := by
    calc ∫⁻ x, ∫⁻ y, ind x * q x y ∂μ ∂μ = ∫⁻ x, ind x * ∫⁻ y, q x y ∂μ ∂μ :=
          lintegral_congr fun x => lintegral_const_mul _ (hqy x)
      _ ≤ ∫⁻ x, ind x * ENNReal.ofReal A ∂μ := lintegral_mono fun x => by gcongr; exact hrow' x
      _ = _ := hint
  have P2 : ∫⁻ x, ∫⁻ y, ind y * q x y ∂μ ∂μ ≤ ENNReal.ofReal A * μ S := by
    calc ∫⁻ x, ∫⁻ y, ind y * q x y ∂μ ∂μ = ∫⁻ y, ∫⁻ x, ind y * q x y ∂μ ∂μ :=
          lintegral_lintegral_swap hmy2.aemeasurable
      _ = ∫⁻ y, ind y * ∫⁻ x, q x y ∂μ ∂μ :=
          lintegral_congr fun y => lintegral_const_mul _ (hqx y)
      _ ≤ ∫⁻ y, ind y * ENNReal.ofReal A ∂μ := lintegral_mono fun y => by gcongr; exact hrowy y
      _ = _ := hint
  calc ∫⁻ x, ∫⁻ y, ‖u x y‖ₑ ^ 2 ∂μ ∂μ
      ≤ ∫⁻ x, ∫⁻ y, (ind x * q x y + ind y * q x y) ∂μ ∂μ := by
        refine lintegral_mono fun x => lintegral_mono_ae ?_
        filter_upwards [hae x] with y hy
        exact hpt x y (Ne.symm hy)
    _ = ∫⁻ x, ∫⁻ y, ind x * q x y ∂μ ∂μ + ∫⁻ x, ∫⁻ y, ind y * q x y ∂μ ∂μ := by
        rw [← lintegral_add_left hmy.lintegral_prod_right']
        refine lintegral_congr fun x => ?_
        rw [lintegral_add_left ((hqy x).const_mul _)]
    _ ≤ ENNReal.ofReal A * μ S + ENNReal.ofReal A * μ S := add_le_add P1 P2
    _ = _ := by ring

theorem s95_ann_L2 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ (u : Euc d → Euc d → ℝ) (t : ℝ),
      (∀ x y, x ≠ y → |u x y| ≤ if t < max ‖x‖ ‖y‖ then 1 + HRS.Whole.rieszWeight s (x - y) else 0) →
      ∫⁻ x, ∫⁻ y, ‖u x y‖ₑ ^ 2 ∂(HRS.Whole.withDensityReal ρ) ∂(HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal A * (2 * HRS.Whole.withDensityReal ρ {x | t < ‖x‖}) := by
  obtain ⟨A, hA, hrow⟩ := s95_row_sq hd hs0 hs M
  refine ⟨A, hA, fun ρ hρ hM u t hu => ?_⟩
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  exact s95_ann_core _ (hrow ρ hρ hM) (wr3_ae_ne hd ρ) u t hu


/-- The tail of `μ` at the annulus radius `k - 1`: exponential in `k`. -/
theorem s95_tail_k (d : ℕ) (C₀ c₀ : ℝ) (hc : 0 < c₀) :
    ∃ Gk : ℝ, 1 ≤ Gk ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) →
      ∀ k : ℕ, HRS.Whole.withDensityReal ρ {x | (k : ℝ) - 1 < ‖x‖} ≤
        ENNReal.ofReal (Gk * Real.exp (-(c₀ * k / 2))) := by
  obtain ⟨G, hG0, hG⟩ := s95_tail d C₀ c₀ hc
  refine ⟨max 1 (G * Real.exp (c₀ / 2)), le_max_left _ _, fun ρ hρ hgauss k => ?_⟩
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  rcases k with _ | j
  · refine (prob_le_one).trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    simpa using le_max_left (1 : ℝ) (G * Real.exp (c₀ / 2))
  · have hj : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    refine (hG ρ hgauss _ hj).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : (j : ℝ) ≤ (j : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) j
    have h2 : -(c₀ * (((j + 1 : ℕ) : ℝ) - 1) ^ 2 / 2) ≤ c₀ / 2 + -(c₀ * ((j + 1 : ℕ) : ℝ) / 2) := by
      push_cast
      nlinarith
    calc G * Real.exp (-(c₀ * (((j + 1 : ℕ) : ℝ) - 1) ^ 2 / 2))
        ≤ G * (Real.exp (c₀ / 2) * Real.exp (-(c₀ * ((j + 1 : ℕ) : ℝ) / 2))) := by
          rw [← Real.exp_add]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hG0
      _ = (G * Real.exp (c₀ / 2)) * Real.exp (-(c₀ * ((j + 1 : ℕ) : ℝ) / 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- `L²(μ⊗μ)` mass of a kernel supported (up to the envelope) on the `k`-th annulus complement. -/
theorem s95_sigma (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M C₀ c₀ : ℝ) (hc : 0 < c₀) :
    ∃ Aσ : ℝ, 0 ≤ Aσ ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) → ∀ (u : Euc d → Euc d → ℝ) (k : ℕ),
      (∀ x y, x ≠ y → |u x y| ≤ if (k : ℝ) - 1 < max ‖x‖ ‖y‖ then 1 + HRS.Whole.rieszWeight s (x - y) else 0) →
      ∫⁻ x, ∫⁻ y, ‖u x y‖ₑ ^ 2 ∂(HRS.Whole.withDensityReal ρ) ∂(HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal (Aσ * Real.exp (-(c₀ * k / 2))) := by
  obtain ⟨A, hA, hL2⟩ := s95_ann_L2 hd hs0 hs M
  obtain ⟨Gk, hGk, htail⟩ := s95_tail_k d C₀ c₀ hc
  refine ⟨2 * A * Gk, by positivity, fun ρ hρ hM hgauss u k hu => ?_⟩
  refine (hL2 ρ hρ hM u _ hu).trans ?_
  calc ENNReal.ofReal A * (2 * HRS.Whole.withDensityReal ρ {x | (k : ℝ) - 1 < ‖x‖})
      ≤ ENNReal.ofReal A * (2 * ENNReal.ofReal (Gk * Real.exp (-(c₀ * k / 2)))) := by
        gcongr
        exact htail ρ hρ hgauss k
    _ = ENNReal.ofReal (A * (2 * (Gk * Real.exp (-(c₀ * k / 2))))) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hA]
    _ = _ := by congr 1; ring

end HRS.MS.R2Poly
