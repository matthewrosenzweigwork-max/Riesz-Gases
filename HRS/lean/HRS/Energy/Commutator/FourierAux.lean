import HRS.Energy.Commutator.HeatAux

/-!
# Fourier calculus for the regularised stress argument (packet CM-S3 helpers)

Real cosine series `ser w = ∑_k w_k cos(2π k·x)` with Gaussian-decaying even weights, their
smoothness, Fourier coefficients and convolution with weighted finite measures.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate
open HRS HRS.KernelAux

namespace HRS.Commutator.FourierAux

variable {d : ℕ}

/-- The real cosine series `x ↦ ∑_k w_k cos(2π k·x)`. -/
def ser (w : Lattice d → ℝ) (x : Torus d) : ℝ := ∑' k, w k * Torus.cosMode k x

/-- The complex coefficient sequence of a real weight. -/
def cf (w : Lattice d → ℝ) : PDE.Coeff d := fun k => (w k : ℂ)

theorem summable_cf (w : Lattice d → ℝ) (hw : Summable fun k => |w k|) :
    Summable fun k => ‖cf w k‖ := hw.congr fun k => by simp [cf]

theorem ser_eq_toFun {w : Lattice d → ℝ} (hw : Summable fun k => |w k|) :
    ser w = PDE.toFun (cf w) := by
  funext x
  unfold ser PDE.toFun PDE.series
  have hs := PDE.summable_series_terms (cf w) (summable_cf w hw) x
  rw [Complex.re_tsum hs]
  refine tsum_congr fun k => ?_
  simp [cf, Torus.cosMode]

theorem isRealCoeff_cf {w : Lattice d → ℝ} (heven : ∀ k, w (-k) = w k) : PDE.IsRealCoeff (cf w) := by
  intro k
  simp [cf, heven k]

theorem continuous_ser {w : Lattice d → ℝ} (hw : Summable fun k => |w k|) : Continuous (ser w) := by
  unfold ser
  refine continuous_tsum (u := fun k => |w k|) (fun k => continuous_const.mul (Torus.continuous_cosMode k))
    hw (fun k x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |w k| * |Torus.cosMode k x| ≤ |w k| * 1 := by
        gcongr; exact HRS.abs_cosMode_le k x
    _ = _ := mul_one _

theorem coeffOf_ser {w : Lattice d → ℝ} (hw : Summable fun k => |w k|) (heven : ∀ k, w (-k) = w k) :
    PDE.coeffOf (ser w) = cf w := by
  rw [ser_eq_toFun hw]
  exact PDE.coeffOf_toFun (cf w) (isRealCoeff_cf heven) (summable_cf w hw)

theorem ser_neg (w : Lattice d → ℝ) (x : Torus d) : ser w (-x) = ser w x := by
  unfold ser
  simp only [EnergyAux.cosMode_neg']


/-! ### Smoothness of Gaussian-decaying series -/

theorem one_add_mul_exp_le {δ : ℝ} (hδ : 0 < δ) {y : ℝ} (hy : 0 ≤ y) :
    (1 + y) * Real.exp (-(δ * y)) ≤ 1 + 1 / δ := by
  have h1 : Real.exp (-(δ * y)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
  have h2 : y * Real.exp (-(δ * y)) ≤ 1 / δ := by
    have h3 : (δ * y) * Real.exp (-(δ * y)) ≤ 1 := by
      have := Real.add_one_le_exp (δ * y)
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
      linarith
    rw [le_div_iff₀ hδ]
    nlinarith
  nlinarith [Real.exp_pos (-(δ * y))]

theorem pow_le_exp_mul (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) {y : ℝ} (hy : 0 ≤ y) :
    (1 + y) ^ n ≤ (1 + n / ε) ^ n * Real.exp (ε * y) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ : 0 < ε / n := div_pos hε hn'
  have h := one_add_mul_exp_le hδ hy
  have h0 : 0 ≤ (1 + y) * Real.exp (-(ε / n * y)) := mul_nonneg (by linarith) (Real.exp_pos _).le
  have h1 := pow_le_pow_left₀ h0 h n
  have e1 : ((1 + y) * Real.exp (-(ε / n * y))) ^ n = (1 + y) ^ n * Real.exp (-(ε * y)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    field_simp
  have e2 : (1 + 1 / (ε / n)) = 1 + n / ε := by field_simp
  rw [e1, e2] at h1
  have h3 : 0 < Real.exp (ε * y) := Real.exp_pos _
  have : (1 + y) ^ n = (1 + y) ^ n * Real.exp (-(ε * y)) * Real.exp (ε * y) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  rw [this]
  calc (1 + y) ^ n * Real.exp (-(ε * y)) * Real.exp (ε * y)
      ≤ (1 + n / ε) ^ n * Real.exp (ε * y) := mul_le_mul_of_nonneg_right h1 h3.le

theorem memHs_of_gauss {m : ℝ} (hm : 0 ≤ m) {c : PDE.Coeff d} {ε C : ℝ} (hε : 0 < ε)
    (hw : ∀ k, ‖c k‖ ≤ C * Real.exp (-ε * Lattice.enorm k ^ 2)) : PDE.MemHs m c := by
  set n : ℕ := ⌈m⌉₊ + 1 with hn
  have hn0 : 0 < n := by omega
  have hmn : m ≤ n := by
    have := Nat.le_ceil m
    have h2 : (⌈m⌉₊ : ℝ) ≤ n := by rw [hn]; push_cast; linarith
    linarith
  have hc0 : 0 < 4 * Real.pi ^ 2 := by positivity
  set ε' : ℝ := ε / (4 * Real.pi ^ 2) with hε'
  have hε'0 : 0 < ε' := div_pos hε hc0
  set B : ℝ := (1 + n / ε') ^ n with hB
  unfold PDE.MemHs
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
    (fun k => ?_) ((summable_gauss_lattice d ε hε).mul_left (B * C ^ 2))
  have hy : 0 ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
  have h1 : PDE.sobWeight m k ≤ (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ n := by
    unfold PDE.sobWeight
    calc (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ m
        ≤ (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ (n : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hmn
      _ = _ := Real.rpow_natCast _ n
  have h2 := pow_le_exp_mul n hn0 hε'0 hy
  have h3 : ‖c k‖ ^ 2 ≤ C ^ 2 * Real.exp (-(2 * ε) * Lattice.enorm k ^ 2) := by
    have := hw k
    calc ‖c k‖ ^ 2 ≤ (C * Real.exp (-ε * Lattice.enorm k ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = C ^ 2 * Real.exp (-(2 * ε) * Lattice.enorm k ^ 2) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  calc PDE.sobWeight m k * ‖c k‖ ^ 2
      ≤ ((1 + n / ε') ^ n * Real.exp (ε' * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2))) *
        (C ^ 2 * Real.exp (-(2 * ε) * Lattice.enorm k ^ 2)) :=
        mul_le_mul (h1.trans h2) h3 (sq_nonneg _) (by positivity)
    _ = B * C ^ 2 * Real.exp (-ε * Lattice.enorm k ^ 2) := by
        rw [hB]
        have : Real.exp (ε' * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)) *
            Real.exp (-(2 * ε) * Lattice.enorm k ^ 2) = Real.exp (-ε * Lattice.enorm k ^ 2) := by
          rw [← Real.exp_add]; congr 1
          rw [hε']; field_simp; ring
        calc (1 + n / ε') ^ n * Real.exp (ε' * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)) *
              (C ^ 2 * Real.exp (-(2 * ε) * Lattice.enorm k ^ 2))
            = (1 + n / ε') ^ n * C ^ 2 * (Real.exp (ε' * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)) *
              Real.exp (-(2 * ε) * Lattice.enorm k ^ 2)) := by ring
          _ = _ := by rw [this]

theorem isCk_ser (j : ℕ) {w : Lattice d → ℝ} {ε C : ℝ} (hε : 0 < ε)
    (hw : ∀ k, |w k| ≤ C * Real.exp (-ε * Lattice.enorm k ^ 2)) (heven : ∀ k, w (-k) = w k) :
    Torus.IsCk j (ser w) := by
  have hsum : Summable fun k => |w k| :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hw ((summable_gauss_lattice d ε hε).mul_left C)
  have hm : (d : ℝ) / 2 + j < (d : ℝ) / 2 + j + 1 := by linarith
  obtain ⟨C', hC'⟩ := PDE.toFun_isCk_le (d := d) j ((d : ℝ) / 2 + j + 1) hm
  have hmh := memHs_of_gauss (m := (d : ℝ) / 2 + j + 1) (by positivity) hε
    (c := cf w) (C := C) (fun k => by simpa [cf] using hw k)
  rw [ser_eq_toFun hsum]
  exact (hC' (cf w) hmh (isRealCoeff_cf heven)).1

theorem mode_at_zero (k : Lattice d) : Torus.mode k (0 : Torus d) = 1 := by
  simp [Torus.mode, UnitAddTorus.mFourier]

theorem mode_neg_arg (k : Lattice d) (y : Torus d) : Torus.mode k (-y) = Torus.mode (-k) y := by
  have h1 := Torus.mode_add_arg k y (-y)
  rw [add_neg_cancel, mode_at_zero] at h1
  have h3 := Torus.mode_neg_lattice k y
  calc Torus.mode k (-y) = Torus.mode k (-y) * (Torus.mode (-k) y * Torus.mode k y) := by rw [h3, mul_one]
    _ = (Torus.mode k y * Torus.mode k (-y)) * Torus.mode (-k) y := by ring
    _ = Torus.mode (-k) y := by rw [← h1, one_mul]

/-- Convolution of a kernel with the weighted measure `s ρ`. -/
def convS (K : Torus d → ℝ) (ρ : Measure (Torus d)) (s : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ y, K (x - y) * s y ∂ρ

/-- Fourier coefficient of the weighted measure `s ρ`. -/
def shat (ρ : Measure (Torus d)) (s : Torus d → ℝ) (k : Lattice d) : ℂ :=
  ∫ y, Torus.mode (-k) y * (s y : ℂ) ∂ρ

theorem norm_shat_le {ρ : Measure (Torus d)} [IsFiniteMeasure ρ] {s : Torus d → ℝ}
    {B : ℝ} (hs : ∀ y, |s y| ≤ B) (k : Lattice d) : ‖shat ρ s k‖ ≤ B * ρ.real Set.univ := by
  unfold shat
  refine (norm_integral_le_of_norm_le_const (C := B) (Filter.Eventually.of_forall fun y => ?_)).trans
    (by simp [Measure.real, mul_comm])
  rw [norm_mul, Torus.norm_mode, one_mul]
  simpa using hs y

theorem shat_neg {ρ : Measure (Torus d)} (s : Torus d → ℝ) (k : Lattice d) :
    shat ρ s (-k) = conj (shat ρ s k) := by
  unfold shat
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [neg_neg, map_mul, Complex.conj_ofReal]
  rw [Torus.mode_neg, Complex.conj_conj]


theorem continuous_convS {K : Torus d → ℝ} (hK : Continuous K) (ρ : Measure (Torus d))
    [IsFiniteMeasure ρ] {s : Torus d → ℝ} (hsm : Measurable s) {B : ℝ} (hs : ∀ y, |s y| ≤ B) :
    Continuous (convS K ρ s) := by
  obtain ⟨BK, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuousOn
  unfold convS
  refine continuous_of_dominated (bound := fun _ => BK * B) (fun x => ?_) (fun x => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun y => ?_)
  · exact ((hK.measurable.comp (measurable_const.sub measurable_id)).mul hsm).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_mul]
    have h1 := hB (x - y) (mem_univ _)
    have h2 : ‖s y‖ ≤ B := by simpa using hs y
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  · exact (hK.comp (continuous_id.sub continuous_const)).mul continuous_const

theorem coeff_convS {K : Torus d → ℝ} (hK : Continuous K) (ρ : Measure (Torus d))
    [IsFiniteMeasure ρ] {s : Torus d → ℝ} (hsm : Measurable s) {B : ℝ} (hs : ∀ y, |s y| ≤ B) (k : Lattice d) :
    Torus.fcoef (convS K ρ s) k = Torus.fcoef K k * shat ρ s k := by
  obtain ⟨BK, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuousOn
  unfold Torus.fcoef convS shat
  have hint : Integrable (Function.uncurry fun (x y : Torus d) =>
      Torus.mode (-k) x * ((K (x - y) * s y : ℝ) : ℂ)) ((volume : Measure (Torus d)).prod ρ) := by
    refine Integrable.mono' (integrable_const (BK * B)) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have h1 : Measurable fun p : Torus d × Torus d => Torus.mode (-k) p.1 :=
        (Torus.continuous_mode (-k)).measurable.comp measurable_fst
      have h2 : Measurable fun p : Torus d × Torus d => ((K (p.1 - p.2) * s p.2 : ℝ) : ℂ) :=
        Complex.measurable_ofReal.comp
          ((hK.measurable.comp (measurable_fst.sub measurable_snd)).mul (hsm.comp measurable_snd))
      exact (h1.mul h2).aestronglyMeasurable
    · simp only [Function.uncurry, norm_mul, Torus.norm_mode, one_mul, Complex.norm_real]
      have h1 := hB (p.1 - p.2) (mem_univ _)
      have h2 : ‖s p.2‖ ≤ B := by simpa using hs p.2
      exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  have h1 : ∀ x : Torus d, Torus.mode (-k) x * (((∫ y, K (x - y) * s y ∂ρ : ℝ)) : ℂ) =
      ∫ y, Torus.mode (-k) x * ((K (x - y) * s y : ℝ) : ℂ) ∂ρ := by
    intro x
    rw [integral_const_mul, integral_complex_ofReal]
  simp_rw [h1]
  rw [integral_integral_swap hint]
  have h2 : ∀ y : Torus d, ∫ x, Torus.mode (-k) x * ((K (x - y) * s y : ℝ) : ℂ) =
      (Torus.fcoef K k * (Torus.mode (-k) y * (s y : ℂ))) := by
    intro y
    have h3 := Torus.fcoef_translate K k (-y)
    simp only [Torus.fcoef] at h3 ⊢
    rw [mode_neg_arg] at h3
    simp only [sub_eq_add_neg] 
    have : ∀ x : Torus d, Torus.mode (-k) x * ((K (x + -y) * s y : ℝ) : ℂ) =
        (s y : ℂ) * (Torus.mode (-k) x * (K (x + -y) : ℂ)) := by
      intro x; push_cast; ring
    simp_rw [this]
    rw [integral_const_mul, h3]
    ring
  simp_rw [h2]
  rw [integral_const_mul]
  rfl


/-- Coefficient sequence of `ser w ⋆ (s ρ)`. -/
def cfs (w : Lattice d → ℝ) (ρ : Measure (Torus d)) (s : Torus d → ℝ) : PDE.Coeff d :=
  fun k => (w k : ℂ) * shat ρ s k

theorem isRealCoeff_cfs {w : Lattice d → ℝ} (heven : ∀ k, w (-k) = w k) (ρ : Measure (Torus d))
    (s : Torus d → ℝ) : PDE.IsRealCoeff (cfs w ρ s) := by
  intro k
  simp [cfs, heven k, shat_neg]

theorem convS_ser_eq {w : Lattice d → ℝ} (hw : Summable fun k => |w k|) (heven : ∀ k, w (-k) = w k)
    (ρ : Measure (Torus d)) [IsFiniteMeasure ρ] {s : Torus d → ℝ} (hsm : Measurable s)
    {B : ℝ} (hs : ∀ y, |s y| ≤ B) : convS (ser w) ρ s = PDE.toFun (cfs w ρ s) := by
  have hcont := continuous_convS (continuous_ser hw) ρ hsm hs
  have hco : PDE.coeffOf (convS (ser w) ρ s) = cfs w ρ s := by
    funext k
    rw [PDE.coeffOf_eq_fcoef, coeff_convS (continuous_ser hw) ρ hsm hs k, ← PDE.coeffOf_eq_fcoef,
      coeffOf_ser hw heven]
    rfl
  have hsum : Summable fun k => ‖PDE.coeffOf (convS (ser w) ρ s) k‖ := by
    rw [hco]
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      (hw.mul_right (B * ρ.real Set.univ))
    simp only [cfs, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_shat_le hs k) (abs_nonneg _)
  have := PDE.toFun_coeffOf (convS (ser w) ρ s) hcont hsum
  rw [hco] at this
  exact this.symm

theorem isCk_convS (j : ℕ) {w : Lattice d → ℝ} {ε C : ℝ} (hε : 0 < ε)
    (hw : ∀ k, |w k| ≤ C * Real.exp (-ε * Lattice.enorm k ^ 2)) (heven : ∀ k, w (-k) = w k)
    (ρ : Measure (Torus d)) [IsFiniteMeasure ρ] {s : Torus d → ℝ} (hsm : Measurable s)
    {B : ℝ} (hs : ∀ y, |s y| ≤ B) : Torus.IsCk j (convS (ser w) ρ s) := by
  have hsum : Summable fun k => |w k| :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hw ((summable_gauss_lattice d ε hε).mul_left C)
  rw [convS_ser_eq hsum heven ρ hsm hs]
  have hm : (d : ℝ) / 2 + j < (d : ℝ) / 2 + j + 1 := by linarith
  obtain ⟨C', hC'⟩ := PDE.toFun_isCk_le (d := d) j ((d : ℝ) / 2 + j + 1) hm
  have hmh : PDE.MemHs ((d : ℝ) / 2 + j + 1) (cfs w ρ s) := by
    refine memHs_of_gauss (by positivity) hε (C := C * (B * ρ.real Set.univ)) (fun k => ?_)
    simp only [cfs, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |w k| * ‖shat ρ s k‖ ≤ (C * Real.exp (-ε * Lattice.enorm k ^ 2)) * (B * ρ.real Set.univ) :=
          mul_le_mul (hw k) (norm_shat_le hs k) (norm_nonneg _) ((abs_nonneg _).trans (hw k))
      _ = _ := by ring
  exact (hC' (cfs w ρ s) hmh (isRealCoeff_cfs heven ρ s)).1


theorem eq_of_coeffOf_eq {f g : Torus d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hs : Summable fun k => ‖PDE.coeffOf f k‖) (h : PDE.coeffOf f = PDE.coeffOf g) : f = g := by
  have h1 := PDE.toFun_coeffOf f hf hs
  have h2 := PDE.toFun_coeffOf g hg (by rw [← h]; exact hs)
  rw [← h1, ← h2, h]

theorem abs_apply_le_enorm (k : Lattice d) (i : Fin d) : |(k i : ℝ)| ≤ Lattice.enorm k := by
  unfold Lattice.enorm
  have := PiLp.norm_apply_le (Lattice.toEuc k) i
  simpa [Lattice.toEuc, Real.norm_eq_abs] using this

theorem summable_deriv_gauss {w : Lattice d → ℝ} {ε C : ℝ} (hε : 0 < ε)
    (hw : ∀ k, |w k| ≤ C * Real.exp (-ε * Lattice.enorm k ^ 2)) (i : Fin d) :
    Summable fun k : Lattice d => |(k i : ℝ)| * |w k| := by
  have hs := (summable_pow_gauss_lattice d hε 1).mul_left C
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (fun k => ?_) hs
  calc |(k i : ℝ)| * |w k| ≤ Lattice.enorm k * (C * Real.exp (-ε * Lattice.enorm k ^ 2)) :=
        mul_le_mul (abs_apply_le_enorm k i) (hw k) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by ring

theorem coeffOf_convS_ser {w : Lattice d → ℝ} (hw : Summable fun k => |w k|)
    (heven : ∀ k, w (-k) = w k) (ρ : Measure (Torus d)) [IsFiniteMeasure ρ] {s : Torus d → ℝ}
    (hsm : Measurable s) {B : ℝ} (hs : ∀ y, |s y| ≤ B) :
    PDE.coeffOf (convS (ser w) ρ s) = cfs w ρ s := by
  funext k
  rw [PDE.coeffOf_eq_fcoef, coeff_convS (continuous_ser hw) ρ hsm hs k, ← PDE.coeffOf_eq_fcoef,
    coeffOf_ser hw heven]
  rfl

theorem partialDeriv_convS (i : Fin d) {w : Lattice d → ℝ} {ε C : ℝ} (hε : 0 < ε)
    (hw : ∀ k, |w k| ≤ C * Real.exp (-ε * Lattice.enorm k ^ 2)) (heven : ∀ k, w (-k) = w k)
    (ρ : Measure (Torus d)) [IsFiniteMeasure ρ] {s : Torus d → ℝ} (hsm : Measurable s)
    {B : ℝ} (hs : ∀ y, |s y| ≤ B) :
    Torus.partialDeriv i (convS (ser w) ρ s) = convS (Torus.partialDeriv i (ser w)) ρ s := by
  have hsum : Summable fun k => |w k| :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hw ((summable_gauss_lattice d ε hε).mul_left C)
  have h1 : Torus.IsCk 1 (ser w) := isCk_ser 1 hε hw heven
  have h2 : Torus.IsCk 1 (convS (ser w) ρ s) := isCk_convS 1 hε hw heven ρ hsm hs
  have hc1 : Continuous (Torus.partialDeriv i (convS (ser w) ρ s)) :=
    PDE.continuous_partialDeriv i _ h2
  have hc2 : Continuous (convS (Torus.partialDeriv i (ser w)) ρ s) :=
    continuous_convS (PDE.continuous_partialDeriv i _ h1) ρ hsm hs
  have hco1 : PDE.coeffOf (Torus.partialDeriv i (convS (ser w) ρ s)) =
      PDE.derivCoeff i (cfs w ρ s) := by
    rw [PDE.coeffOf_partialDeriv i _ h2, coeffOf_convS_ser hsum heven ρ hsm hs]
  have hco2 : PDE.coeffOf (convS (Torus.partialDeriv i (ser w)) ρ s) =
      PDE.derivCoeff i (cfs w ρ s) := by
    funext k
    rw [PDE.coeffOf_eq_fcoef, coeff_convS (PDE.continuous_partialDeriv i _ h1) ρ hsm hs k,
      ← PDE.coeffOf_eq_fcoef, PDE.coeffOf_partialDeriv i _ h1, coeffOf_ser hsum heven]
    simp [PDE.derivCoeff, cfs, cf]
    ring
  have hsum2 : Summable fun k => ‖PDE.coeffOf (Torus.partialDeriv i (convS (ser w) ρ s)) k‖ := by
    rw [hco1]
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      (((summable_deriv_gauss hε hw i).mul_left (2 * Real.pi)).mul_right (B * ρ.real Set.univ))
    simp only [PDE.derivCoeff, cfs, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      Complex.norm_intCast, Complex.norm_ofNat]
    have hp : |Real.pi| = Real.pi := abs_of_pos Real.pi_pos
    rw [hp]
    have h := norm_shat_le (ρ := ρ) hs k
    have hnn : 0 ≤ 2 * Real.pi * (|(k i : ℝ)| * |w k|) := by positivity
    calc 2 * Real.pi * 1 * |(k i : ℝ)| * (|w k| * ‖shat ρ s k‖)
        = 2 * Real.pi * (|(k i : ℝ)| * |w k|) * ‖shat ρ s k‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h hnn
  exact eq_of_coeffOf_eq hc1 hc2 hsum2 (hco1.trans hco2.symm)


theorem enorm_neg (k : Lattice d) : Lattice.enorm (-k) = Lattice.enorm k := by
  unfold Lattice.enorm
  rw [Torus.toEuc_neg, norm_neg]

/-- The heat weights `e^{-4π²ε|k|²}`. -/
def aW (ε : ℝ) (k : Lattice d) : ℝ := Real.exp (-(4 * Real.pi ^ 2 * ε) * Lattice.enorm k ^ 2)

/-- The weights `e^{-ε(l+4π²|k|²)}/(l+4π²|k|²)` of the regularised Green function
(zero for `l = 0`, `k = 0`). -/
def cW (l ε : ℝ) (k : Lattice d) : ℝ :=
  if l = 0 ∧ k = 0 then 0
  else Real.exp (-ε * (l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)) / (l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)

theorem aW_even (ε : ℝ) (k : Lattice d) : aW ε (-k) = aW ε k := by
  unfold aW; rw [enorm_neg]

theorem cW_even (l ε : ℝ) (k : Lattice d) : cW l ε (-k) = cW l ε k := by
  unfold cW
  rw [enorm_neg]
  simp only [neg_eq_zero]

theorem aW_pos (ε : ℝ) (k : Lattice d) : 0 < aW ε k := Real.exp_pos _

theorem aW_bound {ε : ℝ} (k : Lattice d) :
    |aW ε k| ≤ 1 * Real.exp (-(4 * Real.pi ^ 2 * ε) * Lattice.enorm k ^ 2) := by
  rw [abs_of_pos (aW_pos ε k), one_mul]; rfl

theorem denom_pos {l : ℝ} (hl : 0 ≤ l) {k : Lattice d} (h : ¬(l = 0 ∧ k = 0)) :
    0 < l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
  by_cases hl0 : l = 0
  · have hk : k ≠ 0 := fun hk => h ⟨hl0, hk⟩
    have h1 := one_le_enorm k hk
    have h2 : 0 < Lattice.enorm k := by linarith
    rw [hl0]; simp only [zero_add]; positivity
  · have : 0 < l := lt_of_le_of_ne hl (Ne.symm hl0)
    have : 0 ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
    linarith

theorem cW_zero_zero (ε : ℝ) : cW 0 ε (0 : Lattice d) = 0 := by
  unfold cW; simp

theorem cW_nonneg {l : ℝ} (hl : 0 ≤ l) (ε : ℝ) (k : Lattice d) : 0 ≤ cW l ε k := by
  unfold cW
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (Real.exp_pos _).le (denom_pos hl h).le

theorem cW_bound {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 ≤ ε) (k : Lattice d) :
    |cW l ε k| ≤ (1 / l + 1 / (4 * Real.pi ^ 2)) *
      Real.exp (-(4 * Real.pi ^ 2 * ε) * Lattice.enorm k ^ 2) := by
  rw [abs_of_nonneg (cW_nonneg hl ε k)]
  have hC : 0 ≤ 1 / l + 1 / (4 * Real.pi ^ 2) := by positivity
  unfold cW
  split_ifs with h
  · positivity
  · have hD := denom_pos hl h
    have he : Real.exp (-ε * (l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)) ≤
        Real.exp (-(4 * Real.pi ^ 2 * ε) * Lattice.enorm k ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hε hl, sq_nonneg (Lattice.enorm k)]
    have hinv : 1 / (l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ≤ 1 / l + 1 / (4 * Real.pi ^ 2) := by
      by_cases hl0 : l = 0
      · have hk : k ≠ 0 := fun hk => h ⟨hl0, hk⟩
        have h1 := one_le_enorm k hk
        rw [hl0]
        simp only [zero_add, div_zero]
        rw [one_div_le_one_div (by positivity) (by positivity)]
        have h2 : 1 ≤ Lattice.enorm k ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 4 * Real.pi ^ 2)]
      · have hlp : 0 < l := lt_of_le_of_ne hl (Ne.symm hl0)
        have : 1 / (l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ≤ 1 / l := by
          apply one_div_le_one_div_of_le hlp
          have : 0 ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
          linarith
        have h2 : 0 ≤ 1 / (4 * Real.pi ^ 2) := by positivity
        linarith
    calc Real.exp (-ε * (l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)) /
          (l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)
        = Real.exp (-ε * (l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)) *
          (1 / (l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)) := by ring
      _ ≤ Real.exp (-(4 * Real.pi ^ 2 * ε) * Lattice.enorm k ^ 2) * (1 / l + 1 / (4 * Real.pi ^ 2)) :=
          mul_le_mul he hinv (by positivity) (Real.exp_pos _).le
      _ = _ := by ring

theorem denom_mul_cW {l : ℝ} (hl : 0 ≤ l) (ε : ℝ) {k : Lattice d} (h : ¬(l = 0 ∧ k = 0)) :
    (l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * cW l ε k = Real.exp (-l * ε) * aW ε k := by
  have hD := denom_pos hl h
  unfold cW aW
  rw [if_neg h]
  field_simp
  rw [← Real.exp_add]
  congr 1; ring

theorem cW_two {l : ℝ} (hl : 0 ≤ l) (ε : ℝ) (k : Lattice d) :
    cW l (2 * ε) k = Real.exp (-l * ε) * cW l ε k * aW ε k := by
  unfold cW aW
  by_cases h : l = 0 ∧ k = 0
  · simp [h]
  · have hD := denom_pos hl h
    rw [if_neg h, if_neg h]
    field_simp
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1; ring


theorem fcoef_lin {f g : Torus d → ℝ} (hf : Continuous f) (hg : Continuous g) (a b : ℝ) (k : Lattice d) :
    Torus.fcoef (fun x => a * f x + b * g x) k = a * Torus.fcoef f k + b * Torus.fcoef g k := by
  unfold Torus.fcoef
  have h1 : Integrable fun x : Torus d => Torus.mode (-k) x * (f x : ℂ) :=
    ((Torus.continuous_mode (-k)).mul (Complex.continuous_ofReal.comp hf)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable fun x : Torus d => Torus.mode (-k) x * (g x : ℂ) :=
    ((Torus.continuous_mode (-k)).mul (Complex.continuous_ofReal.comp hg)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have e : ∀ x : Torus d, Torus.mode (-k) x * ((a * f x + b * g x : ℝ) : ℂ) =
      (a : ℂ) * (Torus.mode (-k) x * (f x : ℂ)) + (b : ℂ) * (Torus.mode (-k) x * (g x : ℂ)) := by
    intro x; push_cast; ring
  simp_rw [e]
  rw [integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul]

theorem shat_zero (ρ : Measure (Torus d)) (s : Torus d → ℝ) :
    shat ρ s 0 = ((∫ y, s y ∂ρ : ℝ) : ℂ) := by
  unfold shat
  simp only [neg_zero, Torus.mode_zero, one_mul]
  exact integral_complex_ofReal

theorem green_identity {l ε : ℝ} (hl : 0 ≤ l) (hε : 0 < ε) (ρ : Measure (Torus d)) [IsFiniteMeasure ρ]
    {s : Torus d → ℝ} (hsm : Measurable s) {B : ℝ} (hs : ∀ y, |s y| ≤ B)
    (hneut : l = 0 → ∫ y, s y ∂ρ = 0) (x : Torus d) :
    l * convS (ser (cW l ε)) ρ s x - Torus.laplacian (convS (ser (cW l ε)) ρ s) x =
      Real.exp (-l * ε) * convS (ser (aW ε)) ρ s x := by
  have hc0 : 0 < 4 * Real.pi ^ 2 * ε := by positivity
  have hcb : ∀ k : Lattice d, |cW l ε k| ≤ (1 / l + 1 / (4 * Real.pi ^ 2)) *
      Real.exp (-(4 * Real.pi ^ 2 * ε) * Lattice.enorm k ^ 2) := fun k => cW_bound hl hε.le k
  have hab : ∀ k : Lattice d, |aW ε k| ≤ 1 * Real.exp (-(4 * Real.pi ^ 2 * ε) * Lattice.enorm k ^ 2) :=
    fun k => aW_bound k
  have hsumc : Summable fun k : Lattice d => |cW l ε k| :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hcb ((summable_gauss_lattice d _ hc0).mul_left _)
  have hsuma : Summable fun k : Lattice d => |aW ε k| :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hab ((summable_gauss_lattice d _ hc0).mul_left _)
  set φ := convS (ser (cW l ε)) ρ s with hφ
  have hφ2 : Torus.IsCk 2 φ := isCk_convS 2 hc0 hcb (cW_even l ε) ρ hsm hs
  have hφ0 : Continuous φ := continuous_convS (continuous_ser hsumc) ρ hsm hs
  have hlap : Continuous (Torus.laplacian φ) := by
    have : Torus.laplacian φ = fun x => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j φ) x :=
      funext (PDE.laplacian_eq_sum φ hφ2)
    rw [this]
    exact continuous_finsetSum _ fun j _ =>
      PDE.continuous_partialDeriv j _ (PDE.isCk_one_partialDeriv j φ hφ2)
  have hP : Continuous (convS (ser (aW ε)) ρ s) := continuous_convS (continuous_ser hsuma) ρ hsm hs
  set P := convS (ser (aW ε)) ρ s with hPdef
  have hF1 : Continuous (fun x => l * φ x + (-1) * Torus.laplacian φ x) :=
    (continuous_const.mul hφ0).add (continuous_const.mul hlap)
  have hF2 : Continuous (fun x => Real.exp (-l * ε) * P x + 0 * P x) :=
    (continuous_const.mul hP).add (continuous_const.mul hP)
  have hcφ : PDE.coeffOf φ = cfs (cW l ε) ρ s := coeffOf_convS_ser hsumc (cW_even l ε) ρ hsm hs
  have hcP : PDE.coeffOf P = cfs (aW ε) ρ s := coeffOf_convS_ser hsuma (aW_even ε) ρ hsm hs
  have hcl : PDE.coeffOf (Torus.laplacian φ) = PDE.laplaceCoeff (cfs (cW l ε) ρ s) := by
    rw [PDE.coeffOf_laplacian φ hφ2, hcφ]
  have hco : PDE.coeffOf (fun x => l * φ x + (-1) * Torus.laplacian φ x) =
      PDE.coeffOf (fun x => Real.exp (-l * ε) * P x + 0 * P x) := by
    funext k
    rw [PDE.coeffOf_eq_fcoef, PDE.coeffOf_eq_fcoef, fcoef_lin hφ0 hlap, fcoef_lin hP hP]
    simp only [← PDE.coeffOf_eq_fcoef]
    rw [hcφ, hcl, hcP]
    simp only [PDE.laplaceCoeff, cfs, cf]
    by_cases h : l = 0 ∧ k = 0
    · obtain ⟨hl0, hk0⟩ := h
      subst hl0; subst hk0
      have h0 : shat ρ s 0 = 0 := by rw [shat_zero, hneut rfl]; simp
      have : Lattice.enorm (0 : Lattice d) = 0 := by
        unfold Lattice.enorm; simp [Lattice.toEuc]; rfl
      simp [h0, cW_zero_zero]
    · have := denom_mul_cW hl ε h
      have hd : ((l + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ) * ((cW l ε k : ℝ) : ℂ) =
          ((Real.exp (-l * ε) * aW ε k : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, this]
      push_cast at hd ⊢
      calc (l : ℂ) * (↑(cW l ε k) * shat ρ s k) + (-1 : ℂ) * (-(4 * (Real.pi : ℂ) ^ 2 * (Lattice.enorm k : ℂ) ^ 2) *
            (↑(cW l ε k) * shat ρ s k))
          = ((l : ℂ) + 4 * (Real.pi : ℂ) ^ 2 * (Lattice.enorm k : ℂ) ^ 2) * ↑(cW l ε k) * shat ρ s k := by ring
        _ = _ := by rw [hd]; ring
  have hsum : Summable fun k => ‖PDE.coeffOf (fun x => l * φ x + (-1) * Torus.laplacian φ x) k‖ := by
    rw [hco]
    have hco2 : ∀ k, PDE.coeffOf (fun x => Real.exp (-l * ε) * P x + 0 * P x) k =
        (Real.exp (-l * ε) : ℂ) * ((aW ε k : ℂ) * shat ρ s k) := by
      intro k
      rw [PDE.coeffOf_eq_fcoef, fcoef_lin hP hP]
      simp only [← PDE.coeffOf_eq_fcoef]
      rw [hcP]
      simp [cfs, cf]
    simp_rw [hco2]
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      (hsuma.mul_right (Real.exp (-l * ε) * (B * ρ.real Set.univ)))
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := norm_shat_le (ρ := ρ) hs k
    calc |Real.exp (-l * ε)| * (|aW ε k| * ‖shat ρ s k‖)
        ≤ |Real.exp (-l * ε)| * (|aW ε k| * (B * ρ.real Set.univ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) (abs_nonneg _)
      _ = _ := by rw [abs_of_pos (Real.exp_pos _)]; ring
  have := eq_of_coeffOf_eq hF1 hF2 hsum hco
  have := congrFun this x
  simp only [zero_mul, add_zero] at this
  linarith


end HRS.Commutator.FourierAux
