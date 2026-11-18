import HRS.PDE.ToolboxRd.Defs

/-!
# `L²` Fourier analysis on `ℝ^d` for Lemma C.3 on `ℝ^d`

Basic API for `fourierL2`, the translation formula, `H¹` via difference quotients, and the
quadratic form estimates `quadratic_toolbox_basic`, `quadratic_toolbox_cauchySchwarz`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ComplexInnerProductSpace

namespace HRS.PDE.ToolboxRd.FourierAux
open HRS.PDE.ToolboxRd
variable {d : ℕ}

/-- real `L²` function as a complex `Lp` element -/
def ofRealLp {u : Euc d → ℝ} (hu : MemLp u 2 volume) : Lp (α := Euc d) ℂ 2 :=
  (hu.ofReal (K := ℂ)).toLp (fun x => ((u x : ℝ) : ℂ))

/-- the `L²` Fourier transform as an `Lp` map -/
abbrev FT (d : ℕ) : Lp (α := Euc d) ℂ 2 ≃ₗᵢ[ℂ] Lp (α := Euc d) ℂ 2 :=
  Lp.fourierTransformₗᵢ (Euc d) ℂ

theorem fourierL2_eq {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    fourierL2 u = ⇑(FT d (ofRealLp hu)) := by
  unfold fourierL2
  simp only [hu, dite_true]; rfl

theorem ofRealLp_coe {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    (ofRealLp hu : Euc d → ℂ) =ᵐ[volume] fun x => ((u x : ℝ) : ℂ) :=
  MemLp.coeFn_toLp _

theorem ofRealLp_add {u v : Euc d → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    ofRealLp (hu.add hv) = ofRealLp hu + ofRealLp hv := by
  apply Lp.ext
  filter_upwards [ofRealLp_coe (hu.add hv), ofRealLp_coe hu, ofRealLp_coe hv,
    Lp.coeFn_add (ofRealLp hu) (ofRealLp hv)] with x h1 h2 h3 h4
  rw [h4]; simp [h1, h2, h3]

theorem inner_FT (f g : Lp (α := Euc d) ℂ 2) : inner ℂ (FT d f) (FT d g) = inner ℂ f g :=
  (FT d).inner_map_map f g

theorem ofRealLp_sub {u v : Euc d → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    ofRealLp (hu.sub hv) = ofRealLp hu - ofRealLp hv := by
  apply Lp.ext
  filter_upwards [ofRealLp_coe (hu.sub hv), ofRealLp_coe hu, ofRealLp_coe hv,
    Lp.coeFn_sub (ofRealLp hu) (ofRealLp hv)] with x h1 h2 h3 h4
  rw [h4]; simp [h1, h2, h3]

theorem ofRealLp_smul {u : Euc d → ℝ} (hu : MemLp u 2 volume) (c : ℝ) :
    ofRealLp (hu.const_smul c) = (c : ℂ) • ofRealLp hu := by
  apply Lp.ext
  filter_upwards [ofRealLp_coe (hu.const_smul c), ofRealLp_coe hu,
    Lp.coeFn_smul (c : ℂ) (ofRealLp hu)] with x h1 h2 h4
  rw [h4]; simp [h1, h2]

theorem ofRealLp_congr {u v : Euc d → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (h : u =ᵐ[volume] v) : ofRealLp hu = ofRealLp hv := by
  apply Lp.ext
  filter_upwards [ofRealLp_coe hu, ofRealLp_coe hv, h] with x h1 h2 h3
  rw [h1, h2, h3]

theorem fourierL2_congr_ae {u v : Euc d → ℝ} (h : u =ᵐ[volume] v) :
    fourierL2 u = fourierL2 v := by
  by_cases hu : MemLp u 2 volume
  · have hv : MemLp v 2 volume := hu.ae_eq h
    rw [fourierL2_eq hu, fourierL2_eq hv, ofRealLp_congr hu hv h]
  · have hv : ¬ MemLp v 2 volume := fun hv => hu (hv.ae_eq h.symm)
    simp [fourierL2, hu, hv]

theorem fourierL2_add {u v : Euc d → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    fourierL2 (fun x => u x + v x) =ᵐ[volume] fun ξ => fourierL2 u ξ + fourierL2 v ξ := by
  have hw : MemLp (fun x => u x + v x) 2 volume := hu.add hv
  rw [fourierL2_eq hw, fourierL2_eq hu, fourierL2_eq hv]
  have : ofRealLp hw = ofRealLp hu + ofRealLp hv := ofRealLp_add hu hv
  rw [this, map_add]
  exact Lp.coeFn_add _ _

theorem fourierL2_sub {u v : Euc d → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    fourierL2 (fun x => u x - v x) =ᵐ[volume] fun ξ => fourierL2 u ξ - fourierL2 v ξ := by
  have hw : MemLp (fun x => u x - v x) 2 volume := hu.sub hv
  rw [fourierL2_eq hw, fourierL2_eq hu, fourierL2_eq hv]
  have : ofRealLp hw = ofRealLp hu - ofRealLp hv := ofRealLp_sub hu hv
  rw [this, map_sub]
  exact Lp.coeFn_sub _ _

theorem fourierL2_smul {u : Euc d → ℝ} (hu : MemLp u 2 volume) (c : ℝ) :
    fourierL2 (fun x => c * u x) =ᵐ[volume] fun ξ => (c : ℂ) * fourierL2 u ξ := by
  have hw : MemLp (fun x => c * u x) 2 volume := hu.const_mul c
  rw [fourierL2_eq hw, fourierL2_eq hu]
  have : ofRealLp hw = (c : ℂ) • ofRealLp hu := ofRealLp_smul hu c
  rw [this, map_smul]
  filter_upwards [Lp.coeFn_smul (c : ℂ) (FT d (ofRealLp hu))] with x hx
  rw [hx]; simp only [Pi.smul_apply, smul_eq_mul]

theorem inner_ofRealLp {u v : Euc d → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    inner ℂ (ofRealLp hv) (ofRealLp hu) = ((∫ x, u x * v x : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  rw [← integral_complex_ofReal (μ := volume) (f := fun x => u x * v x)]
  apply integral_congr_ae
  filter_upwards [ofRealLp_coe hu, ofRealLp_coe hv] with x h1 h2
  rw [h1, h2]
  simp

theorem inner_fourier_ofRealLp {u v : Euc d → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    inner ℂ (FT d (ofRealLp hv)) (FT d (ofRealLp hu)) =
      ∫ ξ, fourierL2 u ξ * conj (fourierL2 v ξ) := by
  rw [MeasureTheory.L2.inner_def, fourierL2_eq hu, fourierL2_eq hv]
  apply integral_congr_ae
  filter_upwards with x
  simp


/-- the phase `e^{-2πi⟨h,ξ⟩}` -/
def phase (h : Euc d) (ξ : Euc d) : ℂ :=
  Complex.exp (((-2 * Real.pi * inner ℝ h ξ : ℝ) : ℂ) * Complex.I)

theorem norm_phase (h ξ : Euc d) : ‖phase h ξ‖ = 1 := by
  unfold phase
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_phase (h : Euc d) : Continuous (phase h) := by
  unfold phase; fun_prop

/-- translation on `L²` -/
def translLp (h : Euc d) : Lp (α := Euc d) ℂ 2 →+ Lp (α := Euc d) ℂ 2 :=
  Lp.compMeasurePreserving (fun x : Euc d => x - h) (measurePreserving_sub_right volume h)

theorem continuous_translLp (h : Euc d) : Continuous (translLp h) :=
  (Lp.isometry_compMeasurePreserving _).continuous

def phaseLp (h : Euc d) : Lp (α := Euc d) ℂ ⊤ :=
  (memLp_top_of_bound (continuous_phase h).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ξ => (norm_phase h ξ).le)).toLp (phase h)

theorem phaseLp_coe (h : Euc d) : (phaseLp h : Euc d → ℂ) =ᵐ[volume] phase h :=
  MemLp.coeFn_toLp _

/-- multiplication by the phase -/
def mulPhase (h : Euc d) : Lp (α := Euc d) ℂ 2 →+ Lp (α := Euc d) ℂ 2 where
  toFun F := (phaseLp h : Lp (α := Euc d) ℂ ⊤) • F
  map_zero' := Lp.smul_zero _ _ _
  map_add' F G := Lp.add_smul _ F G

theorem mulPhase_coe (h : Euc d) (F : Lp (α := Euc d) ℂ 2) :
    (mulPhase h F : Euc d → ℂ) =ᵐ[volume] fun ξ => phase h ξ * F ξ := by
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (phaseLp h) F, phaseLp_coe h] with ξ h1 h2
  simp only [mulPhase, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [h1]; simp [h2]

theorem continuous_mulPhase (h : Euc d) : Continuous (mulPhase h) := by
  apply AddMonoidHomClass.continuous_of_bound (mulPhase h) ‖(phaseLp h : Lp (α := Euc d) ℂ ⊤)‖
  intro F
  exact Lp.norm_smul_le (r := 2) (phaseLp h) F


open SchwartzMap in
/-- translated Schwartz function -/
def translSchwartz (h : Euc d) (φ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ :=
  SchwartzMap.compCLM ℝ (g := fun x : Euc d => x - h) (by fun_prop)
    ⟨1, 1 + ‖h‖, fun x => by
      have : ‖x‖ ≤ ‖x - h‖ + ‖h‖ := by simpa using norm_add_le (x - h) h
      nlinarith [norm_nonneg h, norm_nonneg (x - h)]⟩ φ

theorem translSchwartz_apply (h : Euc d) (φ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    translSchwartz h φ x = φ (x - h) := rfl

theorem fourier_translSchwartz (h : Euc d) (φ : SchwartzMap (Euc d) ℂ) (ξ : Euc d) :
    (𝓕 (translSchwartz h φ) : SchwartzMap (Euc d) ℂ) ξ = phase h ξ * (𝓕 φ : SchwartzMap (Euc d) ℂ) ξ := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq', Real.fourier_eq']
  have key : ∀ v : Euc d, Complex.exp (((-2 * Real.pi * inner ℝ v ξ : ℝ) : ℂ) * Complex.I) •
      (translSchwartz h φ) v = (fun y : Euc d => (phase h ξ * Complex.exp (((-2 * Real.pi * inner ℝ y ξ : ℝ) : ℂ) * Complex.I)) • φ y) (v - h) := by
    intro v
    simp only [translSchwartz_apply, phase, smul_eq_mul]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    rw [← add_mul]
    congr 1
    push_cast
    rw [inner_sub_left]
    push_cast
    ring
  simp_rw [key]
  rw [integral_sub_right_eq_self (fun y : Euc d => (phase h ξ * Complex.exp (((-2 * Real.pi * inner ℝ y ξ : ℝ) : ℂ) * Complex.I)) • φ y) h]
  simp only [smul_eq_mul, mul_assoc]
  rw [integral_const_mul]

theorem translLp_toLp (h : Euc d) (φ : SchwartzMap (Euc d) ℂ) :
    translLp h (φ.toLp 2) = (translSchwartz h φ).toLp 2 := by
  apply Lp.ext
  have h1 := Lp.coeFn_compMeasurePreserving (φ.toLp 2 : Lp (α := Euc d) ℂ 2)
    (measurePreserving_sub_right volume h)
  have h2 := (measurePreserving_sub_right (volume : Measure (Euc d)) h).quasiMeasurePreserving.ae_eq_comp
    (SchwartzMap.coeFn_toLp φ 2 volume)
  filter_upwards [h1, h2, SchwartzMap.coeFn_toLp (translSchwartz h φ) 2 volume] with x a b c
  rw [c]
  exact a.trans b

theorem fourier_translLp (h : Euc d) (f : Lp (α := Euc d) ℂ 2) :
    FT d (translLp h f) = mulPhase h (FT d f) := by
  refine (SchwartzMap.denseRange_toLpCLM (E := Euc d) (F := ℂ) (p := 2)
    ENNReal.ofNat_ne_top).induction_on f (isClosed_eq ?_ ?_) ?_
  · exact (FT d).continuous.comp (continuous_translLp h)
  · exact (continuous_mulPhase h).comp (FT d).continuous
  · intro φ
    simp only [SchwartzMap.toLpCLM_apply]
    rw [translLp_toLp]
    have e1 : FT d ((translSchwartz h φ).toLp 2) = ((𝓕 (translSchwartz h φ) : SchwartzMap (Euc d) ℂ)).toLp 2 :=
      SchwartzMap.toLp_fourier_eq _
    have e2 : FT d (φ.toLp 2) = ((𝓕 φ : SchwartzMap (Euc d) ℂ)).toLp 2 :=
      SchwartzMap.toLp_fourier_eq _
    rw [e1, e2]
    apply Lp.ext
    filter_upwards [SchwartzMap.coeFn_toLp (𝓕 (translSchwartz h φ) : SchwartzMap (Euc d) ℂ) 2 volume,
      mulPhase_coe h (((𝓕 φ : SchwartzMap (Euc d) ℂ)).toLp 2),
      SchwartzMap.coeFn_toLp (𝓕 φ : SchwartzMap (Euc d) ℂ) 2 volume] with ξ a b c
    rw [a, b, c, fourier_translSchwartz]

theorem memLp_fourierL2 {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    MemLp (fourierL2 u) 2 volume := by
  rw [fourierL2_eq hu]; exact Lp.memLp _

theorem aestronglyMeasurable_fourierL2 {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    AEStronglyMeasurable (fourierL2 u) volume :=
  (memLp_fourierL2 hu).aestronglyMeasurable

theorem integral_fourierL2_mul_conj {u v : Euc d → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    ∫ ξ, fourierL2 u ξ * conj (fourierL2 v ξ) = ((∫ x, u x * v x : ℝ) : ℂ) := by
  rw [← inner_fourier_ofRealLp hu hv, inner_FT, inner_ofRealLp hu hv]

theorem integrable_fourierL2_mul_conj {u v : Euc d → ℝ} (hu : MemLp u 2 volume)
    (hv : MemLp v 2 volume) :
    Integrable (fun ξ => fourierL2 u ξ * conj (fourierL2 v ξ)) volume := by
  rw [fourierL2_eq hu, fourierL2_eq hv]
  have := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (FT d (ofRealLp hv)) (FT d (ofRealLp hu))
  refine this.congr ?_
  filter_upwards with x
  simp

theorem integrable_norm_sq_fourierL2 {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    Integrable (fun ξ => ‖fourierL2 u ξ‖ ^ 2) volume :=
  (memLp_fourierL2 hu).norm.integrable_sq

theorem integral_norm_sq_fourierL2 {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    ∫ ξ, ‖fourierL2 u ξ‖ ^ 2 = ∫ x, u x ^ 2 := by
  have h := integral_fourierL2_mul_conj hu hu
  have h1 : (∫ ξ, fourierL2 u ξ * conj (fourierL2 u ξ)) = ((∫ ξ, ‖fourierL2 u ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal (μ := volume) (f := fun ξ => ‖fourierL2 u ξ‖ ^ 2)]
    congr 1; ext ξ
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h1] at h
  have h2 := Complex.ofReal_injective h
  rw [h2]; congr 1; ext x; ring

theorem integral_sq_eq_norm_sq {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    ∫ x, u x ^ 2 = ∫ ξ, ‖fourierL2 u ξ‖ ^ 2 := (integral_norm_sq_fourierL2 hu).symm

theorem memLp_translate {u : Euc d → ℝ} (hu : MemLp u 2 volume) (h : Euc d) :
    MemLp (fun x => u (x - h)) 2 volume :=
  hu.comp_measurePreserving (measurePreserving_sub_right volume h)

theorem ofRealLp_translate {u : Euc d → ℝ} (hu : MemLp u 2 volume) (h : Euc d) :
    translLp h (ofRealLp hu) = ofRealLp (memLp_translate hu h) := by
  apply Lp.ext
  have h1 := Lp.coeFn_compMeasurePreserving (ofRealLp hu) (measurePreserving_sub_right volume h)
  have h2 := (measurePreserving_sub_right (volume : Measure (Euc d)) h).quasiMeasurePreserving.ae_eq_comp
    (ofRealLp_coe hu)
  filter_upwards [h1, h2, ofRealLp_coe (memLp_translate hu h)] with x a b c
  rw [c]
  exact a.trans b

/-- Translation formula: `\\widehat{u - u(· - h)} = (1 - e^{-2πi⟨h,ξ⟩}) û`. -/
theorem fourierL2_sub_translate {u : Euc d → ℝ} (hu : MemLp u 2 volume) (h : Euc d) :
    fourierL2 (fun x => u x - u (x - h)) =ᵐ[volume]
      fun ξ => (1 - phase h ξ) * fourierL2 u ξ := by
  have hs := memLp_translate hu h
  have hw : MemLp (fun x => u x - u (x - h)) 2 volume := hu.sub hs
  rw [fourierL2_eq hw]
  have : ofRealLp hw = ofRealLp hu - translLp h (ofRealLp hu) := by
    rw [ofRealLp_translate hu h]; exact ofRealLp_sub hu hs
  rw [this, map_sub, fourier_translLp, fourierL2_eq hu]
  filter_upwards [Lp.coeFn_sub (FT d (ofRealLp hu)) (mulPhase h (FT d (ofRealLp hu))),
    mulPhase_coe h (FT d (ofRealLp hu))] with ξ a b
  rw [a]; simp only [Pi.sub_apply]; rw [b]; ring

theorem integral_diff_sq_eq {u : Euc d → ℝ} (hu : MemLp u 2 volume) (h : Euc d) :
    ∫ x, (u x - u (x - h)) ^ 2 = ∫ ξ, ‖1 - phase h ξ‖ ^ 2 * ‖fourierL2 u ξ‖ ^ 2 := by
  have hw : MemLp (fun x => u x - u (x - h)) 2 volume := hu.sub (memLp_translate hu h)
  rw [integral_sq_eq_norm_sq hw]
  apply integral_congr_ae
  filter_upwards [fourierL2_sub_translate hu h] with ξ hξ
  rw [hξ, norm_mul, mul_pow]

theorem integrable_diff_sq {u : Euc d → ℝ} (hu : MemLp u 2 volume) (h : Euc d) :
    Integrable (fun ξ => ‖1 - phase h ξ‖ ^ 2 * ‖fourierL2 u ξ‖ ^ 2) volume := by
  have hw : MemLp (fun x => u x - u (x - h)) 2 volume := hu.sub (memLp_translate hu h)
  refine (integrable_norm_sq_fourierL2 hw).congr ?_
  filter_upwards [fourierL2_sub_translate hu h] with ξ hξ
  rw [hξ, norm_mul, mul_pow]

theorem norm_one_sub_exp_sq (θ : ℝ) :
    ‖1 - Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at this
    rw [this, Real.cos_sq']; ring
  have h2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have := Real.sin_two_mul (θ / 2)
    rwa [show 2 * (θ / 2) = θ by ring] at this
  rw [this, h2]
  have := Real.sin_sq_add_cos_sq (θ / 2)
  nlinarith [this]

theorem norm_one_sub_phase_sq (h ξ : Euc d) :
    ‖1 - phase h ξ‖ ^ 2 = 4 * Real.sin (Real.pi * inner ℝ h ξ) ^ 2 := by
  unfold phase
  rw [norm_one_sub_exp_sq]
  have : -2 * Real.pi * inner ℝ h ξ / 2 = -(Real.pi * inner ℝ h ξ) := by ring
  rw [this, Real.sin_neg]; ring

theorem norm_one_sub_phase_le (h ξ : Euc d) :
    ‖1 - phase h ξ‖ ≤ 2 * Real.pi * (‖h‖ * ‖ξ‖) := by
  unfold phase
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -2 * Real.pi * inner ℝ h ξ)
  rw [mul_comm Complex.I] at this
  rw [norm_sub_rev]
  refine this.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  simp only [abs_neg, abs_two, Real.abs_pi]
  have := abs_real_inner_le_norm h ξ
  have hpi := Real.pi_pos
  nlinarith

theorem norm_one_sub_phase_sq_le (h ξ : Euc d) :
    ‖1 - phase h ξ‖ ^ 2 ≤ ‖h‖ ^ 2 * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) := by
  have h1 := norm_one_sub_phase_le h ξ
  have h0 := norm_nonneg (1 - phase h ξ)
  calc ‖1 - phase h ξ‖ ^ 2 ≤ (2 * Real.pi * (‖h‖ * ‖ξ‖)) ^ 2 := by gcongr
    _ = ‖h‖ ^ 2 * (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) := by ring
    _ ≤ _ := by
      have := sq_nonneg ‖h‖
      nlinarith


/-- the Sobolev weight `1 + 4π²|ξ|²` -/
def wt (ξ : Euc d) : ℝ := 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2

theorem one_le_wt (ξ : Euc d) : 1 ≤ wt ξ := by
  unfold wt; nlinarith [sq_nonneg ‖ξ‖, sq_nonneg Real.pi]

theorem wt_pos (ξ : Euc d) : 0 < wt ξ := lt_of_lt_of_le one_pos (one_le_wt ξ)

theorem continuous_wt : Continuous (wt : Euc d → ℝ) := by unfold wt; fun_prop

theorem continuous_wt_rpow (s : ℝ) : Continuous (fun ξ : Euc d => wt ξ ^ s) :=
  continuous_wt.rpow_const (fun x => Or.inl (wt_pos x).ne')

theorem sobolevNormSq_eq (s : ℝ) (u : Euc d → ℝ) :
    sobolevNormSq s u = ∫ ξ, wt ξ ^ s * ‖fourierL2 u ξ‖ ^ 2 := rfl

theorem aesm_sq {F : Euc d → ℂ} (hm : AEStronglyMeasurable F volume) :
    AEStronglyMeasurable (fun ξ => ‖F ξ‖ ^ 2) volume :=
  (continuous_pow 2).comp_aestronglyMeasurable hm.norm

theorem aesm_wt_mul {F : Euc d → ℂ} (hm : AEStronglyMeasurable F volume) (s : ℝ) :
    AEStronglyMeasurable (fun ξ => wt ξ ^ s * ‖F ξ‖ ^ 2) volume :=
  (continuous_wt_rpow s).aestronglyMeasurable.mul (aesm_sq hm)

theorem memSobolev_mono {s s' : ℝ} {u : Euc d → ℝ} (h : s' ≤ s) (hu : MemSobolev s u) :
    MemSobolev s' u := by
  refine ⟨hu.1, ?_⟩
  have hm := aestronglyMeasurable_fourierL2 hu.1
  refine Integrable.mono' hu.2 (aesm_wt_mul hm s') (Filter.Eventually.of_forall fun ξ => ?_)
  have h0 : 0 ≤ wt ξ ^ s' * ‖fourierL2 u ξ‖ ^ 2 := by
    have := wt_pos (d := d) ξ
    positivity
  change ‖wt ξ ^ s' * ‖fourierL2 u ξ‖ ^ 2‖ ≤ wt ξ ^ s * ‖fourierL2 u ξ‖ ^ 2
  rw [Real.norm_of_nonneg h0]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (one_le_wt ξ) h) (by positivity)

theorem diff_sq_le {u : Euc d → ℝ} (hu : MemSobolev 1 u) (h : Euc d) :
    ∫ x, (u x - u (x - h)) ^ 2 ≤ ‖h‖ ^ 2 * sobolevNormSq 1 u := by
  rw [integral_diff_sq_eq hu.1, sobolevNormSq_eq, ← integral_const_mul]
  refine integral_mono (integrable_diff_sq hu.1 h) (hu.2.const_mul _) fun ξ => ?_
  have h1 : ‖1 - phase h ξ‖ ^ 2 ≤ ‖h‖ ^ 2 * wt ξ := norm_one_sub_phase_sq_le h ξ
  rw [Real.rpow_one]
  show _ ≤ ‖h‖ ^ 2 * (wt ξ * _)
  calc _ ≤ (‖h‖ ^ 2 * wt ξ) * ‖fourierL2 u ξ‖ ^ 2 := by gcongr
    _ = _ := by ring


theorem sin_eq_mul_sinc (x : ℝ) : Real.sin x = x * Real.sinc x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]; field_simp

theorem inner_single_left' (i : Fin d) (t : ℝ) (ξ : Euc d) :
    inner ℝ (EuclideanSpace.single i t : Euc d) ξ = t * ξ i := by
  simp [EuclideanSpace.inner_single_left]

/-- coordinate difference quotient integrand -/
def dq (u : Euc d → ℝ) (i : Fin d) (t : ℝ) (ξ : Euc d) : ℝ :=
  ‖1 - phase (EuclideanSpace.single i t : Euc d) ξ‖ ^ 2 / t ^ 2 * ‖fourierL2 u ξ‖ ^ 2

theorem tendsto_dq (u : Euc d → ℝ) (i : Fin d) (ξ : Euc d) :
    Tendsto (fun t : ℝ => dq u i t ξ) (𝓝[>] 0)
      (𝓝 (4 * Real.pi ^ 2 * (ξ i) ^ 2 * ‖fourierL2 u ξ‖ ^ 2)) := by
  have hc : Continuous (fun t : ℝ => 4 * (Real.pi * ξ i) ^ 2 * Real.sinc (Real.pi * ξ i * t) ^ 2 *
      ‖fourierL2 u ξ‖ ^ 2) := by
    have := Real.continuous_sinc
    fun_prop
  have h0 := hc.tendsto 0
  simp only [mul_zero, Real.sinc_zero] at h0
  have h1 : Tendsto (fun t : ℝ => 4 * (Real.pi * ξ i) ^ 2 * Real.sinc (Real.pi * ξ i * t) ^ 2 *
      ‖fourierL2 u ξ‖ ^ 2) (𝓝[>] 0) (𝓝 (4 * (Real.pi * ξ i) ^ 2 * 1 ^ 2 * ‖fourierL2 u ξ‖ ^ 2)) :=
    h0.mono_left nhdsWithin_le_nhds
  have h2 : (4 * (Real.pi * ξ i) ^ 2 * 1 ^ 2 * ‖fourierL2 u ξ‖ ^ 2) =
      4 * Real.pi ^ 2 * (ξ i) ^ 2 * ‖fourierL2 u ξ‖ ^ 2 := by ring
  rw [h2] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  unfold dq
  rw [norm_one_sub_phase_sq, inner_single_left', sin_eq_mul_sinc (Real.pi * (t * ξ i))]
  have : Real.pi * (t * ξ i) = Real.pi * ξ i * t := by ring
  rw [this]
  field_simp


theorem norm_single' (i : Fin d) (t : ℝ) : ‖(EuclideanSpace.single i t : Euc d)‖ = |t| := by
  simp

theorem dq_integrable {u : Euc d → ℝ} (hu : MemLp u 2 volume) (i : Fin d) (t : ℝ) :
    Integrable (dq u i t) volume := by
  have := (integrable_diff_sq hu (EuclideanSpace.single i t : Euc d)).div_const (t ^ 2)
  refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [dq]; ring

theorem integral_dq_le {u : Euc d → ℝ} (hu : MemLp u 2 volume) (C : ℝ)
    (hC : ∀ h : Euc d, ∫ x, (u x - u (x - h)) ^ 2 ≤ C * ‖h‖ ^ 2) (i : Fin d) {t : ℝ} (ht : 0 < t) :
    ∫ ξ, dq u i t ξ ≤ C := by
  have h1 : ∫ ξ, dq u i t ξ = (∫ x, (u x - (u (x - (EuclideanSpace.single i t : Euc d)))) ^ 2) / t ^ 2 := by
    rw [integral_diff_sq_eq hu, ← integral_div]
    congr 1; ext ξ; simp only [dq]; ring
  rw [h1, div_le_iff₀ (by positivity)]
  have := hC (EuclideanSpace.single i t)
  rw [norm_single', sq_abs] at this
  linarith

theorem aemeasurable_dq {u : Euc d → ℝ} (hu : MemLp u 2 volume) (i : Fin d) (t : ℝ) :
    AEMeasurable (dq u i t) volume := by
  have hm := aesm_sq (aestronglyMeasurable_fourierL2 hu)
  have hc : Continuous (fun ξ : Euc d => ‖1 - phase (EuclideanSpace.single i t : Euc d) ξ‖ ^ 2 / t ^ 2) := by
    have := continuous_phase (EuclideanSpace.single i t : Euc d)
    fun_prop
  exact (hc.aestronglyMeasurable.mul hm).aemeasurable

theorem coord_integrable {u : Euc d → ℝ} (hu : MemLp u 2 volume) (C : ℝ)
    (hC : ∀ h : Euc d, ∫ x, (u x - u (x - h)) ^ 2 ≤ C * ‖h‖ ^ 2) (i : Fin d) :
    Integrable (fun ξ : Euc d => 4 * Real.pi ^ 2 * (ξ i) ^ 2 * ‖fourierL2 u ξ‖ ^ 2) volume ∧
      ∫ ξ, 4 * Real.pi ^ 2 * (ξ i) ^ 2 * ‖fourierL2 u ξ‖ ^ 2 ≤ C := by
  set a : Euc d → ℝ := fun ξ => 4 * Real.pi ^ 2 * (ξ i) ^ 2 * ‖fourierL2 u ξ‖ ^ 2 with ha
  have ha0 : ∀ ξ, 0 ≤ a ξ := fun ξ => by simp only [ha]; positivity
  have hmeas : ∀ t : ℝ, AEMeasurable (fun ξ => ENNReal.ofReal (dq u i t ξ)) volume :=
    fun t => ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_dq hu i t)
  have hfat := lintegral_liminf_le' (μ := (volume : Measure (Euc d))) (u := 𝓝[>] (0 : ℝ)) hmeas
  have hlim : ∀ ξ, liminf (fun t : ℝ => ENNReal.ofReal (dq u i t ξ)) (𝓝[>] 0) = ENNReal.ofReal (a ξ) := by
    intro ξ
    exact ((ENNReal.tendsto_ofReal (tendsto_dq u i ξ))).liminf_eq
  simp_rw [hlim] at hfat
  have hC0 : 0 ≤ C := by
    have h1 := hC (EuclideanSpace.single i 1)
    rw [norm_single'] at h1
    have : 0 ≤ ∫ x, (u x - u (x - (EuclideanSpace.single i (1:ℝ) : Euc d))) ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    simp at h1
    linarith
  have hle : liminf (fun t : ℝ => ∫⁻ ξ, ENNReal.ofReal (dq u i t ξ)) (𝓝[>] 0) ≤ ENNReal.ofReal C := by
    apply liminf_le_of_frequently_le'
    apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [← ofReal_integral_eq_lintegral_ofReal (dq_integrable hu i t)
      (Filter.Eventually.of_forall fun ξ => by simp only [dq]; positivity)]
    exact ENNReal.ofReal_le_ofReal (integral_dq_le hu C hC i ht)
  have hfin := hfat.trans hle
  have hint : Integrable a volume := by
    refine ⟨?_, ?_⟩
    · have h2 := (aesm_sq (aestronglyMeasurable_fourierL2 hu))
      have : Continuous (fun ξ : Euc d => 4 * Real.pi ^ 2 * (ξ i) ^ 2) := by
        have : Continuous (fun ξ : Euc d => ξ i) := by fun_prop
        fun_prop
      exact this.aestronglyMeasurable.mul h2
    · rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall ha0)]
      exact lt_of_le_of_lt hfin ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff hC0, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall ha0)]
  exact hfin


theorem memSobolev_one_of_diff_bound {u : Euc d → ℝ} (hu : MemLp u 2 volume) (C : ℝ)
    (hC : ∀ h : Euc d, ∫ x, (u x - u (x - h)) ^ 2 ≤ C * ‖h‖ ^ 2) : MemSobolev 1 u := by
  refine ⟨hu, ?_⟩
  have hsum : Integrable (fun ξ : Euc d => ‖fourierL2 u ξ‖ ^ 2 +
      ∑ i : Fin d, 4 * Real.pi ^ 2 * (ξ i) ^ 2 * ‖fourierL2 u ξ‖ ^ 2) volume :=
    (integrable_norm_sq_fourierL2 hu).add
      (integrable_finsetSum _ fun i _ => (coord_integrable hu C hC i).1)
  refine hsum.congr (Filter.Eventually.of_forall fun ξ => ?_)
  beta_reduce
  rw [Real.rpow_one]
  show _ = wt ξ * _
  have hn : ‖ξ‖ ^ 2 = ∑ i : Fin d, (ξ i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  simp only [wt, hn, ← Finset.sum_mul, ← Finset.mul_sum]
  ring


theorem bdd_of_lipschitz_memLp {w : Euc d → ℝ} {L : ℝ} (hw : IsLipschitz L w)
    (h2 : MemLp w 2 volume) : ∃ B : ℝ, ∀ x, |w x| ≤ B := by
  set L' : ℝ := max L 1 with hL'
  have hL'pos : 0 < L' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set M : ℝ := ∫ x, w x ^ 2 with hM
  set c : ℝ := (volume (Metric.ball (0 : Euc d) 1)).toReal with hc
  have hcpos : 0 < c := by
    apply ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 one_pos).ne'
    exact measure_ball_lt_top.ne
  set K : ℝ := 4 * (2 * L') ^ d * M / c with hK
  refine ⟨max 1 K, fun x0 => ?_⟩
  by_cases ha1 : |w x0| ≤ 1
  · exact ha1.trans (le_max_left _ _)
  rw [not_le] at ha1
  set a : ℝ := |w x0| with ha
  have hapos : 0 < a := lt_trans one_pos ha1
  set r : ℝ := a / (2 * L') with hr
  have hrpos : 0 < r := by positivity
  have hball : ∀ y ∈ Metric.ball x0 r, a ^ 2 / 4 ≤ w y ^ 2 := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have h1 : |w y - w x0| ≤ L' * ‖y - x0‖ := by
      refine (hw y x0).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    have h3 : L' * ‖y - x0‖ ≤ a / 2 := by
      calc L' * ‖y - x0‖ ≤ L' * r := by gcongr
        _ = a / 2 := by rw [hr]; field_simp
    have h4 : a / 2 ≤ |w y| := by
      have := abs_sub_abs_le_abs_sub (w x0) (w y)
      rw [abs_sub_comm] at this
      linarith
    have h5 : (a / 2) ^ 2 ≤ |w y| ^ 2 := by gcongr
    rw [sq_abs] at h5
    nlinarith
  have hint : Integrable (fun x => w x ^ 2) volume := h2.integrable_sq
  have hlow : (a ^ 2 / 4) * (volume.real (Metric.ball x0 r)) ≤ M := by
    have := integral_mono_of_nonneg (μ := volume)
      (f := (Metric.ball x0 r).indicator (fun _ => a ^ 2 / 4)) (g := fun x => w x ^ 2)
      (Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ Metric.ball x0 r
        · simp [hx]; positivity
        · simp [hx]) hint
      (Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ Metric.ball x0 r
        · simp only [Set.indicator_of_mem hx]; exact hball x hx
        · simp only [Set.indicator_of_notMem hx]; positivity)
    rw [integral_indicator_const _ Metric.isOpen_ball.measurableSet] at this
    simpa [mul_comm] using this
  have hvol : volume.real (Metric.ball x0 r) = r ^ d * c := by
    rw [Measure.real, Measure.addHaar_ball_of_pos volume x0 hrpos, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  rw [hvol] at hlow
  have hr' : r ^ d = a ^ d / (2 * L') ^ d := by rw [hr, div_pow]
  have hkey : a ^ (d + 2) ≤ K := by
    rw [hK, le_div_iff₀ hcpos]
    rw [hr'] at hlow
    have hp : 0 < (2 * L') ^ d := by positivity
    have : a ^ (d + 2) * c ≤ 4 * (2 * L') ^ d * M := by
      have e : a ^ 2 / 4 * (a ^ d / (2 * L') ^ d * c) = a ^ (d + 2) * c / (4 * (2 * L') ^ d) := by
        rw [pow_add]; field_simp
      rw [e, div_le_iff₀ (by positivity)] at hlow
      linarith
    exact this
  have : a ≤ a ^ (d + 2) := by
    calc a = a ^ 1 := (pow_one a).symm
      _ ≤ a ^ (d + 2) := pow_le_pow_right₀ ha1.le (by omega)
  exact (this.trans hkey).trans (le_max_right _ _)


theorem continuous_of_isLipschitz {b : Euc d → ℝ} {L : ℝ} (hb : IsLipschitz L b) : Continuous b := by
  have : LipschitzWith (Real.toNNReal L) b := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm]
    refine (hb x y).trans ?_
    have : L ≤ (Real.toNNReal L : ℝ) := Real.le_coe_toNNReal L
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  exact this.continuous

theorem memSobolev_one_mul {b h : Euc d → ℝ} {Lb : ℝ} (hb : IsLipschitz Lb b)
    (hbb : ∃ B : ℝ, ∀ x, |b x| ≤ B) (hh : MemSobolev 1 h) :
    MemSobolev 1 (fun x => b x * h x) := by
  obtain ⟨B, hB⟩ := hbb
  have hbm : MemLp b ⊤ volume :=
    memLp_top_of_bound (continuous_of_isLipschitz hb).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by simpa using hB x)
  have hbh : MemLp (fun x => b x * h x) 2 volume := by
    have := hh.1.fun_mul (r := 2) hbm
    simpa only [mul_comm] using this
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine memSobolev_one_of_diff_bound hbh (2 * B ^ 2 * sobolevNormSq 1 h +
    2 * Lb ^ 2 * ∫ x, h x ^ 2) fun k => ?_
  have hD : MemLp (fun x => h x - h (x - k)) 2 volume := hh.1.sub (memLp_translate hh.1 k)
  have hs : MemLp (fun x => h (x - k)) 2 volume := memLp_translate hh.1 k
  have hbk : MemLp (fun x => b x * h x - b (x - k) * h (x - k)) 2 volume :=
    hbh.sub (memLp_translate hbh k)
  have hpt : ∀ x, (b x * h x - b (x - k) * h (x - k)) ^ 2 ≤
      2 * B ^ 2 * (h x - h (x - k)) ^ 2 + 2 * (Lb ^ 2 * ‖k‖ ^ 2) * h (x - k) ^ 2 := by
    intro x
    have e : b x * h x - b (x - k) * h (x - k) =
        b x * (h x - h (x - k)) + h (x - k) * (b x - b (x - k)) := by ring
    have h1 : (b x * (h x - h (x - k))) ^ 2 ≤ B ^ 2 * (h x - h (x - k)) ^ 2 := by
      rw [mul_pow]
      have : b x ^ 2 ≤ B ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
      gcongr
    have h2 : (h (x - k) * (b x - b (x - k))) ^ 2 ≤ (Lb ^ 2 * ‖k‖ ^ 2) * h (x - k) ^ 2 := by
      rw [mul_pow]
      have hl := hb x (x - k)
      rw [sub_sub_cancel] at hl
      have : (b x - b (x - k)) ^ 2 ≤ (Lb * ‖k‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hl 2
      rw [mul_pow] at this
      nlinarith [sq_nonneg (h (x - k))]
    rw [e]
    nlinarith [sq_nonneg (b x * (h x - h (x - k)) - h (x - k) * (b x - b (x - k)))]
  have hi1 : Integrable (fun x => (h x - h (x - k)) ^ 2) volume := hD.integrable_sq
  have hi2 : Integrable (fun x => h (x - k) ^ 2) volume := hs.integrable_sq
  calc ∫ x, (b x * h x - b (x - k) * h (x - k)) ^ 2
      ≤ ∫ x, (2 * B ^ 2 * (h x - h (x - k)) ^ 2 + 2 * (Lb ^ 2 * ‖k‖ ^ 2) * h (x - k) ^ 2) :=
        integral_mono hbk.integrable_sq ((hi1.const_mul _).add (hi2.const_mul _)) hpt
    _ = 2 * B ^ 2 * (∫ x, (h x - h (x - k)) ^ 2) + 2 * (Lb ^ 2 * ‖k‖ ^ 2) * ∫ x, h x ^ 2 := by
        have key : ∫ x, h (x - k) ^ 2 = ∫ x : Euc d, h x ^ 2 :=
          integral_sub_right_eq_self (μ := volume) (fun x => h x ^ 2) k
        rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
          integral_const_mul, key]
    _ ≤ _ := by
        have := diff_sq_le hh k
        have hS : 0 ≤ ‖k‖ ^ 2 := sq_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 2 * B ^ 2)]


theorem measurable_of_homog {θ : ℝ} {m : Euc d → ℝ} (hm : IsHomogSymbol θ m) : Measurable m := by
  have hs : MeasurableSet {ξ : Euc d | ξ ≠ 0} := (isOpen_ne.measurableSet)
  have h1 : ContinuousOn m {ξ : Euc d | ξ ≠ 0} := hm.smooth.continuousOn
  have h2 : Measurable ({ξ : Euc d | ξ ≠ 0}.piecewise m (fun _ => 0)) :=
    h1.measurable_piecewise continuousOn_const hs
  convert h2 using 1
  ext ξ
  by_cases hξ : ξ = 0
  · subst hξ; simp [hm.zero]
  · rw [Set.piecewise_eq_of_mem _ _ _ (show ξ ∈ {ξ : Euc d | ξ ≠ 0} from hξ)]

theorem symbol_bound {θ : ℝ} (hθ : 0 < θ) {m : Euc d → ℝ} (hm : IsHomogSymbol θ m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ, m ξ ≤ A * wt ξ ^ (θ / 2) := by
  have hcomp : IsCompact (Metric.sphere (0 : Euc d) 1) := isCompact_sphere 0 1
  have hcont : ContinuousOn m (Metric.sphere (0 : Euc d) 1) := by
    refine hm.smooth.continuousOn.mono ?_
    intro x hx
    have : ‖x‖ = 1 := by simpa using hx
    intro h0; rw [h0] at this; simp at this
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun ξ => ?_⟩
  by_cases hξ : ξ = 0
  · subst hξ
    rw [hm.zero]; have := wt_pos (d := d) 0; positivity
  · have hc : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    set η : Euc d := ‖ξ‖⁻¹ • ξ with hη
    have hηS : η ∈ Metric.sphere (0 : Euc d) 1 := by
      rw [mem_sphere_zero_iff_norm, hη, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hc.ne']
    have hmη : m η ≤ max C 0 := by
      have := hC η hηS
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    have h1 : m ξ = ‖ξ‖ ^ θ * m η := by
      rw [← hm.homog ‖ξ‖ hc η, hη, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    have h2 : ‖ξ‖ ^ θ ≤ wt ξ ^ (θ / 2) := by
      have e : ‖ξ‖ ^ θ = (‖ξ‖ ^ 2) ^ (θ / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; congr 1; push_cast; ring
      rw [e]
      apply Real.rpow_le_rpow (by positivity) _ (by linarith)
      unfold wt
      have hp : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg ‖ξ‖)]
    rw [h1]
    have h3 : 0 ≤ ‖ξ‖ ^ θ := Real.rpow_nonneg hc.le _
    calc ‖ξ‖ ^ θ * m η ≤ ‖ξ‖ ^ θ * max C 0 := by gcongr
      _ ≤ wt ξ ^ (θ / 2) * max C 0 := by gcongr
      _ = _ := by ring


theorem symbolForm_eq_re (m : Euc d → ℝ) (u v : Euc d → ℝ) :
    symbolForm m u v = (∫ ξ, ((m ξ : ℝ) : ℂ) * (fourierL2 u ξ * conj (fourierL2 v ξ))).re := rfl

theorem symbolForm_comm (m : Euc d → ℝ) (u v : Euc d → ℝ) :
    symbolForm m u v = symbolForm m v u := by
  rw [symbolForm_eq_re, symbolForm_eq_re]
  have : (∫ ξ, ((m ξ : ℝ) : ℂ) * (fourierL2 v ξ * conj (fourierL2 u ξ))) =
      conj (∫ ξ, ((m ξ : ℝ) : ℂ) * (fourierL2 u ξ * conj (fourierL2 v ξ))) := by
    rw [← integral_conj]
    congr 1; ext ξ
    simp [mul_comm]
  rw [this, Complex.conj_re]

theorem symbolForm_self_eq (m : Euc d → ℝ) (u : Euc d → ℝ) :
    symbolForm m u u = ∫ ξ, m ξ * ‖fourierL2 u ξ‖ ^ 2 := by
  rw [symbolForm_eq_re]
  have : (∫ ξ, ((m ξ : ℝ) : ℂ) * (fourierL2 u ξ * conj (fourierL2 u ξ))) =
      ((∫ ξ, m ξ * ‖fourierL2 u ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal (μ := volume) (f := fun ξ => m ξ * ‖fourierL2 u ξ‖ ^ 2)]
    congr 1; ext ξ
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [this, Complex.ofReal_re]

/-- the form is nonnegative on the diagonal (for any `u`; uses `m ≥ 0`). -/
theorem symbolForm_self_nonneg {θ : ℝ} {m : Euc d → ℝ} (hm : IsHomogSymbol θ m) (u : Euc d → ℝ) :
    0 ≤ symbolForm m u u := by
  rw [symbolForm_self_eq]
  exact integral_nonneg fun ξ => mul_nonneg (hm.nonneg ξ) (sq_nonneg _)

theorem integrable_m_sq {θ : ℝ} (hθ : 0 < θ) {m : Euc d → ℝ} (hm : IsHomogSymbol θ m)
    {u : Euc d → ℝ} (hu : MemSobolev (θ / 2) u) :
    Integrable (fun ξ => m ξ * ‖fourierL2 u ξ‖ ^ 2) volume := by
  obtain ⟨A, hA0, hA⟩ := symbol_bound hθ hm
  refine Integrable.mono' (hu.2.const_mul A)
    ((measurable_of_homog hm).aestronglyMeasurable.mul (aesm_sq (aestronglyMeasurable_fourierL2 hu.1)))
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (hm.nonneg ξ) (sq_nonneg _))]
  change _ ≤ A * (wt ξ ^ (θ / 2) * _)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hA ξ) (sq_nonneg _)

theorem integrable_form {θ : ℝ} (hθ : 0 < θ) {m : Euc d → ℝ} (hm : IsHomogSymbol θ m)
    {u v : Euc d → ℝ} (hu : MemSobolev (θ / 2) u) (hv : MemSobolev (θ / 2) v) :
    Integrable (fun ξ => ((m ξ : ℝ) : ℂ) * (fourierL2 u ξ * conj (fourierL2 v ξ))) volume := by
  have hmu := integrable_m_sq hθ hm hu
  have hmv := integrable_m_sq hθ hm hv
  have hau := aestronglyMeasurable_fourierL2 hu.1
  have hav := aestronglyMeasurable_fourierL2 hv.1
  refine Integrable.mono' ((hmu.add hmv).div_const 2)
    ((Complex.measurable_ofReal.comp (measurable_of_homog hm)).aestronglyMeasurable.mul
      (hau.mul (Complex.continuous_conj.comp_aestronglyMeasurable hav)))
    (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_of_nonneg (hm.nonneg ξ),
    Pi.add_apply]
  have := hm.nonneg ξ
  nlinarith [sq_nonneg (‖fourierL2 u ξ‖ - ‖fourierL2 v ξ‖), mul_nonneg this (sq_nonneg (‖fourierL2 u ξ‖ - ‖fourierL2 v ξ‖))]

theorem cs_aux {P Q R : Euc d → ℝ} (hP : Integrable P volume) (hQ : Integrable Q volume)
    (hR : Integrable R volume) (h : ∀ t ξ, 0 ≤ t ^ 2 * P ξ - 2 * t * R ξ + Q ξ) :
    (∫ ξ, R ξ) ^ 2 ≤ (∫ ξ, P ξ) * (∫ ξ, Q ξ) := by
  have h1 : ∀ t : ℝ, 0 ≤ (∫ ξ, P ξ) * (t * t) + (-2 * ∫ ξ, R ξ) * t + ∫ ξ, Q ξ := by
    intro t
    have : ∫ ξ, (t ^ 2 * P ξ - 2 * t * R ξ + Q ξ) =
        (∫ ξ, P ξ) * (t * t) + (-2 * ∫ ξ, R ξ) * t + ∫ ξ, Q ξ := by
      rw [integral_add (f := fun ξ => t ^ 2 * P ξ - 2 * t * R ξ) (g := Q)
        ((hP.const_mul _).sub (hR.const_mul _)) hQ,
        integral_sub (hP.const_mul _) (hR.const_mul _), integral_const_mul, integral_const_mul]
      ring
    rw [← this]
    exact integral_nonneg fun ξ => h t ξ
  have := discrim_le_zero h1
  unfold discrim at this
  nlinarith


theorem form_cauchySchwarz {θ : ℝ} (hθ : 0 < θ) {m : Euc d → ℝ} (hm : IsHomogSymbol θ m)
    {u v : Euc d → ℝ} (hu : MemSobolev (θ / 2) u) (hv : MemSobolev (θ / 2) v) :
    |symbolForm m u v| ≤ Real.sqrt (symbolForm m u u) * Real.sqrt (symbolForm m v v) := by
  have hF := integrable_form hθ hm hu hv
  have hmu := integrable_m_sq hθ hm hu
  have hmv := integrable_m_sq hθ hm hv
  set R : Euc d → ℝ := fun ξ => m ξ * (‖fourierL2 u ξ‖ * ‖fourierL2 v ξ‖) with hR
  have hRint : Integrable R volume := by
    refine hF.norm.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_of_nonneg (hm.nonneg ξ), hR]
  have h1 : |symbolForm m u v| ≤ ∫ ξ, R ξ := by
    rw [symbolForm_eq_re]
    refine (Complex.abs_re_le_norm _).trans ((norm_integral_le_integral_norm _).trans (le_of_eq ?_))
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_of_nonneg (hm.nonneg ξ), hR]
  have h2 : (∫ ξ, R ξ) ^ 2 ≤ (∫ ξ, m ξ * ‖fourierL2 u ξ‖ ^ 2) * (∫ ξ, m ξ * ‖fourierL2 v ξ‖ ^ 2) := by
    refine cs_aux hmu hmv hRint fun t ξ => ?_
    have : t ^ 2 * (m ξ * ‖fourierL2 u ξ‖ ^ 2) - 2 * t * R ξ + m ξ * ‖fourierL2 v ξ‖ ^ 2 =
        m ξ * (t * ‖fourierL2 u ξ‖ - ‖fourierL2 v ξ‖) ^ 2 := by simp only [hR]; ring
    rw [this]
    exact mul_nonneg (hm.nonneg ξ) (sq_nonneg _)
  rw [symbolForm_self_eq, symbolForm_self_eq, ← Real.sqrt_mul
    (integral_nonneg fun ξ => mul_nonneg (hm.nonneg ξ) (sq_nonneg _))]
  exact h1.trans ((le_abs_self _).trans (Real.abs_le_sqrt h2))

theorem form_basic {θ : ℝ} (hθ : 0 < θ) {m : Euc d → ℝ} (hm : IsHomogSymbol θ m) :
    ∃ C : ℝ, ∀ u v : Euc d → ℝ, MemSobolev (θ / 2) u → MemSobolev (θ / 2) v →
      Integrable (fun ξ => m ξ * ‖fourierL2 u ξ‖ ^ 2) ∧ Integrable (fun ξ => m ξ * ‖fourierL2 v ξ‖ ^ 2) ∧
      Integrable (fun ξ => ((m ξ : ℝ) : ℂ) * (fourierL2 u ξ * conj (fourierL2 v ξ))) ∧
      symbolForm m u v = symbolForm m v u ∧ 0 ≤ symbolForm m u u ∧
      symbolForm m u u ≤ C * sobolevNormSq (θ / 2) u := by
  obtain ⟨A, hA0, hA⟩ := symbol_bound hθ hm
  refine ⟨A, fun u v hu hv => ⟨integrable_m_sq hθ hm hu, integrable_m_sq hθ hm hv,
    integrable_form hθ hm hu hv, symbolForm_comm m u v, symbolForm_self_nonneg hm u, ?_⟩⟩
  rw [symbolForm_self_eq, sobolevNormSq_eq, ← integral_const_mul]
  refine integral_mono (integrable_m_sq hθ hm hu) (hu.2.const_mul A) fun ξ => ?_
  change _ ≤ A * (wt ξ ^ (θ / 2) * _)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hA ξ) (sq_nonneg _)


/-- pointwise complex conjugation on `L²` -/
def conjLp : Lp (α := Euc d) ℂ 2 → Lp (α := Euc d) ℂ 2 :=
  (Complex.conjLIE.lipschitz : LipschitzWith 1 (conj : ℂ → ℂ)).compLp (map_zero _)

theorem conjLp_coe (f : Lp (α := Euc d) ℂ 2) :
    (conjLp f : Euc d → ℂ) =ᵐ[volume] fun ξ => conj (f ξ) :=
  LipschitzWith.coeFn_compLp _ _ _

theorem continuous_conjLp : Continuous (conjLp : Lp (α := Euc d) ℂ 2 → Lp (α := Euc d) ℂ 2) :=
  LipschitzWith.continuous_compLp _ _

/-- reflection on `L²` -/
def negLp : Lp (α := Euc d) ℂ 2 → Lp (α := Euc d) ℂ 2 :=
  Lp.compMeasurePreserving (fun x : Euc d => -x) (Measure.measurePreserving_neg volume)

theorem negLp_coe (f : Lp (α := Euc d) ℂ 2) :
    (negLp f : Euc d → ℂ) =ᵐ[volume] fun ξ => f (-ξ) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem continuous_negLp : Continuous (negLp : Lp (α := Euc d) ℂ 2 → Lp (α := Euc d) ℂ 2) :=
  (Lp.isometry_compMeasurePreserving _).continuous


/-- conjugated Schwartz function -/
def conjSchwartz (φ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ :=
  φ.postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem conjSchwartz_apply (φ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    conjSchwartz φ x = conj (φ x) := rfl

theorem fourier_conjSchwartz (φ : SchwartzMap (Euc d) ℂ) (ξ : Euc d) :
    (𝓕 (conjSchwartz φ) : SchwartzMap (Euc d) ℂ) ξ = conj ((𝓕 φ : SchwartzMap (Euc d) ℂ) (-ξ)) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq', Real.fourier_eq',
    ← integral_conj]
  congr 1; ext x
  simp only [conjSchwartz_apply, smul_eq_mul, map_mul, ← Complex.exp_conj]
  refine congrArg₂ (· * ·) ?_ rfl
  congr 1
  rw [Complex.conj_ofReal, Complex.conj_I, inner_neg_right]
  push_cast; ring

theorem conjLp_toLp (φ : SchwartzMap (Euc d) ℂ) :
    conjLp (φ.toLp 2) = (conjSchwartz φ).toLp 2 := by
  apply Lp.ext
  filter_upwards [conjLp_coe (φ.toLp 2 : Lp (α := Euc d) ℂ 2), SchwartzMap.coeFn_toLp φ 2 volume,
    SchwartzMap.coeFn_toLp (conjSchwartz φ) 2 volume] with x a b c
  rw [c, a, b]; rfl

theorem toLp_conj_aux (g g' : SchwartzMap (Euc d) ℂ) (h : ∀ ξ, g' ξ = conj (g (-ξ))) :
    g'.toLp 2 = negLp (conjLp (g.toLp 2)) := by
  apply Lp.ext
  have hq := (Measure.measurePreserving_neg (volume : Measure (Euc d))).quasiMeasurePreserving
  have h1 := negLp_coe (conjLp (g.toLp 2))
  have h2 := hq.ae_eq_comp (conjLp_coe (g.toLp 2))
  have h3 := hq.ae_eq_comp (SchwartzMap.coeFn_toLp g 2 volume)
  have h4 := SchwartzMap.coeFn_toLp g' 2 volume
  filter_upwards [h1, h2, h3, h4] with ξ a b c e
  rw [e, a]
  simp only [Function.comp_apply] at b c
  rw [b, c, h]

theorem fourier_conjLp (f : Lp (α := Euc d) ℂ 2) :
    FT d (conjLp f) = negLp (conjLp (FT d f)) := by
  refine (SchwartzMap.denseRange_toLpCLM (E := Euc d) (F := ℂ) (p := 2)
    ENNReal.ofNat_ne_top).induction_on f (isClosed_eq ?_ ?_) ?_
  · exact (FT d).continuous.comp continuous_conjLp
  · exact continuous_negLp.comp (continuous_conjLp.comp (FT d).continuous)
  · intro φ
    simp only [SchwartzMap.toLpCLM_apply]
    rw [conjLp_toLp]
    have e1 : FT d ((conjSchwartz φ).toLp 2) = ((𝓕 (conjSchwartz φ) : SchwartzMap (Euc d) ℂ)).toLp 2 :=
      SchwartzMap.toLp_fourier_eq _
    have e2 : FT d (φ.toLp 2) = ((𝓕 φ : SchwartzMap (Euc d) ℂ)).toLp 2 :=
      SchwartzMap.toLp_fourier_eq _
    rw [e1, e2]
    exact toLp_conj_aux _ _ (fourier_conjSchwartz φ)

/-- Hermitian symmetry of the `L²` Fourier transform of a real function. -/
theorem fourierL2_neg {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    ∀ᵐ ξ ∂(volume : Measure (Euc d)), fourierL2 u (-ξ) = conj (fourierL2 u ξ) := by
  have hc : conjLp (ofRealLp hu) = ofRealLp hu := by
    apply Lp.ext
    filter_upwards [conjLp_coe (ofRealLp hu), ofRealLp_coe hu] with x a b
    rw [a, b]; simp
  have h := fourier_conjLp (ofRealLp hu)
  rw [hc] at h
  have hq := (Measure.measurePreserving_neg (volume : Measure (Euc d))).quasiMeasurePreserving
  have h' : ∀ ξ, (FT d (ofRealLp hu) : Euc d → ℂ) ξ =
      (negLp (conjLp (FT d (ofRealLp hu))) : Euc d → ℂ) ξ := fun ξ => by rw [← h]
  have h2 : ∀ᵐ ξ ∂(volume : Measure (Euc d)), (FT d (ofRealLp hu) : Euc d → ℂ) ξ =
      conj ((FT d (ofRealLp hu) : Euc d → ℂ) (-ξ)) := by
    have h5 := negLp_coe (conjLp (FT d (ofRealLp hu)))
    have h6 := conjLp_coe (FT d (ofRealLp hu))
    have h7 := hq.ae_eq_comp h6
    filter_upwards [h5, h7] with ξ a c
    simp only [Function.comp_apply] at c
    rw [h' ξ, a, c]
  have h3 := hq.ae h2
  rw [fourierL2_eq hu]
  filter_upwards [h3] with ξ hξ
  rw [neg_neg] at hξ
  exact hξ


/-- Agreement with the pointwise Fourier integral `𝓕` for real Schwartz functions. -/
theorem fourierL2_schwartz (u : SchwartzMap (Euc d) ℝ) :
    fourierL2 (⇑u) =ᵐ[volume] 𝓕 (fun x : Euc d => ((u x : ℝ) : ℂ)) := by
  have hu : MemLp (⇑u) 2 volume := u.memLp 2 volume
  set φ : SchwartzMap (Euc d) ℂ := u.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM with hφ
  have h1 : ofRealLp hu = φ.toLp 2 := by
    apply Lp.ext
    filter_upwards [ofRealLp_coe hu, SchwartzMap.coeFn_toLp φ 2 volume] with x a b
    rw [a, b]; rfl
  have e : FT d (φ.toLp 2) = ((𝓕 φ : SchwartzMap (Euc d) ℂ)).toLp 2 :=
    SchwartzMap.toLp_fourier_eq _
  rw [fourierL2_eq hu, h1, e]
  filter_upwards [SchwartzMap.coeFn_toLp (𝓕 φ : SchwartzMap (Euc d) ℂ) 2 volume] with ξ a
  rw [a, SchwartzMap.fourier_coe]
  rfl


/-- Plancherel (polarized, real form): `∫ u v = Re ∫ û \bar{v̂}`. -/
theorem integral_mul_eq_re_fourierL2 {u v : Euc d → ℝ} (hu : MemLp u 2 volume)
    (hv : MemLp v 2 volume) :
    ∫ x, u x * v x = (∫ ξ, fourierL2 u ξ * conj (fourierL2 v ξ)).re := by
  rw [integral_fourierL2_mul_conj hu hv, Complex.ofReal_re]

end HRS.PDE.ToolboxRd.FourierAux
