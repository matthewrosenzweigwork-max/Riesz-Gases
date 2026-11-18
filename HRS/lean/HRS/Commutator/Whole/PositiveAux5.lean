import HRS.Commutator.Whole.PositiveAux4

/-!
# Helpers for `Positive.lean` (packet `CMX-POS`), part E

Signed measures as `h • m`, and the Fourier quadratic form for the Gaussian-mixture kernels.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- A finite signed measure `σ = σ⁺ - σ⁻` is `h • m` for the finite measure `m = σ⁺ + σ⁻` and a
measurable function `h` with `|h| ≤ 1`. -/
theorem SMeas.exists_density (σ : SMeas d) (hf : σ.IsFinite) :
    ∃ (m : Measure (Euc d)) (h : Euc d → ℝ), IsFiniteMeasure m ∧ Measurable h ∧ (∀ x, |h x| ≤ 1) ∧
      σ.pos ≤ m ∧ σ.neg ≤ m ∧ m = σ.pos + σ.neg ∧
      ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (f : Euc d → F),
        Integrable f m → ∫ x, f x ∂σ.pos - ∫ x, f x ∂σ.neg = ∫ x, h x • f x ∂m := by
  obtain ⟨h1, h2⟩ := hf
  haveI := h1
  haveI := h2
  set m : Measure (Euc d) := σ.pos + σ.neg with hm
  have hmfin : IsFiniteMeasure m := by rw [hm]; infer_instance
  haveI := hmfin
  haveI : σ.pos.HaveLebesgueDecomposition (σ.pos + σ.neg) :=
    Measure.haveLebesgueDecomposition_of_sigmaFinite _ _
  haveI : σ.neg.HaveLebesgueDecomposition (σ.pos + σ.neg) :=
    Measure.haveLebesgueDecomposition_of_sigmaFinite _ _
  have hp : σ.pos ≤ m := Measure.le_add_right le_rfl
  have hn : σ.neg ≤ m := Measure.le_add_left le_rfl
  have hpa : σ.pos ≪ m := Measure.absolutelyContinuous_of_le hp
  have hna : σ.neg ≪ m := Measure.absolutelyContinuous_of_le hn
  set h₀ : Euc d → ℝ := fun x => (σ.pos.rnDeriv m x).toReal - (σ.neg.rnDeriv m x).toReal with hh₀
  set h : Euc d → ℝ := fun x => max (-1) (min 1 (h₀ x)) with hh
  have hmeas : Measurable h := by
    have : Measurable h₀ := by
      refine Measurable.sub ?_ ?_
      · exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
      · exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
    exact measurable_const.max (measurable_const.min this)
  have hbd : ∀ x, |h x| ≤ 1 := by
    intro x
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  have hae : h =ᵐ[m] h₀ := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hp, Measure.rnDeriv_le_one_of_le hn] with x hx1 hx2
    have a1 : (σ.pos.rnDeriv m x).toReal ≤ 1 := by
      have := ENNReal.toReal_mono ENNReal.one_ne_top hx1
      simpa using this
    have a2 : (σ.neg.rnDeriv m x).toReal ≤ 1 := by
      have := ENNReal.toReal_mono ENNReal.one_ne_top hx2
      simpa using this
    have b1 : 0 ≤ (σ.pos.rnDeriv m x).toReal := ENNReal.toReal_nonneg
    have b2 : 0 ≤ (σ.neg.rnDeriv m x).toReal := ENNReal.toReal_nonneg
    simp only [hh, hh₀]
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  refine ⟨m, h, hmfin, hmeas, hbd, hp, hn, hm, ?_⟩
  intro F _ _ _ f hint
  have i1 : Integrable (fun x => (σ.pos.rnDeriv m x).toReal • f x) m :=
    (integrable_rnDeriv_smul_iff hpa).2 (hint.mono_measure hp)
  have i2 : Integrable (fun x => (σ.neg.rnDeriv m x).toReal • f x) m :=
    (integrable_rnDeriv_smul_iff hna).2 (hint.mono_measure hn)
  rw [← integral_rnDeriv_smul hpa, ← integral_rnDeriv_smul hna, ← integral_sub i1 i2]
  have : (fun x => h x • f x) =ᵐ[m] (fun x => (σ.pos.rnDeriv m x).toReal • f x - (σ.neg.rnDeriv m x).toReal • f x) := by
    filter_upwards [hae] with x hx
    rw [hx]; simp only [hh₀, sub_smul]
  rw [integral_congr_ae this]


/-- Fourier inversion for `φ`, in real form. -/
lemma phi_inv (z : Euc d) :
    phi z = ∫ ξ : Euc d, phiHatR d ‖ξ‖ * Real.cos (2 * Real.pi * inner ℝ z ξ) := by
  have hf : Integrable (fun x : Euc d => ((phi x : ℝ) : ℂ)) := integrable_phi.ofReal
  have hF2 : 𝓕 (fun x : Euc d => ((phi x : ℝ) : ℂ)) = fun η => ((phiHatR d ‖η‖ : ℝ) : ℂ) :=
    funext fourier_phi
  have hFi : Integrable (𝓕 (fun x : Euc d => ((phi x : ℝ) : ℂ))) := by
    rw [hF2]; exact integrable_phiHat.ofReal
  have hc : Continuous (fun x : Euc d => ((phi x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_phi
  have h2 := congrFun (hc.fourierInv_fourier_eq hf hFi) z
  rw [hF2, Real.fourierInv_eq'] at h2
  have h3 := congrArg Complex.re h2
  have hint : Integrable (fun v : Euc d => Complex.exp (↑(2 * Real.pi * inner ℝ v z) * Complex.I) •
      ((phiHatR d ‖v‖ : ℝ) : ℂ)) := by
    refine integrable_phiHat.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · have := continuous_phiHatR (d := d)
      exact (by fun_prop : Continuous (fun v : Euc d => Complex.exp (↑(2 * Real.pi * inner ℝ v z) * Complex.I) •
        ((phiHatR d ‖v‖ : ℝ) : ℂ))).aestronglyMeasurable
    · rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (phiHatR_pos _).le]
  have h4 := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at h4
  rw [← h4] at h3
  rw [Complex.ofReal_re] at h3
  rw [← h3]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, real_inner_comm]


lemma phi_scaled {t : ℝ} (ht : 0 < t) (z : Euc d) :
    phi (t⁻¹ • z) = ∫ ξ : Euc d, (t ^ d * phiHatR d (t * ‖ξ‖)) * Real.cos (2 * Real.pi * inner ℝ z ξ) := by
  rw [phi_inv]
  have := Measure.integral_comp_smul_of_nonneg (volume : Measure (Euc d))
    (fun η : Euc d => phiHatR d ‖η‖ * Real.cos (2 * Real.pi * inner ℝ (t⁻¹ • z) η)) t (hR := ht.le)
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at this
  have h2 : ∫ η : Euc d, phiHatR d ‖η‖ * Real.cos (2 * Real.pi * inner ℝ (t⁻¹ • z) η) =
      t ^ d * ∫ ξ : Euc d, phiHatR d ‖t • ξ‖ * Real.cos (2 * Real.pi * inner ℝ (t⁻¹ • z) (t • ξ)) := by
    rw [this, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  rw [h2, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  have : t⁻¹ * (t * inner ℝ z ξ) = inner ℝ z ξ := by field_simp
  rw [this]; ring


/-- Fubini between a finite measure and an integrable weight (bounded integrand). -/
lemma swap_K {m : Measure (Euc d)} [IsFiniteMeasure m] {K : Euc d → ℝ} (hK : Integrable K)
    (hKc : Continuous K)
    {g : Euc d → Euc d → ℝ} (hg : Measurable (fun p : Euc d × Euc d => g p.1 p.2)) {B : ℝ}
    (hb : ∀ y ξ, |g y ξ| ≤ B) :
    ∫ y, ∫ ξ, K ξ * g y ξ ∂volume ∂m = ∫ ξ, K ξ * ∫ y, g y ξ ∂m ∂volume := by
  have hI : Integrable (fun p : Euc d × Euc d => K p.2 * g p.1 p.2) (m.prod volume) := by
    have h1 : Integrable (fun p : Euc d × Euc d => B * ‖K p.2‖) (m.prod volume) := by
      have := Integrable.mul_prod (f := fun _ : Euc d => B) (g := fun ξ => ‖K ξ‖) (μ := m) (ν := volume)
        (integrable_const B) hK.norm
      exact this
    refine h1.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have : Measurable (fun p : Euc d × Euc d => K p.2 * g p.1 p.2) := by
        have := hKc.measurable
        fun_prop
      exact this.aestronglyMeasurable
    · rw [norm_mul, mul_comm]
      exact mul_le_mul (by simpa using hb p.1 p.2) le_rfl (norm_nonneg _) (by
        have := hb p.1 p.2; have := abs_nonneg (g p.1 p.2); linarith)
  have := integral_integral_swap (μ := m) (ν := volume) (f := fun y ξ => K ξ * g y ξ) hI
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [integral_const_mul]


/-- `∫ h cos(2π⟨x,ξ⟩) dm`. -/
def cosT (m : Measure (Euc d)) (h : Euc d → ℝ) (ξ : Euc d) : ℝ :=
  ∫ x, h x * Real.cos (2 * Real.pi * inner ℝ x ξ) ∂m

/-- `∫ h sin(2π⟨x,ξ⟩) dm`. -/
def sinT (m : Measure (Euc d)) (h : Euc d → ℝ) (ξ : Euc d) : ℝ :=
  ∫ x, h x * Real.sin (2 * Real.pi * inner ℝ x ξ) ∂m

lemma continuous_cosT {m : Measure (Euc d)} [IsFiniteMeasure m] {h : Euc d → ℝ} (hh : Measurable h)
    (hb : ∀ x, |h x| ≤ 1) : Continuous (cosT m h) := by
  unfold cosT
  refine continuous_of_dominated (bound := fun _ => 1) ?_ ?_ (integrable_const _) ?_
  · intro ξ
    exact (by fun_prop : Measurable (fun x : Euc d => h x * Real.cos (2 * Real.pi * inner ℝ x ξ))).aestronglyMeasurable
  · intro ξ
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    calc |h x| * |Real.cos (2 * Real.pi * inner ℝ x ξ)| ≤ 1 * 1 :=
          mul_le_mul (hb x) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · refine Filter.Eventually.of_forall fun x => ?_
    fun_prop

lemma continuous_sinT {m : Measure (Euc d)} [IsFiniteMeasure m] {h : Euc d → ℝ} (hh : Measurable h)
    (hb : ∀ x, |h x| ≤ 1) : Continuous (sinT m h) := by
  unfold sinT
  refine continuous_of_dominated (bound := fun _ => 1) ?_ ?_ (integrable_const _) ?_
  · intro ξ
    exact (by fun_prop : Measurable (fun x : Euc d => h x * Real.sin (2 * Real.pi * inner ℝ x ξ))).aestronglyMeasurable
  · intro ξ
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    calc |h x| * |Real.sin (2 * Real.pi * inner ℝ x ξ)| ≤ 1 * 1 :=
          mul_le_mul (hb x) (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · refine Filter.Eventually.of_forall fun x => ?_
    fun_prop

lemma abs_cosT_le {m : Measure (Euc d)} [IsFiniteMeasure m] {h : Euc d → ℝ}
    (hb : ∀ x, |h x| ≤ 1) (ξ : Euc d) : |cosT m h ξ| ≤ m.real Set.univ := by
  unfold cosT
  have := norm_integral_le_of_norm_le_const (μ := m) (C := 1)
    (f := fun x => h x * Real.cos (2 * Real.pi * inner ℝ x ξ)) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |h x| * |Real.cos (2 * Real.pi * inner ℝ x ξ)| ≤ 1 * 1 :=
            mul_le_mul (hb x) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1)
  simpa using this

lemma abs_sinT_le {m : Measure (Euc d)} [IsFiniteMeasure m] {h : Euc d → ℝ}
    (hb : ∀ x, |h x| ≤ 1) (ξ : Euc d) : |sinT m h ξ| ≤ m.real Set.univ := by
  unfold sinT
  have := norm_integral_le_of_norm_le_const (μ := m) (C := 1)
    (f := fun x => h x * Real.sin (2 * Real.pi * inner ℝ x ξ)) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |h x| * |Real.sin (2 * Real.pi * inner ℝ x ξ)| ≤ 1 * 1 :=
            mul_le_mul (hb x) (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1)
  simpa using this


lemma integrable_h_trig {m : Measure (Euc d)} [IsFiniteMeasure m] {h : Euc d → ℝ} (hh : Measurable h)
    (hb : ∀ x, |h x| ≤ 1) (ξ : Euc d) :
    Integrable (fun x : Euc d => h x * Real.cos (2 * Real.pi * inner ℝ x ξ)) m ∧
    Integrable (fun x : Euc d => h x * Real.sin (2 * Real.pi * inner ℝ x ξ)) m := by
  constructor
  · refine Integrable.mono' (integrable_const (1:ℝ))
      (by fun_prop : Measurable (fun x : Euc d => h x * Real.cos (2 * Real.pi * inner ℝ x ξ))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |h x| * |Real.cos (2 * Real.pi * inner ℝ x ξ)| ≤ 1 * 1 :=
          mul_le_mul (hb x) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · refine Integrable.mono' (integrable_const (1:ℝ))
      (by fun_prop : Measurable (fun x : Euc d => h x * Real.sin (2 * Real.pi * inner ℝ x ξ))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |h x| * |Real.sin (2 * Real.pi * inner ℝ x ξ)| ≤ 1 * 1 :=
          mul_le_mul (hb x) (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1

lemma Q_pair {m : Measure (Euc d)} [IsFiniteMeasure m] {h : Euc d → ℝ} (hh : Measurable h)
    (hb : ∀ x, |h x| ≤ 1) {K : Euc d → ℝ} (hK : Integrable K) (hKc : Continuous K)
    {k : Euc d → ℝ} (hk : ∀ z, k z = ∫ ξ, K ξ * Real.cos (2 * Real.pi * inner ℝ z ξ)) :
    ∫ x, h x * ∫ y, h y * k (x - y) ∂m ∂m = ∫ ξ, K ξ * (cosT m h ξ ^ 2 + sinT m h ξ ^ 2) := by
  have step1 : ∀ x : Euc d, ∫ y, h y * k (x - y) ∂m = ∫ ξ, K ξ * (Real.cos (2 * Real.pi * inner ℝ x ξ) *
      cosT m h ξ + Real.sin (2 * Real.pi * inner ℝ x ξ) * sinT m h ξ) := by
    intro x
    have e : ∀ y, h y * k (x - y) = ∫ ξ, K ξ * (h y * Real.cos (2 * Real.pi * inner ℝ (x - y) ξ)) := by
      intro y
      rw [hk, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only; ring
    simp_rw [e]
    rw [swap_K (m := m) (g := fun y ξ => h y * Real.cos (2 * Real.pi * inner ℝ (x - y) ξ)) hK hKc
      (by fun_prop) (B := 1) (fun y ξ => by
        rw [abs_mul]
        calc |h y| * |Real.cos (2 * Real.pi * inner ℝ (x - y) ξ)| ≤ 1 * 1 :=
              mul_le_mul (hb y) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only
    congr 1
    have e2 : ∀ y : Euc d, h y * Real.cos (2 * Real.pi * inner ℝ (x - y) ξ) =
        Real.cos (2 * Real.pi * inner ℝ x ξ) * (h y * Real.cos (2 * Real.pi * inner ℝ y ξ)) +
        Real.sin (2 * Real.pi * inner ℝ x ξ) * (h y * Real.sin (2 * Real.pi * inner ℝ y ξ)) := by
      intro y
      rw [inner_sub_left, mul_sub, Real.cos_sub]; ring
    simp_rw [e2]
    obtain ⟨i1, i2⟩ := integrable_h_trig (m := m) hh hb ξ
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
    rfl
  simp_rw [step1]
  have e3 : ∀ x : Euc d, h x * ∫ ξ, K ξ * (Real.cos (2 * Real.pi * inner ℝ x ξ) * cosT m h ξ +
      Real.sin (2 * Real.pi * inner ℝ x ξ) * sinT m h ξ) =
      ∫ ξ, K ξ * (h x * (Real.cos (2 * Real.pi * inner ℝ x ξ) * cosT m h ξ +
      Real.sin (2 * Real.pi * inner ℝ x ξ) * sinT m h ξ)) := by
    intro x
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only; ring
  simp_rw [e3]
  have hcc := continuous_cosT (m := m) hh hb
  have hss := continuous_sinT (m := m) hh hb
  have hM : (0:ℝ) ≤ m.real Set.univ := measureReal_nonneg
  rw [swap_K (m := m) (g := fun x ξ => h x * (Real.cos (2 * Real.pi * inner ℝ x ξ) * cosT m h ξ +
      Real.sin (2 * Real.pi * inner ℝ x ξ) * sinT m h ξ)) hK hKc
      (by
        have := hcc.measurable; have := hss.measurable
        fun_prop) (B := 2 * m.real Set.univ) (fun x ξ => by
        rw [abs_mul]
        have h1 : |Real.cos (2 * Real.pi * inner ℝ x ξ) * cosT m h ξ +
            Real.sin (2 * Real.pi * inner ℝ x ξ) * sinT m h ξ| ≤ 2 * m.real Set.univ := by
          calc _ ≤ |Real.cos (2 * Real.pi * inner ℝ x ξ) * cosT m h ξ| +
              |Real.sin (2 * Real.pi * inner ℝ x ξ) * sinT m h ξ| := abs_add_le _ _
            _ ≤ m.real Set.univ + m.real Set.univ := by
              rw [abs_mul, abs_mul]
              exact add_le_add
                (le_trans (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)) (abs_cosT_le hb ξ))
                (le_trans (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)) (abs_sinT_le hb ξ))
            _ = 2 * m.real Set.univ := by ring
        calc |h x| * _ ≤ 1 * (2 * m.real Set.univ) := mul_le_mul (hb x) h1 (abs_nonneg _) zero_le_one
          _ = _ := one_mul _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  congr 1
  have e4 : ∀ x : Euc d, h x * (Real.cos (2 * Real.pi * inner ℝ x ξ) * cosT m h ξ +
      Real.sin (2 * Real.pi * inner ℝ x ξ) * sinT m h ξ) =
      cosT m h ξ * (h x * Real.cos (2 * Real.pi * inner ℝ x ξ)) +
      sinT m h ξ * (h x * Real.sin (2 * Real.pi * inner ℝ x ξ)) := by
    intro x; ring
  simp_rw [e4]
  obtain ⟨i1, i2⟩ := integrable_h_trig (m := m) hh hb ξ
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
  unfold cosT sinT
  ring


lemma integrable_phiHat_scaled {t : ℝ} (ht : 0 < t) :
    Integrable (fun ξ : Euc d => phiHatR d (t * ‖ξ‖)) := by
  have := (integrable_phiHat (d := d)).comp_smul (R := t) ht.ne'
  refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht]

lemma continuous_phiHat_scaled (t : ℝ) : Continuous (fun ξ : Euc d => phiHatR d (t * ‖ξ‖)) := by
  have := continuous_phiHatR (d := d)
  fun_prop

/-- `Q_t`: the quadratic form of `φ(·/t)` against `h m`. -/
lemma QT {m : Measure (Euc d)} [IsFiniteMeasure m] {h : Euc d → ℝ} (hh : Measurable h)
    (hb : ∀ x, |h x| ≤ 1) {t : ℝ} (ht : 0 < t) :
    ∫ x, h x * ∫ y, h y * phi (t⁻¹ • (x - y)) ∂m ∂m =
      ∫ ξ, (t ^ d * phiHatR d (t * ‖ξ‖)) * (cosT m h ξ ^ 2 + sinT m h ξ ^ 2) := by
  refine Q_pair hh hb ?_ ?_ (fun z => phi_scaled ht z)
  · exact (integrable_phiHat_scaled ht).const_mul _
  · have := continuous_phiHat_scaled (d := d) t
    fun_prop


/-- Tonelli on the Fourier side. -/
lemma TF {m : Measure (Euc d)} [IsFiniteMeasure m] {h : Euc d → ℝ} (hh : Measurable h)
    (hb : ∀ x, |h x| ≤ 1) {ν : Measure ℝ} [SFinite ν] (hν : ∀ᵐ t ∂ν, 0 < t) {c : ℝ → ℝ}
    (hc : Measurable c) (hc0 : ∀ᵐ t ∂ν, 0 ≤ c t)
    (hint : Integrable (fun t => c t * ∫ ξ : Euc d, (t ^ d * phiHatR d (t * ‖ξ‖)) *
      (cosT m h ξ ^ 2 + sinT m h ξ ^ 2)) ν) :
    Integrable (fun ξ : Euc d => (∫ t, c t * (t ^ d * phiHatR d (t * ‖ξ‖)) ∂ν) *
      (cosT m h ξ ^ 2 + sinT m h ξ ^ 2)) ∧
    ∫ ξ : Euc d, (∫ t, c t * (t ^ d * phiHatR d (t * ‖ξ‖)) ∂ν) * (cosT m h ξ ^ 2 + sinT m h ξ ^ 2) =
      ∫ t, c t * (∫ ξ : Euc d, (t ^ d * phiHatR d (t * ‖ξ‖)) * (cosT m h ξ ^ 2 + sinT m h ξ ^ 2)) ∂ν := by
  have hcc := continuous_cosT (m := m) hh hb
  have hss := continuous_sinT (m := m) hh hb
  have hΨ := continuous_phiHatR (d := d)
  let F : Euc d × ℝ → ℝ := fun p => c p.2 * (p.2 ^ d * phiHatR d (p.2 * ‖p.1‖)) *
      (cosT m h p.1 ^ 2 + sinT m h p.1 ^ 2)
  have hFm : Measurable F := by
    have := hcc.measurable; have := hss.measurable
    unfold F
    fun_prop
  have hbdd : ∃ M : ℝ, ∀ ξ : Euc d, ‖cosT m h ξ ^ 2 + sinT m h ξ ^ 2‖ ≤ M := by
    refine ⟨2 * (m.real Set.univ) ^ 2, fun ξ => ?_⟩
    have h1 := abs_cosT_le (m := m) hb ξ
    have h2 := abs_sinT_le (m := m) hb ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : cosT m h ξ ^ 2 ≤ (m.real Set.univ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have : sinT m h ξ ^ 2 ≤ (m.real Set.univ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    linarith
  have hslice : ∀ t : ℝ, 0 < t → Integrable (fun ξ : Euc d => F (ξ, t)) := by
    intro t ht
    obtain ⟨M, hM⟩ := hbdd
    have h1 : Integrable (fun ξ : Euc d => c t * (t ^ d * phiHatR d (t * ‖ξ‖))) :=
      ((integrable_phiHat_scaled ht).const_mul (t ^ d)).const_mul (c t)
    have h2 := h1.bdd_mul (c := M) (f := fun ξ : Euc d => cosT m h ξ ^ 2 + sinT m h ξ ^ 2)
      (by have := hcc.measurable; have := hss.measurable
          exact (by fun_prop : Measurable (fun ξ : Euc d => cosT m h ξ ^ 2 + sinT m h ξ ^ 2)).aestronglyMeasurable)
      (Filter.Eventually.of_forall hM)
    refine h2.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [F]; ring
  have hFi : Integrable F (volume.prod ν) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [hν] with t ht
      exact hslice t ht
    · refine hint.congr ?_
      filter_upwards [hν, hc0] with t ht hct
      have : ∀ ξ : Euc d, ‖F (ξ, t)‖ = c t * ((t ^ d * phiHatR d (t * ‖ξ‖)) *
          (cosT m h ξ ^ 2 + sinT m h ξ ^ 2)) := by
        intro ξ
        have := phiHatR_pos (d := d) (t * ‖ξ‖)
        have : 0 ≤ c t * (t ^ d * phiHatR d (t * ‖ξ‖)) * (cosT m h ξ ^ 2 + sinT m h ξ ^ 2) := by positivity
        simp only [F]
        rw [Real.norm_of_nonneg this]; ring
      simp_rw [this]
      rw [integral_const_mul]
  refine ⟨?_, ?_⟩
  · have := hFi.integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [F]
    rw [integral_mul_const]
  · have hswap := integral_integral_swap (μ := (volume : Measure (Euc d))) (ν := ν)
      (f := fun ξ t => F (ξ, t)) hFi
    have e1 : ∀ ξ : Euc d, ∫ t, F (ξ, t) ∂ν = (∫ t, c t * (t ^ d * phiHatR d (t * ‖ξ‖)) ∂ν) *
        (cosT m h ξ ^ 2 + sinT m h ξ ^ 2) := by
      intro ξ; simp only [F]; rw [integral_mul_const]
    have e2 : ∀ t : ℝ, ∫ ξ : Euc d, F (ξ, t) = c t * ∫ ξ, (t ^ d * phiHatR d (t * ‖ξ‖)) *
        (cosT m h ξ ^ 2 + sinT m h ξ ^ 2) := by
      intro t; rw [← integral_const_mul]; simp only [F]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only; ring
    simp_rw [e1, e2] at hswap
    exact hswap


lemma abs_phi_le_one (x : Euc d) : |phi x| ≤ 1 := by
  have := phiR_pos (d := d) ‖x‖
  show |phiR d ‖x‖| ≤ 1
  rw [abs_of_pos this]; exact phiR_le_one _

lemma integrable_pair_phi {m : Measure (Euc d)} [IsFiniteMeasure m] {h : Euc d → ℝ}
    (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1) (t : ℝ) :
    Integrable (fun p : Euc d × Euc d => h p.1 * h p.2 * phi (t⁻¹ • (p.1 - p.2))) (m.prod m) := by
  have := continuous_phi (d := d)
  refine Integrable.mono' (integrable_const (1:ℝ)) ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact (by fun_prop : Measurable (fun p : Euc d × Euc d => h p.1 * h p.2 * phi (t⁻¹ • (p.1 - p.2)))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |h p.1| * |h p.2| * |phi (t⁻¹ • (p.1 - p.2))| ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul (hb _) (hb _) (abs_nonneg _) zero_le_one) (abs_phi_le_one _)
            (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num

/-- Fubini in the scale variable on the physical side. -/
lemma MIX {m : Measure (Euc d)} [IsFiniteMeasure m] {h : Euc d → ℝ} (hh : Measurable h)
    (hb : ∀ x, |h x| ≤ 1) {ν : Measure ℝ} [SFinite ν] (hν : ∀ᵐ t ∂ν, 0 < t) {c : ℝ → ℝ}
    (hc : Measurable c) (hc0 : ∀ᵐ t ∂ν, 0 ≤ c t)
    (hint : Integrable (fun t => c t * ∫ p : Euc d × Euc d, phi (t⁻¹ • (p.1 - p.2)) ∂(m.prod m)) ν) :
    Integrable (fun t => c t * (∫ x, h x * ∫ y, h y * phi (t⁻¹ • (x - y)) ∂m ∂m)) ν ∧
    ∫ x, h x * ∫ y, h y * (∫ t, c t * phi (t⁻¹ • (x - y)) ∂ν) ∂m ∂m =
      ∫ t, c t * (∫ x, h x * ∫ y, h y * phi (t⁻¹ • (x - y)) ∂m ∂m) ∂ν := by
  have hphi := continuous_phi (d := d)
  let Gabs : (Euc d × Euc d) × ℝ → ℝ := fun q => c q.2 * phi (q.2⁻¹ • (q.1.1 - q.1.2))
  have hGabsm : Measurable Gabs := by unfold Gabs; fun_prop
  have hGabs : Integrable Gabs ((m.prod m).prod ν) := by
    rw [integrable_prod_iff' hGabsm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [hν, hc0] with t ht hct
      refine Integrable.mono' (integrable_const (c t)) ?_ (Filter.Eventually.of_forall fun p => ?_)
      · exact (by unfold Gabs; fun_prop : Measurable (fun p : Euc d × Euc d => Gabs (p, t))).aestronglyMeasurable
      · simp only [Gabs]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hct]
        exact mul_le_of_le_one_right hct (abs_phi_le_one _)
    · refine hint.congr ?_
      filter_upwards [hν, hc0] with t ht hct
      simp only [Gabs]
      have : ∀ p : Euc d × Euc d, ‖c t * phi (t⁻¹ • (p.1 - p.2))‖ = c t * phi (t⁻¹ • (p.1 - p.2)) := by
        intro p
        exact Real.norm_of_nonneg (mul_nonneg hct (phiR_pos _).le)
      simp_rw [this]
      rw [integral_const_mul]
  let G : (Euc d × Euc d) × ℝ → ℝ := fun q => h q.1.1 * h q.1.2 * Gabs q
  have hGi : Integrable G ((m.prod m).prod ν) := by
    refine hGabs.norm.mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
    · exact (by unfold G Gabs; fun_prop : Measurable G).aestronglyMeasurable
    · simp only [G]
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have := mul_le_mul (mul_le_mul (hb q.1.1) (hb q.1.2) (abs_nonneg _) zero_le_one)
        (le_refl ‖Gabs q‖) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1 * 1)
      simpa using this
  -- the iterated integrals
  have hJ : Integrable (fun p : Euc d × Euc d => ∫ t, G (p, t) ∂ν) (m.prod m) := hGi.integral_prod_left
  have e1 : ∫ x, h x * ∫ y, h y * (∫ t, c t * phi (t⁻¹ • (x - y)) ∂ν) ∂m ∂m =
      ∫ p : Euc d × Euc d, ∫ t, G (p, t) ∂ν ∂(m.prod m) := by
    rw [integral_prod _ hJ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [G, Gabs]
    rw [integral_const_mul]
    ring
  have e3 : ∀ t : ℝ, ∫ p : Euc d × Euc d, G (p, t) ∂(m.prod m) =
      c t * (∫ x, h x * ∫ y, h y * phi (t⁻¹ • (x - y)) ∂m ∂m) := by
    intro t
    have e2 : ∀ p : Euc d × Euc d, G (p, t) = c t * (h p.1 * h p.2 * phi (t⁻¹ • (p.1 - p.2))) := by
      intro p; simp only [G, Gabs]; ring
    simp_rw [e2]
    rw [integral_const_mul, integral_prod _ (integrable_pair_phi hh hb t)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only; ring
  refine ⟨?_, ?_⟩
  · exact hGi.integral_prod_right.congr (Filter.Eventually.of_forall e3)
  · rw [e1, integral_integral_swap hGi]
    exact integral_congr_ae (Filter.Eventually.of_forall e3)


/-- The quadratic form of a kernel that is a mixture of dilates of `φ`. -/
theorem QFgen {m : Measure (Euc d)} [IsFiniteMeasure m] {h : Euc d → ℝ} (hh : Measurable h)
    (hb : ∀ x, |h x| ≤ 1) {ν : Measure ℝ} [SFinite ν] (hν : ∀ᵐ t ∂ν, 0 < t) {c : ℝ → ℝ}
    (hc : Measurable c) (hc0 : ∀ᵐ t ∂ν, 0 ≤ c t)
    (hint : Integrable (fun t => c t * ∫ p : Euc d × Euc d, phi (t⁻¹ • (p.1 - p.2)) ∂(m.prod m)) ν)
    {H : Euc d → ℝ} (hH : ∀ z, H z = ∫ t, c t * phi (t⁻¹ • z) ∂ν) :
    Integrable (fun ξ : Euc d => (∫ t, c t * (t ^ d * phiHatR d (t * ‖ξ‖)) ∂ν) *
      (cosT m h ξ ^ 2 + sinT m h ξ ^ 2)) ∧
    ∫ x, h x * ∫ y, h y * H (x - y) ∂m ∂m =
      ∫ ξ : Euc d, (∫ t, c t * (t ^ d * phiHatR d (t * ‖ξ‖)) ∂ν) * (cosT m h ξ ^ 2 + sinT m h ξ ^ 2) := by
  obtain ⟨hI, hE⟩ := MIX hh hb hν hc hc0 hint
  have hQ : ∀ᵐ t ∂ν, c t * (∫ x, h x * ∫ y, h y * phi (t⁻¹ • (x - y)) ∂m ∂m) =
      c t * (∫ ξ : Euc d, (t ^ d * phiHatR d (t * ‖ξ‖)) * (cosT m h ξ ^ 2 + sinT m h ξ ^ 2)) := by
    filter_upwards [hν] with t ht
    rw [QT hh hb ht]
  have hI' := hI.congr hQ
  obtain ⟨hT1, hT2⟩ := TF hh hb hν hc hc0 hI'
  refine ⟨hT1, ?_⟩
  have : ∀ x y : Euc d, H (x - y) = ∫ t, c t * phi (t⁻¹ • (x - y)) ∂ν := fun x y => hH _
  simp_rw [this]
  rw [hE, hT2]
  exact integral_congr_ae hQ


/-- `σ = h • m` with all the properties used below. -/
structure SRepr (σ : SMeas d) (m : Measure (Euc d)) (h : Euc d → ℝ) : Prop where
  fin : IsFiniteMeasure m
  meas : Measurable h
  bd : ∀ x, |h x| ≤ 1
  pos_le : σ.pos ≤ m
  neg_le : σ.neg ≤ m
  eq_add : m = σ.pos + σ.neg
  int_eq : ∀ f : Euc d → ℝ, Integrable f m → σ.int f = ∫ x, h x * f x ∂m
  fourier_eq : ∀ ξ : Euc d, σ.fourier ξ = ∫ x, (h x : ℝ) • Complex.exp
    (-(2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ))) ∂m

theorem SMeas.exists_repr (σ : SMeas d) (hf : σ.IsFinite) : ∃ m h, SRepr σ m h := by
  obtain ⟨m, h, hm, hmeas, hb, hp, hn, hmeq, hint⟩ := σ.exists_density hf
  refine ⟨m, h, ⟨hm, hmeas, hb, hp, hn, hmeq, ?_, ?_⟩⟩
  · intro f hfi
    have := hint f hfi
    simpa [SMeas.int] using this
  · intro ξ
    haveI := hm
    have hi : Integrable (fun x : Euc d => Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)))) m := by
      refine Integrable.mono' (integrable_const (1:ℝ)) ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (by fun_prop : Continuous (fun x : Euc d => Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ))))).aestronglyMeasurable
      · rw [Complex.norm_exp]
        have : (-(2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x ξ : ℝ) : ℂ))).re = 0 := by
          simp
        rw [this]; simp
    have := hint _ hi
    simpa [SMeas.fourier] using this


theorem SRepr.norm_fourier_sq {σ : SMeas d} {m : Measure (Euc d)} {h : Euc d → ℝ} (hr : SRepr σ m h)
    (ξ : Euc d) : ‖σ.fourier ξ‖ ^ 2 = cosT m h ξ ^ 2 + sinT m h ξ ^ 2 := by
  haveI := hr.fin
  have e : ∀ x : Euc d, (h x : ℝ) • Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ))) =
      ((h x * Real.cos (2 * Real.pi * inner ℝ x ξ) : ℝ) : ℂ) -
        Complex.I * ((h x * Real.sin (2 * Real.pi * inner ℝ x ξ) : ℝ) : ℂ) := by
    intro x
    have : -(2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) =
        ((-(2 * Real.pi * inner ℝ x ξ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    simp only [Complex.real_smul]
    push_cast
    ring
  rw [hr.fourier_eq ξ]
  simp_rw [e]
  obtain ⟨i1, i2⟩ := integrable_h_trig (m := m) hr.meas hr.bd ξ
  rw [integral_sub i1.ofReal ((i2.ofReal).const_mul _), integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal]
  have : (((∫ x, h x * Real.cos (2 * Real.pi * inner ℝ x ξ) ∂m : ℝ) : ℂ) -
      Complex.I * ((∫ x, h x * Real.sin (2 * Real.pi * inner ℝ x ξ) ∂m : ℝ) : ℂ)) =
      ((cosT m h ξ : ℝ) : ℂ) - Complex.I * ((sinT m h ξ : ℝ) : ℂ) := rfl
  rw [this, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring


theorem kerEnergy_eq {σ : SMeas d} {m : Measure (Euc d)} {h : Euc d → ℝ} (hr : SRepr σ m h)
    (H : Euc d → ℝ) (hH : Measurable H) (E : ∀ᵐ x ∂m, Integrable (fun y => H (x - y)) m)
    (B : ℝ) (hB : ∀ᵐ x ∂m, ∫ y, |H (x - y)| ∂m ≤ B) :
    kerEnergy H σ = ∫ x, h x * ∫ y, h y * H (x - y) ∂m ∂m := by
  haveI := hr.fin
  have hpa : σ.pos ≪ m := Measure.absolutelyContinuous_of_le hr.pos_le
  have hna : σ.neg ≪ m := Measure.absolutelyContinuous_of_le hr.neg_le
  set I : Euc d → ℝ := fun x => ∫ y, h y * H (x - y) ∂m with hI
  have hinner : ∀ᵐ x ∂m, σ.int (fun y => H (x - y)) = I x := by
    filter_upwards [E] with x hx
    rw [hr.int_eq _ hx]
  have hImeas : AEStronglyMeasurable I m := by
    have hf : Measurable (fun p : Euc d × Euc d => h p.2 * H (p.1 - p.2)) := by
      have := hr.meas
      fun_prop
    exact (hf.stronglyMeasurable.integral_prod_right' (ν := m)).aestronglyMeasurable
  have hIint : Integrable I m := by
    refine Integrable.mono' (integrable_const B) hImeas ?_
    filter_upwards [E, hB] with x hx hBx
    have : ‖I x‖ ≤ ∫ y, |H (x - y)| ∂m := by
      calc ‖I x‖ ≤ ∫ y, ‖h y * H (x - y)‖ ∂m := norm_integral_le_integral_norm _
        _ ≤ ∫ y, |H (x - y)| ∂m := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _) hx.abs
            (Filter.Eventually.of_forall fun y => ?_)
          show ‖h y * H (x - y)‖ ≤ |H (x - y)|
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hr.bd y)
    exact this.trans hBx
  unfold kerEnergy SMeas.pair2
  have h1 : σ.int (fun x => σ.int (fun y => H (x - y))) = σ.int I := by
    unfold SMeas.int
    congr 1
    · exact integral_congr_ae (hpa.ae_le hinner)
    · exact integral_congr_ae (hna.ae_le hinner)
  rw [h1, hr.int_eq I hIint]

end HRS.Commutator.Whole
