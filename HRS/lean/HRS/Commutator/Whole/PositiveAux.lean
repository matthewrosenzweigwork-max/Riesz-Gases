import HRS.Commutator.Whole.Defs

/-!
# Helpers for `Positive.lean` (packet `CMX-POS`), part A

Elementary bounds for `φ`, the Gaussian mixture representation, the radial profile `phiHatR` of
`φ̂`, and its properties (positive, continuous, antitone, integrable).
-/
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff
namespace HRS.Commutator.Whole
open HRS HRS.Whole
variable {d : ℕ} {s : ℝ}

lemma phiR_pos (r : ℝ) : 0 < phiR d r := by
  unfold phiR; positivity

lemma phi_eq (x : Euc d) : phi x = phiR d ‖x‖ := rfl

lemma phiR_le_one (r : ℝ) : phiR d r ≤ 1 := by
  unfold phiR
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · nlinarith [sq_nonneg r]
  · have : (0:ℝ) ≤ d := Nat.cast_nonneg d
    linarith

lemma phiR_le_pow {r : ℝ} (hr : 0 < r) : phiR d r ≤ r ^ (-(2 * (d:ℝ) + 4)) := by
  unfold phiR
  have h1 : (r ^ 2) ^ (-((d:ℝ) + 2)) = r ^ (-(2 * (d:ℝ) + 4)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
  rw [← h1]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith)
  have : (0:ℝ) ≤ d := Nat.cast_nonneg d
  linarith

lemma phiR_ge_pow {r : ℝ} (hr : 1 ≤ r) : (2:ℝ) ^ (-((d:ℝ) + 2)) * r ^ (-(2 * (d:ℝ) + 4)) ≤ phiR d r := by
  have hr0 : 0 < r := by linarith
  unfold phiR
  have h1 : (2 * r ^ 2) ^ (-((d:ℝ) + 2)) = (2:ℝ) ^ (-((d:ℝ) + 2)) * r ^ (-(2 * (d:ℝ) + 4)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]; congr 1; push_cast; ring
  rw [← h1]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith)
  have : (0:ℝ) ≤ d := Nat.cast_nonneg d
  linarith

lemma phiR_ge_near {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1) : (2:ℝ) ^ (-((d:ℝ) + 2)) ≤ phiR d r := by
  unfold phiR
  apply Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith)
  have : (0:ℝ) ≤ d := Nat.cast_nonneg d
  linarith

lemma phiR_antitoneOn : AntitoneOn (phiR d) (Set.Ici 0) := by
  intro a ha b hb hab
  unfold phiR
  apply Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [Set.mem_Ici.1 ha])
  have : (0:ℝ) ≤ d := Nat.cast_nonneg d
  linarith

lemma continuous_phiR : Continuous (phiR d) := by
  unfold phiR
  apply Continuous.rpow_const (by fun_prop)
  intro x; left; positivity

lemma continuous_phi : Continuous (phi : Euc d → ℝ) := continuous_phiR.comp continuous_norm

lemma integrable_phi : Integrable (phi : Euc d → ℝ) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := Euc d) (μ := volume) (r := 2 * (d:ℝ) + 4)
    (by simp; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [phi]; congr 1; ring

theorem phi_mixture_aux (x : Euc d) :
    phi x = (Real.Gamma ((d : ℝ) + 2))⁻¹ *
      ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) + 1) * Real.exp (-t) * Real.exp (-t * ‖x‖ ^ 2) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (d:ℝ) + 2) (r := 1 + ‖x‖^2) (by positivity) (by positivity)
  have e : ∀ t : ℝ, t ^ ((d : ℝ) + 1) * Real.exp (-t) * Real.exp (-t * ‖x‖ ^ 2)
      = t ^ ((d:ℝ) + 2 - 1) * Real.exp (-((1 + ‖x‖^2) * t)) := by
    intro t
    rw [mul_assoc, ← Real.exp_add]; congr 2 <;> ring_nf
  simp_rw [e]
  rw [h]
  have hG : 0 < Real.Gamma ((d:ℝ)+2) := Real.Gamma_pos_of_pos (by positivity)
  rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  simp only [phi]
  field_simp

lemma integrableOn_rpow_exp {a b : ℝ} (ha : -1 < a) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ a * Real.exp (-(b * u))) (Set.Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a) (b := b) ha one_pos hb
  refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp [neg_mul]

/-- weight of the Gaussian mixture. -/
def gmix (d : ℕ) (x : Euc d) (u : ℝ) : ℝ :=
  (Real.Gamma ((d : ℝ) + 2))⁻¹ * (u ^ ((d : ℝ) + 1) * Real.exp (-u) * Real.exp (-u * ‖x‖ ^ 2))

lemma gmix_nonneg (x : Euc d) {u : ℝ} (hu : 0 < u) : 0 ≤ gmix d x u := by
  unfold gmix
  have : 0 < Real.Gamma ((d : ℝ) + 2) := Real.Gamma_pos_of_pos (by positivity)
  positivity

lemma integral_gmix (x : Euc d) : ∫ u in Set.Ioi (0:ℝ), gmix d x u = phi x := by
  unfold gmix
  rw [integral_const_mul, ← phi_mixture_aux]

lemma integrableOn_gmix (x : Euc d) : IntegrableOn (gmix d x) (Set.Ioi 0) := by
  have h := integrableOn_rpow_exp (a := (d:ℝ)+1) (b := 1 + ‖x‖^2)
    (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]) (by positivity)
  have h2 : IntegrableOn (fun u : ℝ => (Real.Gamma ((d : ℝ) + 2))⁻¹ *
      (u ^ ((d:ℝ)+1) * Real.exp (-((1 + ‖x‖^2) * u)))) (Set.Ioi 0) := h.const_mul _
  refine h2.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [gmix]
  congr 1
  rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma measurable_gmix : Measurable (fun p : Euc d × ℝ => gmix d p.1 p.2) := by
  unfold gmix
  fun_prop


/-- Fourier side of the Gaussian mixture. -/
def gmixHat (d : ℕ) (r u : ℝ) : ℝ :=
  (Real.Gamma ((d : ℝ) + 2))⁻¹ * (u ^ ((d : ℝ) + 1) * Real.exp (-u)) *
    ((Real.pi / u) ^ ((d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * r ^ 2 / u))

/-- Radial profile of `φ̂`. -/
def phiHatR (d : ℕ) (r : ℝ) : ℝ := ∫ u in Set.Ioi (0 : ℝ), gmixHat d r u

lemma fourier_gauss {u : ℝ} (hu : 0 < u) (ξ : Euc d) :
    𝓕 (fun x : Euc d => ((Real.exp (-u * ‖x‖ ^ 2) : ℝ) : ℂ)) ξ =
      (((Real.pi / u) ^ ((d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / u) : ℝ) : ℂ) := by
  have hb : (0:ℝ) < (u:ℂ).re := by simpa using hu
  have := fourier_gaussian_innerProductSpace (V := Euc d) hb ξ
  have e : (fun x : Euc d => ((Real.exp (-u * ‖x‖ ^ 2) : ℝ) : ℂ)) =
      fun v : Euc d => Complex.exp (-(u:ℂ) * ‖v‖ ^ 2) := by
    ext v; push_cast; rfl
  rw [e, this]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  push_cast
  rw [Complex.ofReal_cpow (by positivity)]
  push_cast
  congr 1

lemma norm_fourierKernel (ξ x : Euc d) :
    ‖Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ) * Complex.I))‖ = 1 := by
  rw [Complex.norm_exp_ofReal_mul_I]

lemma fourier_phi (ξ : Euc d) :
    𝓕 (fun x : Euc d => ((phi x : ℝ) : ℂ)) ξ = ((phiHatR d ‖ξ‖ : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  have h1 : ∀ x : Euc d, Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ) * Complex.I)) • ((phi x : ℝ) : ℂ)
      = ∫ u in Set.Ioi (0:ℝ), Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ) * Complex.I)) *
          ((gmix d x u : ℝ) : ℂ) := by
    intro x
    rw [integral_const_mul, integral_complex_ofReal, integral_gmix, smul_eq_mul]
  simp_rw [h1]
  have hint : Integrable (fun p : Euc d × ℝ => Complex.exp ((↑(-2 * Real.pi * inner ℝ p.1 ξ) * Complex.I)) *
          ((gmix d p.1 p.2 : ℝ) : ℂ)) (volume.prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    have hm : Measurable (fun p : Euc d × ℝ => Complex.exp ((↑(-2 * Real.pi * inner ℝ p.1 ξ) * Complex.I)) *
          ((gmix d p.1 p.2 : ℝ) : ℂ)) := by
      have := (measurable_gmix (d := d))
      fun_prop
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    have hn : ∀ x : Euc d, ∀ u ∈ Set.Ioi (0:ℝ),
        ‖Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ) * Complex.I)) * ((gmix d x u : ℝ) : ℂ)‖
          = gmix d x u := by
      intro x u hu
      rw [norm_mul, norm_fourierKernel, one_mul, Complex.norm_real, Real.norm_of_nonneg (gmix_nonneg x hu)]
    refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
    · have hg : Integrable (gmix d x) (volume.restrict (Set.Ioi (0:ℝ))) := integrableOn_gmix x
      dsimp only
      exact (hg.ofReal (𝕜 := ℂ)).const_mul _
    · have hg : Integrable (fun x : Euc d => phi x) := integrable_phi
      refine hg.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [setIntegral_congr_fun measurableSet_Ioi (hn x), integral_gmix]
  rw [integral_integral_swap hint]
  have h2 : ∀ u ∈ Set.Ioi (0:ℝ), ∫ x : Euc d, Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ) * Complex.I)) *
      ((gmix d x u : ℝ) : ℂ) = ((gmixHat d ‖ξ‖ u : ℝ) : ℂ) := by
    intro u hu
    have hu : 0 < u := hu
    have := fourier_gauss (d := d) hu ξ
    rw [Real.fourier_eq'] at this
    have e1 : ∀ x : Euc d, Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ) * Complex.I)) *
        ((gmix d x u : ℝ) : ℂ) = (((Real.Gamma ((d : ℝ) + 2))⁻¹ * (u ^ ((d : ℝ) + 1) * Real.exp (-u)) : ℝ) : ℂ) *
          (Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ) * Complex.I)) • ((Real.exp (-u * ‖x‖ ^ 2) : ℝ) : ℂ)) := by
      intro x
      simp only [gmix, smul_eq_mul]
      push_cast
      ring
    simp_rw [e1]
    rw [integral_const_mul, this]
    simp only [gmixHat]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h2, integral_complex_ofReal]
  rfl


lemma gmixHat_nonneg (r : ℝ) {u : ℝ} (hu : 0 < u) : 0 ≤ gmixHat d r u := by
  unfold gmixHat
  have : 0 < Real.Gamma ((d : ℝ) + 2) := Real.Gamma_pos_of_pos (by positivity)
  positivity

lemma gmixHat_pos (r : ℝ) {u : ℝ} (hu : 0 < u) : 0 < gmixHat d r u := by
  unfold gmixHat
  have : 0 < Real.Gamma ((d : ℝ) + 2) := Real.Gamma_pos_of_pos (by positivity)
  positivity

lemma measurable_gmixHat : Measurable (fun p : ℝ × ℝ => gmixHat d p.1 p.2) := by
  unfold gmixHat
  fun_prop

lemma measurable_gmixHat_u (r : ℝ) : Measurable (gmixHat d r) := by
  unfold gmixHat
  fun_prop
lemma gmixHat_le (r : ℝ) {u : ℝ} (hu : 0 < u) :
    gmixHat d r u ≤ (Real.Gamma ((d : ℝ) + 2))⁻¹ * Real.pi ^ ((d : ℝ) / 2) *
      (u ^ ((d : ℝ) / 2 + 1) * Real.exp (-(1 * u))) := by
  unfold gmixHat
  have hG : 0 < Real.Gamma ((d : ℝ) + 2) := Real.Gamma_pos_of_pos (by positivity)
  have h1 : Real.exp (-Real.pi ^ 2 * r ^ 2 / u) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ Real.pi ^ 2 * r ^ 2 / u := by positivity
    have e : -Real.pi ^ 2 * r ^ 2 / u = -(Real.pi ^ 2 * r ^ 2 / u) := by ring
    linarith
  have h2 : u ^ ((d : ℝ) + 1) * (Real.pi / u) ^ ((d : ℝ) / 2) =
      Real.pi ^ ((d : ℝ) / 2) * u ^ ((d : ℝ) / 2 + 1) := by
    rw [Real.div_rpow Real.pi_pos.le hu.le]
    have : u ^ ((d : ℝ) + 1) = u ^ ((d:ℝ)/2 + 1) * u ^ ((d:ℝ)/2) := by
      rw [← Real.rpow_add hu]; congr 1; ring
    rw [this]; field_simp
  calc (Real.Gamma ((d : ℝ) + 2))⁻¹ * (u ^ ((d : ℝ) + 1) * Real.exp (-u)) *
        ((Real.pi / u) ^ ((d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * r ^ 2 / u))
      ≤ (Real.Gamma ((d : ℝ) + 2))⁻¹ * (u ^ ((d : ℝ) + 1) * Real.exp (-u)) *
        ((Real.pi / u) ^ ((d : ℝ) / 2) * 1) := by
        gcongr
    _ = _ := by
        have : (Real.Gamma ((d : ℝ) + 2))⁻¹ * (u ^ ((d : ℝ) + 1) * Real.exp (-u)) *
          ((Real.pi / u) ^ ((d : ℝ) / 2) * 1) = (Real.Gamma ((d : ℝ) + 2))⁻¹ *
          (u ^ ((d : ℝ) + 1) * (Real.pi / u) ^ ((d : ℝ) / 2)) * Real.exp (-u) := by ring
        rw [this, h2]; simp; ring

lemma integrableOn_gmixHat (r : ℝ) : IntegrableOn (gmixHat d r) (Set.Ioi 0) := by
  have h := integrableOn_rpow_exp (a := (d:ℝ)/2 + 1) (b := 1)
    (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]) one_pos
  have h2 := h.const_mul ((Real.Gamma ((d : ℝ) + 2))⁻¹ * Real.pi ^ ((d : ℝ) / 2))
  refine Integrable.mono' h2 ?_ ?_
  · exact (measurable_gmixHat_u r).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (gmixHat_nonneg r hu)]
    exact gmixHat_le r hu

lemma phiHatR_pos (r : ℝ) : 0 < phiHatR d r := by
  unfold phiHatR
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : Function.support (gmixHat d r) ∩ Set.Ioi 0 = Set.Ioi 0 := by
      ext u; constructor
      · exact fun h => h.2
      · intro hu; exact ⟨(gmixHat_pos r hu).ne', hu⟩
    rw [this]; simp
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact gmixHat_nonneg r hu
  · exact integrableOn_gmixHat r


lemma integrable_gauss {b : ℝ} (hb : 0 < b) : Integrable (fun v : Euc d => Real.exp (-b * ‖v‖ ^ 2)) := by
  have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc d)
    (b := (b:ℂ)) (by simpa using hb) 0 0
  have h2 := this.norm
  refine h2.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [zero_mul, add_zero]
  rw [Complex.norm_exp]
  have : (-(b:ℂ) * (‖v‖:ℂ) ^ 2).re = -b * ‖v‖ ^ 2 := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [this]

lemma integral_gauss {b : ℝ} (hb : 0 < b) :
    ∫ v : Euc d, Real.exp (-b * ‖v‖ ^ 2) = (Real.pi / b) ^ ((d : ℝ) / 2) := by
  have := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Euc d) hb
  simpa using this

lemma continuous_phiHatR : Continuous (phiHatR d) := by
  unfold phiHatR
  have h := integrableOn_rpow_exp (a := (d:ℝ)/2 + 1) (b := 1)
    (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]) one_pos
  have h2 : Integrable (fun u : ℝ => (Real.Gamma ((d : ℝ) + 2))⁻¹ * Real.pi ^ ((d : ℝ) / 2) *
      (u ^ ((d : ℝ) / 2 + 1) * Real.exp (-(1 * u)))) (volume.restrict (Set.Ioi 0)) := h.const_mul _
  refine continuous_of_dominated (bound := fun u : ℝ => (Real.Gamma ((d : ℝ) + 2))⁻¹ * Real.pi ^ ((d : ℝ) / 2) *
      (u ^ ((d : ℝ) / 2 + 1) * Real.exp (-(1 * u)))) ?_ ?_ h2 ?_
  · intro r
    exact (measurable_gmixHat_u r).aestronglyMeasurable
  · intro r
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (gmixHat_nonneg r hu)]
    exact gmixHat_le r hu
  · filter_upwards with u
    unfold gmixHat
    fun_prop

lemma phiHatR_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : phiHatR d b ≤ phiHatR d a := by
  unfold phiHatR
  refine setIntegral_mono_on (integrableOn_gmixHat b) (integrableOn_gmixHat a) measurableSet_Ioi ?_
  intro u hu
  have hu : 0 < u := hu
  unfold gmixHat
  have hG : 0 < Real.Gamma ((d : ℝ) + 2) := Real.Gamma_pos_of_pos (by positivity)
  have : a ^ 2 ≤ b ^ 2 := by nlinarith
  have h3 : Real.pi ^ 2 * a ^ 2 / u ≤ Real.pi ^ 2 * b ^ 2 / u := by gcongr
  have e1 : -Real.pi ^ 2 * a ^ 2 / u = -(Real.pi ^ 2 * a ^ 2 / u) := by ring
  have e2 : -Real.pi ^ 2 * b ^ 2 / u = -(Real.pi ^ 2 * b ^ 2 / u) := by ring
  have key : Real.exp (-Real.pi ^ 2 * b ^ 2 / u) ≤ Real.exp (-Real.pi ^ 2 * a ^ 2 / u) := by
    rw [Real.exp_le_exp, e1, e2]; linarith
  have hw : 0 ≤ (Real.Gamma ((d : ℝ) + 2))⁻¹ * (u ^ ((d : ℝ) + 1) * Real.exp (-u)) := by positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left key (by positivity)) hw

lemma integrable_phiHat : Integrable (fun η : Euc d => phiHatR d ‖η‖) := by
  let F : Euc d × ℝ → ℝ := fun p => gmixHat d ‖p.1‖ p.2
  have hm : Measurable F := by
    unfold F gmixHat
    fun_prop
  have hI : Integrable F (volume.prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff' hm.aestronglyMeasurable]
    have hn : ∀ u ∈ Set.Ioi (0:ℝ), ∫ η : Euc d, ‖F (η, u)‖ =
        (Real.Gamma ((d : ℝ) + 2))⁻¹ * (u ^ ((d : ℝ) + 1) * Real.exp (-u)) := by
      intro u hu
      have hu : 0 < u := hu
      have e1 : ∀ η : Euc d, ‖F (η, u)‖ = (Real.Gamma ((d : ℝ) + 2))⁻¹ * (u ^ ((d : ℝ) + 1) * Real.exp (-u)) *
          (Real.pi / u) ^ ((d : ℝ) / 2) * Real.exp (-(Real.pi ^ 2 / u) * ‖η‖ ^ 2) := by
        intro η
        simp only [F]
        rw [Real.norm_of_nonneg (gmixHat_nonneg _ hu)]
        unfold gmixHat
        have : -Real.pi ^ 2 * ‖η‖ ^ 2 / u = -(Real.pi ^ 2 / u) * ‖η‖ ^ 2 := by ring
        rw [this]; ring
      simp_rw [e1]
      rw [integral_const_mul, integral_gauss (by positivity)]
      have : Real.pi / (Real.pi ^ 2 / u) = (Real.pi / u)⁻¹ := by
        field_simp
      rw [this, Real.inv_rpow (by positivity)]
      have : (Real.pi / u) ^ ((d : ℝ) / 2) * ((Real.pi / u) ^ ((d : ℝ) / 2))⁻¹ = 1 := by
        rw [mul_inv_cancel₀]; positivity
      rw [mul_assoc, this, mul_one]
    refine ⟨?_, ?_⟩
    · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with u hu
      have hu : 0 < u := hu
      have e1 : ∀ η : Euc d, F (η, u) = (Real.Gamma ((d : ℝ) + 2))⁻¹ * (u ^ ((d : ℝ) + 1) * Real.exp (-u)) *
          (Real.pi / u) ^ ((d : ℝ) / 2) * Real.exp (-(Real.pi ^ 2 / u) * ‖η‖ ^ 2) := by
        intro η
        simp only [F]
        unfold gmixHat
        have : -Real.pi ^ 2 * ‖η‖ ^ 2 / u = -(Real.pi ^ 2 / u) * ‖η‖ ^ 2 := by ring
        rw [this]; ring
      simp_rw [e1]
      exact (integrable_gauss (by positivity)).const_mul _
    · have h1 := integrableOn_rpow_exp (a := (d:ℝ)+1) (b := 1)
        (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]) one_pos
      have h2 : Integrable (fun u : ℝ => (Real.Gamma ((d : ℝ) + 2))⁻¹ *
          (u ^ ((d : ℝ) + 1) * Real.exp (-(1 * u)))) (volume.restrict (Set.Ioi 0)) := h1.const_mul _
      refine h2.congr ?_
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with u hu
      rw [hn u hu]; simp
  have := hI.integral_prod_left
  exact this

end HRS.Commutator.Whole
