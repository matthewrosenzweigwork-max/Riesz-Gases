import HRS.Sections.ScrnAux12

/-!
# Packet SCRN, part 13: `mesoCovMatrix` and `mesoStatCovMatrix` are positive semidefinite

(So `multivariateGaussian 0 _` of them is a genuine Gaussian and `smoothDist_gaussian_covariance` applies.)
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate

namespace HRS

variable {d : ℕ}

theorem scrn_Gab_integrable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {p : ℕ}
    (φ : Fin p → Euc d → ℝ) (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a))
    {b : ℝ} (hb : 0 < b) (t : Fin p → ℝ) (ht : ∀ a, 0 ≤ t a) (a c : Fin p) :
    Integrable (scrnGab d s b t φ a c) := by
  obtain ⟨A, hA0, hG⟩ := scrn_G_hyp hd hs0 hsd φ hφ
  obtain ⟨hm, h1, -, -⟩ := hG b hb t ht a c
  have hLint : Integrable (fun ξ : Euc d => (1 + ‖ξ‖) ^ (-((d : ℝ) + 1))) := by
    refine integrable_one_add_norm (E := Euc d) ?_
    simp
  exact Integrable.mono' (hLint.const_mul A) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => h1 ξ)

lemma scrnKab_symm (s b : ℝ) {p : ℕ} (t : Fin p → ℝ) (a c : Fin p) (ξ : Euc d) :
    scrnKab d s b t c a ξ = scrnKab d s b t a c ξ := by
  unfold scrnKab
  rw [abs_sub_comm, add_comm]

theorem scrn_mesoCov_psd (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {p : ℕ}
    (φ : Fin p → Euc d → ℝ) (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a))
    {b : ℝ} (hb : 0 < b) (t : Fin p → ℝ) (ht : ∀ a, 0 ≤ t a) :
    (mesoCovMatrix d s b t φ).PosSemidef := by
  have hc : 0 < rieszConst d s := rieszConst_pos hd hs0 hsd
  have hint := scrn_Gab_integrable hd hs0 hsd φ hφ hb t ht
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · -- symmetry
    ext a c
    simp only [Matrix.conjTranspose_apply, star_trivial]
    rw [meso_entry_eq, meso_entry_eq]
    have : ∀ ξ : Euc d, scrnGab d s b t φ c a ξ = (starRingEnd ℂ) (scrnGab d s b t φ a c ξ) := by
      intro ξ
      unfold scrnGab
      rw [scrnKab_symm]
      simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
      ring
    simp_rw [this]
    rw [integral_conj, Complex.conj_re]
  · intro x
    have hq : ∀ ξ : Euc d, 0 ≤ (∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * scrnGab d s b t φ a c ξ).re := by
      intro ξ
      set f : Fin p → ℂ := fun a => 𝓕 (scrnPhiC (φ a)) ξ with hf
      have hρ : 0 ≤ 2 * Real.pi * ‖ξ‖ := by positivity
      have hre : (∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * scrnGab d s b t φ a c ξ).re =
          (∑ a, ∑ c, (x a * (f a).re) * (x c * (f c).re) * scrnKab d s b t a c ξ) +
          (∑ a, ∑ c, (x a * (f a).im) * (x c * (f c).im) * scrnKab d s b t a c ξ) := by
        rw [Complex.re_sum]
        simp_rw [Complex.re_sum]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        unfold scrnGab
        simp only [Complex.re_ofReal_mul, Complex.mul_re, Complex.conj_re, Complex.conj_im,
          Complex.ofReal_re, Complex.ofReal_im, hf]
        ring
      rw [hre]
      have hK : ∀ y : Fin p → ℝ, 0 ≤ ∑ a, ∑ c, y a * y c * scrnKab d s b t a c ξ := fun y =>
        scrnk_psd hc hb hρ t ht y
      exact add_nonneg (hK _) (hK _)
    have hint' : ∀ a c, Integrable (fun ξ : Euc d => ((x a * x c : ℝ) : ℂ) * scrnGab d s b t φ a c ξ) :=
      fun a c => (hint a c).const_mul _
    have hI : ∫ ξ : Euc d, ∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * scrnGab d s b t φ a c ξ =
        ∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * ∫ ξ : Euc d, scrnGab d s b t φ a c ξ := by
      rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun c _ => hint' a c))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finset_sum _ (fun c _ => hint' a c)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [integral_const_mul]
    have hre : (∫ ξ : Euc d, ∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * scrnGab d s b t φ a c ξ).re =
        ∫ ξ : Euc d, (∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * scrnGab d s b t φ a c ξ).re := by
      have hI' : Integrable (fun ξ : Euc d => ∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) *
          scrnGab d s b t φ a c ξ) :=
        integrable_finset_sum _ (fun a _ => integrable_finset_sum _ (fun c _ => hint' a c))
      exact (Complex.reCLM.integral_comp_comm hI').symm
    have hnn : 0 ≤ (∫ ξ : Euc d, ∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * scrnGab d s b t φ a c ξ).re := by
      rw [hre]; exact integral_nonneg hq
    rw [hI] at hnn
    have hfin : dotProduct (star x) ((mesoCovMatrix d s b t φ).mulVec x) =
        (∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * ∫ ξ : Euc d, scrnGab d s b t φ a c ξ).re := by
      rw [Complex.re_sum]
      simp only [dotProduct, Matrix.mulVec, star_trivial, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Complex.re_ofReal_mul, ← meso_entry_eq]
      ring
    rw [hfin]; exact hnn


/-- The stationary kernel entry `S_b(ξ) e^{-|t_a-t_c| a_b(ξ)}`. -/
def scrnKstat (d : ℕ) (s b : ℝ) {p : ℕ} (t : Fin p → ℝ) (a c : Fin p) (ξ : Euc d) : ℝ :=
  scrnS (rieszConst d s) ((d : ℝ) - s) b (2 * Real.pi * ‖ξ‖) *
    Real.exp (-|t a - t c| * scrnA (rieszConst d s) ((d : ℝ) - s) b (2 * Real.pi * ‖ξ‖))

/-- The integrand of the stationary covariance entry. -/
def scrnGstat (d : ℕ) (s b : ℝ) {p : ℕ} (t : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (a c : Fin p)
    (ξ : Euc d) : ℂ :=
  𝓕 (scrnPhiC (φ a)) ξ * (starRingEnd ℂ) (𝓕 (scrnPhiC (φ c)) ξ) * ((scrnKstat d s b t a c ξ : ℝ) : ℂ)

lemma scrnKstat_symm (s b : ℝ) {p : ℕ} (t : Fin p → ℝ) (a c : Fin p) (ξ : Euc d) :
    scrnKstat d s b t c a ξ = scrnKstat d s b t a c ξ := by
  unfold scrnKstat
  rw [abs_sub_comm]

lemma meso_stat_entry_eq (s b : ℝ) {p : ℕ} (t : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (a c : Fin p) :
    mesoStatCovMatrix d s b t φ a c = (∫ ξ : Euc d, scrnGstat d s b t φ a c ξ).re := by
  unfold mesoStatCovMatrix
  simp only [Matrix.of_apply]
  by_cases h : t c ≤ t a
  · rw [if_pos h]
    congr 2
    funext ξ
    unfold scrnGstat scrnKstat scrnPhiC mesoRate mesoSpectral scrnS scrnA
    rw [abs_of_nonneg (by linarith)]
    congr 2
    push_cast
    ring_nf
  · rw [if_neg h]
    have h' : t a ≤ t c := le_of_lt (not_le.1 h)
    have : ∀ ξ : Euc d,
        𝓕 (fun x => ((φ c x : ℝ) : ℂ)) ξ * (starRingEnd ℂ) (𝓕 (fun x => ((φ a x : ℝ) : ℂ)) ξ) *
          (((Real.exp (-(t c - t a) * mesoRate d s b ξ) * mesoSpectral d s b ξ : ℝ) : ℂ)) =
        (starRingEnd ℂ) (scrnGstat d s b t φ a c ξ) := by
      intro ξ
      unfold scrnGstat scrnKstat scrnPhiC mesoRate mesoSpectral scrnS scrnA
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
      push_cast
      ring_nf
    simp_rw [this]
    rw [integral_conj, Complex.conj_re]


/-- Generic positivity: `Re ∫ F_a conj F_c K_{ac}` is PSD when `K(ξ)` is a symmetric PSD kernel. -/
theorem scrn_psd_generic {p : ℕ} (F : Fin p → Euc d → ℂ) (K : Fin p → Fin p → Euc d → ℝ)
    (hsymm : ∀ a c ξ, K c a ξ = K a c ξ)
    (hpsd : ∀ (ξ : Euc d) (y : Fin p → ℝ), 0 ≤ ∑ a, ∑ c, y a * y c * K a c ξ)
    (hint : ∀ a c, Integrable (fun ξ : Euc d => F a ξ * (starRingEnd ℂ) (F c ξ) * ((K a c ξ : ℝ) : ℂ))) :
    (Matrix.of fun a c => (∫ ξ : Euc d, F a ξ * (starRingEnd ℂ) (F c ξ) * ((K a c ξ : ℝ) : ℂ)).re).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext a c
    simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.of_apply]
    have : ∀ ξ : Euc d, F c ξ * (starRingEnd ℂ) (F a ξ) * ((K c a ξ : ℝ) : ℂ) =
        (starRingEnd ℂ) (F a ξ * (starRingEnd ℂ) (F c ξ) * ((K a c ξ : ℝ) : ℂ)) := by
      intro ξ
      rw [hsymm]
      simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
      ring
    simp_rw [this]
    rw [integral_conj, Complex.conj_re]
  · intro x
    set G : Fin p → Fin p → Euc d → ℂ := fun a c ξ =>
      F a ξ * (starRingEnd ℂ) (F c ξ) * ((K a c ξ : ℝ) : ℂ) with hG
    have hint' : ∀ a c, Integrable (fun ξ : Euc d => ((x a * x c : ℝ) : ℂ) * G a c ξ) :=
      fun a c => (hint a c).const_mul _
    have hq : ∀ ξ : Euc d, 0 ≤ (∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * G a c ξ).re := by
      intro ξ
      set f : Fin p → ℂ := fun a => F a ξ with hf
      have hre : (∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * G a c ξ).re =
          (∑ a, ∑ c, (x a * (f a).re) * (x c * (f c).re) * K a c ξ) +
          (∑ a, ∑ c, (x a * (f a).im) * (x c * (f c).im) * K a c ξ) := by
        rw [Complex.re_sum]
        simp_rw [Complex.re_sum]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [hG, Complex.mul_re, Complex.conj_re, Complex.conj_im,
          Complex.ofReal_re, Complex.ofReal_im, hf]
        ring
      rw [hre]
      exact add_nonneg (hpsd ξ _) (hpsd ξ _)
    have hI : ∫ ξ : Euc d, ∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * G a c ξ =
        ∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * ∫ ξ : Euc d, G a c ξ := by
      rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun c _ => hint' a c))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finset_sum _ (fun c _ => hint' a c)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [integral_const_mul]
    have hre : (∫ ξ : Euc d, ∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * G a c ξ).re =
        ∫ ξ : Euc d, (∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * G a c ξ).re := by
      have hI' : Integrable (fun ξ : Euc d => ∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * G a c ξ) :=
        integrable_finset_sum _ (fun a _ => integrable_finset_sum _ (fun c _ => hint' a c))
      exact (Complex.reCLM.integral_comp_comm hI').symm
    have hnn : 0 ≤ (∫ ξ : Euc d, ∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * G a c ξ).re := by
      rw [hre]; exact integral_nonneg hq
    rw [hI] at hnn
    have hfin : dotProduct (star x) ((Matrix.of fun a c => (∫ ξ : Euc d, G a c ξ).re).mulVec x) =
        (∑ a, ∑ c, ((x a * x c : ℝ) : ℂ) * ∫ ξ : Euc d, G a c ξ).re := by
      rw [Complex.re_sum]
      simp only [dotProduct, Matrix.mulVec, star_trivial, Complex.re_sum, Finset.mul_sum,
        Matrix.of_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Complex.re_ofReal_mul]
      ring
    exact hfin ▸ hnn

theorem scrn_mesoStatCov_psd (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {p : ℕ}
    (φ : Fin p → Euc d → ℝ) (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a))
    {b : ℝ} (hb : 0 < b) (t : Fin p → ℝ) (ht : ∀ a, 0 ≤ t a) :
    (mesoStatCovMatrix d s b t φ).PosSemidef := by
  have hc : 0 < rieszConst d s := rieszConst_pos hd hs0 hsd
  obtain ⟨A, hA0, hG⟩ := scrn_G_hyp hd hs0 hsd φ hφ
  have hLint : Integrable (fun ξ : Euc d => (1 + ‖ξ‖) ^ (-((d : ℝ) + 1))) := by
    refine integrable_one_add_norm (E := Euc d) ?_
    simp
  have hK0 : ∀ a c (ξ : Euc d), 0 ≤ scrnKstat d s b t a c ξ ∧ scrnKstat d s b t a c ξ ≤ 1 := by
    intro a c ξ
    have hρ : 0 ≤ 2 * Real.pi * ‖ξ‖ := by positivity
    have hS0 := scrnS_nonneg' (c := rieszConst d s) (q := (d : ℝ) - s) (b := b) hc hb hρ
    have hS1 := scrnS_lt_one' (c := rieszConst d s) (q := (d : ℝ) - s) (b := b) hc hb hρ
    have hA0 := scrnA_nonneg' (c := rieszConst d s) (q := (d : ℝ) - s) (b := b) hc hb hρ
    unfold scrnKstat
    refine ⟨mul_nonneg hS0 (Real.exp_pos _).le, ?_⟩
    have : Real.exp (-|t a - t c| * scrnA (rieszConst d s) ((d : ℝ) - s) b (2 * Real.pi * ‖ξ‖)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [abs_nonneg (t a - t c)])
    nlinarith
  have hint : ∀ a c, Integrable (scrnGstat d s b t φ a c) := by
    intro a c
    obtain ⟨hm, -, hPb, -⟩ := hG b hb t ht a c
    have hFm : ∀ a, Continuous (𝓕 (scrnPhiC (φ a))) := fun a =>
      (scrn_fourier_diff (hφ a).1 (hφ a).2).continuous
    have hmeas : Measurable (scrnGstat d s b t φ a c) := by
      unfold scrnGstat scrnKstat
      refine ((hFm a).measurable.mul (Complex.continuous_conj.measurable.comp (hFm c).measurable)).mul ?_
      refine Complex.measurable_ofReal.comp (Measurable.mul ?_ ?_)
      · unfold scrnS; fun_prop
      · unfold scrnA; fun_prop
    refine Integrable.mono' (hLint.const_mul A) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    unfold scrnGstat
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 a c ξ).1]
    calc _ ≤ ‖𝓕 (scrnPhiC (φ a)) ξ * (starRingEnd ℂ) (𝓕 (scrnPhiC (φ c)) ξ)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hK0 a c ξ).2 (norm_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact hPb ξ
  have hmat : mesoStatCovMatrix d s b t φ =
      Matrix.of fun a c => (∫ ξ : Euc d, scrnGstat d s b t φ a c ξ).re := by
    ext a c
    rw [meso_stat_entry_eq]; rfl
  rw [hmat]
  refine scrn_psd_generic (fun a => 𝓕 (scrnPhiC (φ a))) (scrnKstat d s b t)
    (fun a c ξ => scrnKstat_symm s b t a c ξ) (fun ξ y => ?_) hint
  exact scrnkStat_psd hc hb (by positivity) t ht y

end HRS
