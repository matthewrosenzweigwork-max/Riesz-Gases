import HRS.Sections.IIDAux11

/-!
# IID helper chain, part 12: `L²`-vectors realising the mode covariances, and the Gaussian coupling
`N(0, Σ_q^T)` vs `N(0, Σ_ρ^T)` for nearby densities.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.IID

section SigT

open HRS.InitialDataAux

variable {d : ℕ}

lemma SigT_apply {m : ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (T : Finset (NonzeroLattice d)) {N : ℕ} (hN : 1 ≤ N) (a b : Fin T.card) :
    (∑ _i : Fin N, Yurinskii.momentMatrix (μ.map (xiVec μ N (blk m T)))) a b =
      iidCov μ (blk m T a) (blk m T b) := by
  have hfc : ∀ a, Continuous (blk m T a) := fun a => continuous_scMode m _
  have hξc := continuous_xiVec μ N (blk m T) hfc
  have hξm : Measurable (xiVec μ N (blk m T)) := hξc.measurable
  simp only [Matrix.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : Yurinskii.momentMatrix (μ.map (xiVec μ N (blk m T))) a b =
      ∫ x, xiVec μ N (blk m T) x a * xiVec μ N (blk m T) x b ∂μ := by
    simp only [Yurinskii.momentMatrix, Matrix.of_apply]
    rw [integral_map hξm.aemeasurable (by fun_prop)]
  rw [h1, integral_xiVec_mul hN (blk m T) hfc a b]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  field_simp

end SigT


section L2

open HRS.InitialDataAux

variable {d : ℕ}

lemma integrable_of_pd {q : Torus d → ℝ} (hq : IsProbDensity q) : Integrable q := by
  by_contra h
  have := hq.integral_one
  rw [integral_undef h] at this
  norm_num at this

lemma integrable_mul_bdd {q f : Torus d → ℝ} (hq : Integrable q) (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : Integrable (fun x => q x * f x) := by
  refine Integrable.mono' (hq.norm.mul_const C) (hq.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

lemma memLp_mul_sqrt {q : Torus d → ℝ} (hq : IsProbDensity q) {f : Torus d → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    MemLp (fun x => f x * Real.sqrt (q x)) 2 (volume : Measure (Torus d)) := by
  have hm : Measurable fun x => f x * Real.sqrt (q x) := hf.mul (hq.measurable.sqrt)
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have : Integrable (fun x => q x * (f x) ^ 2) := by
    refine integrable_mul_bdd (integrable_of_pd hq) (hf.pow_const 2) (C := C ^ 2) fun x => ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (by linarith [abs_le.1 (hC x)]) (abs_le.1 (hC x)).2
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [mul_pow, Real.sq_sqrt (hq.nonneg x)]; ring

lemma inner_toLp {f g : Torus d → ℝ} (hf : MemLp f 2 (volume : Measure (Torus d)))
    (hg : MemLp g 2 (volume : Measure (Torus d))) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]; simp [mul_comm]

lemma norm_sq_toLp_sub {f g : Torus d → ℝ} (hf : MemLp f 2 (volume : Measure (Torus d)))
    (hg : MemLp g 2 (volume : Measure (Torus d))) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, (f x - g x) ^ 2 := by
  have e : hf.toLp f - hg.toLp g = (hf.sub hg).toLp (f - g) := (MemLp.toLp_sub hf hg).symm
  rw [e, ← real_inner_self_eq_norm_sq, inner_toLp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]


lemma sqrt_sub_sq_le {q r κ : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) (hκ : 0 ≤ κ) (h : |q - r| ≤ κ * r) :
    (Real.sqrt q - Real.sqrt r) ^ 2 ≤ κ ^ 2 * r := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    have : q ≤ 0 := by
      have := (le_abs_self (q - 0)).trans h
      simp at this; exact this
    have : q = 0 := le_antisymm this hq
    simp [this]
  · set a := Real.sqrt q
    set b := Real.sqrt r
    have ha : a ^ 2 = q := Real.sq_sqrt hq
    have hb : b ^ 2 = r := Real.sq_sqrt hr
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hb0 : 0 < b := Real.sqrt_pos.2 hpos
    have h1 : (a - b) ^ 2 * (a + b) ^ 2 = (q - r) ^ 2 := by rw [← ha, ← hb]; ring
    have h2 : (q - r) ^ 2 ≤ (κ * r) ^ 2 := by
      have := sq_le_sq' (by linarith [abs_le.1 h]) (abs_le.1 h).2
      simpa using this
    have h3 : r ≤ (a + b) ^ 2 := by nlinarith
    have h4 : (a - b) ^ 2 * r ≤ κ ^ 2 * r * r := by
      calc (a - b) ^ 2 * r ≤ (a - b) ^ 2 * (a + b) ^ 2 := by gcongr
        _ ≤ _ := by rw [h1]; nlinarith
    exact le_of_mul_le_mul_right (by nlinarith) hpos

/-- the vector `ψ_r f = (f - r(f)) √r`. -/
def psiv (r f : Torus d → ℝ) (x : Torus d) : ℝ := (f x - ∫ y, r y * f y) * Real.sqrt (r x)


lemma cov_eq_integral {r : Torus d → ℝ} (hr : IsProbDensity r) {f g : Torus d → ℝ}
    (hf : Measurable f) (hg : Measurable g) {C : ℝ} (hCf : ∀ x, |f x| ≤ C) (hCg : ∀ x, |g x| ≤ C) :
    iidCov (withDensityReal r) f g = ∫ x, psiv r f x * psiv r g x := by
  have hri := integrable_of_pd hr
  have i1 : Integrable (fun x => r x * f x) := integrable_mul_bdd hri hf hCf
  have i2 : Integrable (fun x => r x * g x) := integrable_mul_bdd hri hg hCg
  have i3 : Integrable (fun x => r x * (f x * g x)) :=
    integrable_mul_bdd hri (hf.mul hg) (C := C * C) fun x => by
      rw [abs_mul]; exact mul_le_mul (hCf x) (hCg x) (abs_nonneg _) ((abs_nonneg _).trans (hCf x))
  unfold iidCov pair
  rw [integral_withDensityReal_eq r hr.measurable hr.nonneg, integral_withDensityReal_eq r hr.measurable hr.nonneg,
    integral_withDensityReal_eq r hr.measurable hr.nonneg]
  set cf := ∫ y, r y * f y
  set cg := ∫ y, r y * g y
  have e : ∀ x, psiv r f x * psiv r g x =
      r x * (f x * g x) - cg * (r x * f x) - cf * (r x * g x) + cf * cg * r x := by
    intro x
    unfold psiv
    have : Real.sqrt (r x) * Real.sqrt (r x) = r x := Real.mul_self_sqrt (hr.nonneg x)
    calc _ = (f x - cf) * (g x - cg) * (Real.sqrt (r x) * Real.sqrt (r x)) := by ring
      _ = _ := by rw [this]; ring
  simp_rw [e]
  have j1 : Integrable (fun x => r x * (f x * g x) - cg * (r x * f x)) := i3.sub (i1.const_mul cg)
  have j2 : Integrable (fun x => r x * (f x * g x) - cg * (r x * f x) - cf * (r x * g x)) :=
    j1.sub (i2.const_mul cf)
  have j3 : Integrable (fun x => cf * cg * r x) := hri.const_mul _
  rw [integral_add j2 j3, integral_sub j1 (i2.const_mul cf), integral_sub i3 (i1.const_mul cg),
    integral_const_mul, integral_const_mul, integral_const_mul, hr.integral_one]
  ring

lemma psi_close {q ρ : Torus d → ℝ} (hq : IsProbDensity q) (hρ : IsProbDensity ρ) {κ : ℝ}
    (hκ : 0 ≤ κ) (hqρ : ∀ x, |q x - ρ x| ≤ κ * ρ x) {f : Torus d → ℝ} (hf : Measurable f)
    {s : ℝ} (hs : ∀ x, |f x| ≤ s) :
    ∫ x, (psiv q f x - psiv ρ f x) ^ 2 ≤ 10 * s ^ 2 * κ ^ 2 := by
  have hs0 : 0 ≤ s := (abs_nonneg _).trans (hs 0)
  have hqi := integrable_of_pd hq
  have hρi := integrable_of_pd hρ
  have i1 : Integrable (fun x => q x * f x) := integrable_mul_bdd hqi hf hs
  have i2 : Integrable (fun x => ρ x * f x) := integrable_mul_bdd hρi hf hs
  set cq := ∫ y, q y * f y with hcq
  set cρ := ∫ y, ρ y * f y with hcρ
  have hcq_le : |cq| ≤ s := by
    have := norm_integral_le_of_norm_le (hqi.const_mul s) (f := fun x => q x * f x)
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hq.nonneg x)]
        nlinarith [hs x, hq.nonneg x])
    rw [integral_const_mul, hq.integral_one] at this
    simpa using this
  have hcρ_le : |cρ| ≤ s := by
    have := norm_integral_le_of_norm_le (hρi.const_mul s) (f := fun x => ρ x * f x)
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg x)]
        nlinarith [hs x, hρ.nonneg x])
    rw [integral_const_mul, hρ.integral_one] at this
    simpa using this
  have hdiff : |cρ - cq| ≤ κ * s := by
    have e : cρ - cq = ∫ x, (ρ x * f x - q x * f x) := (integral_sub i2 i1).symm
    rw [e]
    have := norm_integral_le_of_norm_le (hρi.const_mul (κ * s)) (f := fun x => ρ x * f x - q x * f x)
      (Filter.Eventually.of_forall fun x => by
        rw [← sub_mul, Real.norm_eq_abs, abs_mul]
        have h1 := hqρ x
        rw [abs_sub_comm] at h1
        calc |ρ x - q x| * |f x| ≤ (κ * ρ x) * s :=
              mul_le_mul h1 (hs x) (abs_nonneg _) (mul_nonneg hκ (hρ.nonneg x))
          _ = κ * s * ρ x := by ring)
    rw [integral_const_mul, hρ.integral_one] at this
    simpa using this
  have hpt : ∀ x, (psiv q f x - psiv ρ f x) ^ 2 ≤ (10 * s ^ 2 * κ ^ 2) * ρ x := by
    intro x
    have hsq := sqrt_sub_sq_le (hq.nonneg x) (hρ.nonneg x) hκ (hqρ x)
    have hb : Real.sqrt (ρ x) ^ 2 = ρ x := Real.sq_sqrt (hρ.nonneg x)
    unfold psiv
    set a := Real.sqrt (q x)
    set b := Real.sqrt (ρ x)
    have e : (f x - cq) * a - (f x - cρ) * b = (f x - cq) * (a - b) + (cρ - cq) * b := by ring
    rw [e]
    have h1 : (f x - cq) ^ 2 ≤ (2 * s) ^ 2 := by
      apply sq_le_sq'
      · linarith [abs_le.1 (hs x), abs_le.1 hcq_le]
      · linarith [abs_le.1 (hs x), abs_le.1 hcq_le]
    have h2 : (cρ - cq) ^ 2 ≤ (κ * s) ^ 2 := by
      apply sq_le_sq'
      · linarith [abs_le.1 hdiff]
      · linarith [abs_le.1 hdiff]
    have h3 : ((f x - cq) * (a - b)) ^ 2 ≤ (2 * s) ^ 2 * (κ ^ 2 * ρ x) := by
      rw [mul_pow]; exact mul_le_mul h1 hsq (sq_nonneg _) (sq_nonneg _)
    have h4 : ((cρ - cq) * b) ^ 2 ≤ (κ * s) ^ 2 * ρ x := by
      rw [mul_pow, hb]; exact mul_le_mul_of_nonneg_right h2 (hρ.nonneg x)
    nlinarith [sq_nonneg ((f x - cq) * (a - b) - (cρ - cq) * b)]
  calc ∫ x, (psiv q f x - psiv ρ f x) ^ 2 ≤ ∫ x, (10 * s ^ 2 * κ ^ 2) * ρ x :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
          (hρi.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = 10 * s ^ 2 * κ ^ 2 := by rw [integral_const_mul, hρ.integral_one, mul_one]


lemma memLp_psiv {r : Torus d → ℝ} (hr : IsProbDensity r) {f : Torus d → ℝ} (hf : Measurable f)
    {s : ℝ} (hs : ∀ x, |f x| ≤ s) :
    MemLp (psiv r f) 2 (volume : Measure (Torus d)) := by
  have := memLp_mul_sqrt hr (hf.sub_const (∫ y, r y * f y)) (C := s + |∫ y, r y * f y|) fun x => by
    refine (abs_sub _ _).trans ?_
    linarith [hs x]
  exact this

lemma gram_vectors_close {m : ℝ} {q ρ : Torus d → ℝ} (hq : IsProbDensity q) (hρ : IsProbDensity ρ)
    {κ : ℝ} (hκ : 0 ≤ κ) (hqρ : ∀ x, |q x - ρ x| ≤ κ * ρ x) (T : Finset (NonzeroLattice d)) :
    ∃ u v : Fin T.card → Lp ℝ 2 (volume : Measure (Torus d)),
      (∀ a b, inner ℝ (u a) (u b) = iidCov (withDensityReal q) (blk m T a) (blk m T b)) ∧
      (∀ a b, inner ℝ (v a) (v b) = iidCov (withDensityReal ρ) (blk m T a) (blk m T b)) ∧
      ∑ a, ‖u a - v a‖ ^ 2 ≤ 20 * κ ^ 2 * ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m)) := by
  set sa : Fin T.card → ℝ := fun a => Real.sqrt 2 * Lattice.jp (kOf T a).1 ^ (-m) with hsa
  have hsa0 : ∀ a, 0 ≤ sa a := fun a => mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Torus.jp_pos _).le _)
  have hfm : ∀ a, Measurable (blk m T a) := fun a => (continuous_scMode m _).measurable
  have hfs : ∀ a x, |blk m T a x| ≤ sa a := fun a x => abs_scMode_le m (kOf T a) x
  refine ⟨fun a => (memLp_psiv hq (hfm a) (hfs a)).toLp _,
    fun a => (memLp_psiv hρ (hfm a) (hfs a)).toLp _, ?_, ?_, ?_⟩
  · intro a b
    rw [inner_toLp, cov_eq_integral hq (hfm a) (hfm b) (C := sa a + sa b)
      (fun x => (hfs a x).trans (by linarith [hsa0 b])) (fun x => (hfs b x).trans (by linarith [hsa0 a]))]
  · intro a b
    rw [inner_toLp, cov_eq_integral hρ (hfm a) (hfm b) (C := sa a + sa b)
      (fun x => (hfs a x).trans (by linarith [hsa0 b])) (fun x => (hfs b x).trans (by linarith [hsa0 a]))]
  · have : ∀ a, ‖(memLp_psiv hq (hfm a) (hfs a)).toLp (psiv q (blk m T a)) -
        (memLp_psiv hρ (hfm a) (hfs a)).toLp (psiv ρ (blk m T a))‖ ^ 2 ≤
        20 * κ ^ 2 * Lattice.jp (kOf T a).1 ^ (-(2 * m)) := by
      intro a
      rw [norm_sq_toLp_sub]
      refine (psi_close hq hρ hκ hqρ (hfm a) (hfs a)).trans (le_of_eq ?_)
      rw [hsa]; simp only
      rw [mul_pow, Real.sq_sqrt (by norm_num), Torus.jp_rpow_sq,
        show 2 * (-m) = -(2 * m) by ring]
      ring
    calc _ ≤ ∑ a : Fin T.card, 20 * κ ^ 2 * Lattice.jp (kOf T a).1 ^ (-(2 * m)) := Finset.sum_le_sum fun a _ => this a
      _ = 20 * κ ^ 2 * ∑ a : Fin T.card, Lattice.jp (kOf T a).1 ^ (-(2 * m)) := by rw [Finset.mul_sum]
      _ = _ := by rw [sum_kOf T (fun k => Lattice.jp k.1 ^ (-(2 * m)))]


theorem gaussT_close {m : ℝ} {q ρ : Torus d → ℝ} (hq : IsProbDensity q) (hρ : IsProbDensity ρ)
    {κ : ℝ} (hκ : 0 ≤ κ) (hqρ : ∀ x, |q x - ρ x| ≤ κ * ρ x) (T : Finset (NonzeroLattice d))
    {N : ℕ} (hN : 1 ≤ N) :
    ∃ P : Measure (EuclideanSpace ℝ (Fin T.card) × EuclideanSpace ℝ (Fin T.card)),
      IsProbabilityMeasure P ∧
      P.map Prod.fst = multivariateGaussian (0 : EuclideanSpace ℝ (Fin T.card))
        (∑ _i : Fin N, Yurinskii.momentMatrix
          ((withDensityReal q).map (xiVec (withDensityReal q) N (blk m T)))) ∧
      P.map Prod.snd = multivariateGaussian (0 : EuclideanSpace ℝ (Fin T.card))
        (∑ _i : Fin N, Yurinskii.momentMatrix
          ((withDensityReal ρ).map (xiVec (withDensityReal ρ) N (blk m T)))) ∧
      Integrable (fun z => ‖z.1 - z.2‖ ^ 2) P ∧
      ∫ z, ‖z.1 - z.2‖ ^ 2 ∂P ≤ 20 * κ ^ 2 * ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m)) := by
  haveI := isProb_withDensityReal hq
  haveI := isProb_withDensityReal hρ
  obtain ⟨u, v, hu, hv, hd⟩ := gram_vectors_close (m := m) hq hρ hκ hqρ T
  obtain ⟨P, hP, h1, h2, hI, h3⟩ := gram_coupling u v
  have gu : Matrix.gram ℝ u = ∑ _i : Fin N, Yurinskii.momentMatrix
      ((withDensityReal q).map (xiVec (withDensityReal q) N (blk m T))) := by
    ext a b; rw [Matrix.gram_apply, hu, SigT_apply T hN]
  have gv : Matrix.gram ℝ v = ∑ _i : Fin N, Yurinskii.momentMatrix
      ((withDensityReal ρ).map (xiVec (withDensityReal ρ) N (blk m T))) := by
    ext a b; rw [Matrix.gram_apply, hv, SigT_apply T hN]
  exact ⟨P, hP, h1.trans (by rw [gu]), h2.trans (by rw [gv]), hI, h3.trans_le hd⟩

end L2

end HRS.IID
