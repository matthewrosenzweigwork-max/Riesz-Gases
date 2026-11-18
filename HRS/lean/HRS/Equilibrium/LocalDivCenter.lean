import HRS.Equilibrium.PairCorrection
open MeasureTheory Set Metric
noncomputable section
namespace HRS.LocalDivAux
variable {d : ℕ}

section Center
variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

theorem integrable_of_bdd_prod {f : Torus d × Torus d → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ p, |f p| ≤ C) : Integrable f (μ.prod μ) :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hb p)

/-- bounded measurable functions -/
def BM {α : Type*} [MeasurableSpace α] (f : α → ℝ) : Prop := Measurable f ∧ ∃ C, ∀ p, |f p| ≤ C

theorem BM.add {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : BM f) (hg : BM g) :
    BM (fun p => f p + g p) := by
  obtain ⟨hf1, Cf, hf2⟩ := hf
  obtain ⟨hg1, Cg, hg2⟩ := hg
  exact ⟨hf1.add hg1, Cf + Cg, fun p => (abs_add_le _ _).trans (add_le_add (hf2 p) (hg2 p))⟩

theorem BM.sub {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : BM f) (hg : BM g) :
    BM (fun p => f p - g p) := by
  obtain ⟨hf1, Cf, hf2⟩ := hf
  obtain ⟨hg1, Cg, hg2⟩ := hg
  exact ⟨hf1.sub hg1, Cf + Cg, fun p => (abs_sub _ _).trans (add_le_add (hf2 p) (hg2 p))⟩

theorem BM.mul {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : BM f) (hg : BM g) :
    BM (fun p => f p * g p) := by
  obtain ⟨hf1, Cf, hf2⟩ := hf
  obtain ⟨hg1, Cg, hg2⟩ := hg
  refine ⟨hf1.mul hg1, Cf * Cg, fun p => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hf2 p) (hg2 p) (abs_nonneg _) ((abs_nonneg _).trans (hf2 p))

theorem BM.const {α : Type*} [MeasurableSpace α] (c : ℝ) : BM (fun _ : α => c) :=
  ⟨measurable_const, |c|, fun _ => le_rfl⟩

theorem BM.integrable {f : Torus d × Torus d → ℝ} (hf : BM f) : Integrable f (μ.prod μ) := by
  obtain ⟨h1, C, h2⟩ := hf
  exact integrable_of_bdd_prod h1 h2

theorem integral_fst_mul {k : Torus d × Torus d → ℝ} (hk : Measurable k) {C : ℝ}
    (hkb : ∀ p, |k p| ≤ C) {F : Torus d → ℝ} (hF : Measurable F) {CF : ℝ}
    (hFb : ∀ x, |F x| ≤ CF) :
    ∫ p, F p.1 * k p ∂(μ.prod μ) = ∫ x, F x * ∫ y, k (x, y) ∂μ ∂μ := by
  have hint : Integrable (fun p : Torus d × Torus d => F p.1 * k p) (μ.prod μ) := by
    refine integrable_of_bdd_prod ((hF.comp measurable_fst).mul hk) (C := CF * C) fun p => ?_
    rw [abs_mul]
    exact mul_le_mul (hFb _) (hkb _) (abs_nonneg _) ((abs_nonneg _).trans (hFb p.1))
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [integral_const_mul]

theorem integral_snd_mul {k : Torus d × Torus d → ℝ} (hk : Measurable k) {C : ℝ}
    (hkb : ∀ p, |k p| ≤ C) {F : Torus d → ℝ} (hF : Measurable F) {CF : ℝ}
    (hFb : ∀ x, |F x| ≤ CF) :
    ∫ p, F p.2 * k p ∂(μ.prod μ) = ∫ y, F y * ∫ x, k (x, y) ∂μ ∂μ := by
  have hint : Integrable (fun p : Torus d × Torus d => F p.2 * k p) (μ.prod μ) := by
    refine integrable_of_bdd_prod ((hF.comp measurable_snd).mul hk) (C := CF * C) fun p => ?_
    rw [abs_mul]
    exact mul_le_mul (hFb _) (hkb _) (abs_nonneg _) ((abs_nonneg _).trans (hFb p.2))
  rw [integral_prod_symm _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [integral_const_mul]

theorem center_sq {h : Torus d → Torus d → ℝ}
    (hm : Measurable (fun p : Torus d × Torus d => h p.1 p.2)) {M : ℝ}
    (hM : ∀ x y, |h x y| ≤ M) (hs : ∀ x y, h x y = h y x) :
    ∫ p, canonicalCenter μ h p.1 p.2 ^ 2 ∂(μ.prod μ) =
      ∫ p, h p.1 p.2 ^ 2 ∂(μ.prod μ) - 2 * ∫ x, (∫ y, h x y ∂μ) ^ 2 ∂μ +
        (∫ x, ∫ y, h x y ∂μ ∂μ) ^ 2 := by
  set A : Torus d → ℝ := fun x => ∫ y, h x y ∂μ with hA
  set c : ℝ := ∫ x, A x ∂μ with hc
  have hAm : Measurable A := by
    have := (hm.stronglyMeasurable).integral_prod_right' (ν := μ)
    exact this.measurable
  have hAb : ∀ x, |A x| ≤ M := by
    intro x
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => h x y) (C := M)
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hM x y)
    simpa [hA, Real.norm_eq_abs] using this
  have hcb : |c| ≤ M := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := A) (C := M)
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hAb y)
    simpa [hc, Real.norm_eq_abs] using this
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hAb (Classical.arbitrary _))
  -- the centred kernel
  set N : Torus d → Torus d → ℝ := fun x y => canonicalCenter μ h x y with hN
  have hNeq : ∀ x y, N x y = h x y - A x - A y + c := by
    intro x y
    simp only [hN, canonicalCenter, hA, hc]
    have : ∫ x', h x' y ∂μ = ∫ y', h y y' ∂μ := integral_congr_ae
      (Filter.Eventually.of_forall fun x' => hs x' y)
    rw [this]
  have hNm : Measurable (fun p : Torus d × Torus d => N p.1 p.2) := by
    simp only [hNeq]
    exact ((hm.sub (hAm.comp measurable_fst)).sub (hAm.comp measurable_snd)).add measurable_const
  have hNb : ∀ p : Torus d × Torus d, |N p.1 p.2| ≤ 4 * M := by
    intro p
    rw [hNeq]
    have h1 := hM p.1 p.2
    have h2 := hAb p.1
    have h3 := hAb p.2
    calc |h p.1 p.2 - A p.1 - A p.2 + c| ≤ |h p.1 p.2| + |A p.1| + |A p.2| + |c| := by
          calc _ ≤ |h p.1 p.2 - A p.1 - A p.2| + |c| := abs_add_le _ _
            _ ≤ |h p.1 p.2 - A p.1| + |A p.2| + |c| := by gcongr; exact abs_sub _ _
            _ ≤ _ := by gcongr; exact abs_sub _ _
      _ ≤ 4 * M := by linarith
  -- inner integrals of N vanish
  have hint_y : ∀ x, ∫ y, N x y ∂μ = 0 := by
    intro x
    have e : ∀ y, N x y = (h x y - A x + c) - A y := fun y => by rw [hNeq]; ring
    simp_rw [e]
    have i1 : Integrable (fun y => h x y) μ := Integrable.of_bound
      (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hM x y)
    have i2 : Integrable A μ := Integrable.of_bound hAm.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hAb y)
    have I1 : Integrable (fun y => h x y - A x + c) μ :=
      (i1.sub (integrable_const _)).add (integrable_const _)
    have I2 : Integrable (fun y => h x y - A x) μ := i1.sub (integrable_const _)
    rw [integral_sub I1 i2, integral_add I2 (integrable_const _), integral_sub i1 (integrable_const _)]
    simp [hA, hc]
  have hint_x : ∀ y, ∫ x, N x y ∂μ = 0 := by
    intro y
    have e : ∀ x, N x y = h x y - A x + (c - A y) := fun x => by rw [hNeq]; ring
    simp_rw [e]
    have i1 : Integrable (fun x => h x y) μ := Integrable.of_bound
      (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x y)
    have i2 : Integrable A μ := Integrable.of_bound hAm.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hAb y)
    have e1 : ∫ x, h x y ∂μ = A y := by
      simp only [hA]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => hs x y)
    have I2 : Integrable (fun x => h x y - A x) μ := i1.sub i2
    rw [integral_add I2 (integrable_const _), integral_sub i1 i2, e1]
    simp [hc]
  have hBMh : BM (fun p : Torus d × Torus d => h p.1 p.2) := ⟨hm, M, fun p => hM _ _⟩
  have hBMA : BM A := ⟨hAm, M, hAb⟩
  have hBMa : BM (fun p : Torus d × Torus d => A p.1) := ⟨hAm.comp measurable_fst, M, fun p => hAb _⟩
  have hBMb : BM (fun p : Torus d × Torus d => A p.2) := ⟨hAm.comp measurable_snd, M, fun p => hAb _⟩
  have hBMN : BM (fun p : Torus d × Torus d => N p.1 p.2) := ⟨hNm, 4 * M, hNb⟩
  have hBMc : BM (fun _ : Torus d × Torus d => c) := BM.const c
  have hgoal : ∀ p : Torus d × Torus d, canonicalCenter μ h p.1 p.2 = N p.1 p.2 := fun p => rfl
  simp_rw [hgoal]
  -- ∫ N² = ∫ N * (h - a - b + c)
  have s1 : ∀ p : Torus d × Torus d, N p.1 p.2 ^ 2 =
      N p.1 p.2 * h p.1 p.2 - A p.1 * N p.1 p.2 - A p.2 * N p.1 p.2 + c * N p.1 p.2 := by
    intro p
    have key : N p.1 p.2 ^ 2 = N p.1 p.2 * (h p.1 p.2 - A p.1 - A p.2 + c) := by
      rw [← hNeq p.1 p.2]; ring
    rw [key]; ring
  have s2 : ∫ p : Torus d × Torus d, N p.1 p.2 ^ 2 ∂(μ.prod μ) =
      (∫ p : Torus d × Torus d, N p.1 p.2 * h p.1 p.2 ∂(μ.prod μ)) -
      (∫ p : Torus d × Torus d, A p.1 * N p.1 p.2 ∂(μ.prod μ)) -
      (∫ p : Torus d × Torus d, A p.2 * N p.1 p.2 ∂(μ.prod μ)) +
      ∫ p : Torus d × Torus d, c * N p.1 p.2 ∂(μ.prod μ) := by
    simp_rw [s1]
    have i1 : Integrable (fun p : Torus d × Torus d => N p.1 p.2 * h p.1 p.2) (μ.prod μ) :=
      (hBMN.mul hBMh).integrable
    have i2 : Integrable (fun p : Torus d × Torus d => A p.1 * N p.1 p.2) (μ.prod μ) :=
      (hBMa.mul hBMN).integrable
    have i3 : Integrable (fun p : Torus d × Torus d => A p.2 * N p.1 p.2) (μ.prod μ) :=
      (hBMb.mul hBMN).integrable
    have i4 : Integrable (fun p : Torus d × Torus d => c * N p.1 p.2) (μ.prod μ) :=
      (hBMc.mul hBMN).integrable
    have j1 : Integrable (fun p : Torus d × Torus d => N p.1 p.2 * h p.1 p.2 - A p.1 * N p.1 p.2)
        (μ.prod μ) := i1.sub i2
    have j2 : Integrable (fun p : Torus d × Torus d => N p.1 p.2 * h p.1 p.2 - A p.1 * N p.1 p.2 -
        A p.2 * N p.1 p.2) (μ.prod μ) := j1.sub i3
    rw [integral_add j2 i4, integral_sub j1 i3, integral_sub i1 i2]
  have z1 : ∫ p : Torus d × Torus d, A p.1 * N p.1 p.2 ∂(μ.prod μ) = 0 := by
    rw [integral_fst_mul hBMN.1 (fun p => hNb p) hAm hAb]
    simp [hint_y]
  have z2 : ∫ p : Torus d × Torus d, A p.2 * N p.1 p.2 ∂(μ.prod μ) = 0 := by
    rw [integral_snd_mul hBMN.1 (fun p => hNb p) hAm hAb]
    simp [hint_x]
  have z3 : ∫ p : Torus d × Torus d, c * N p.1 p.2 ∂(μ.prod μ) = 0 := by
    rw [integral_const_mul]
    have : ∫ p : Torus d × Torus d, N p.1 p.2 ∂(μ.prod μ) = 0 := by
      rw [integral_prod _ hBMN.integrable]
      simp [hint_y]
    rw [this, mul_zero]
  -- ∫ N h
  have s3 : ∀ p : Torus d × Torus d, N p.1 p.2 * h p.1 p.2 =
      h p.1 p.2 ^ 2 - A p.1 * h p.1 p.2 - A p.2 * h p.1 p.2 + c * h p.1 p.2 := by
    intro p; rw [hNeq]; ring
  have s4 : ∫ p : Torus d × Torus d, N p.1 p.2 * h p.1 p.2 ∂(μ.prod μ) =
      (∫ p : Torus d × Torus d, h p.1 p.2 ^ 2 ∂(μ.prod μ)) -
      (∫ p : Torus d × Torus d, A p.1 * h p.1 p.2 ∂(μ.prod μ)) -
      (∫ p : Torus d × Torus d, A p.2 * h p.1 p.2 ∂(μ.prod μ)) +
      ∫ p : Torus d × Torus d, c * h p.1 p.2 ∂(μ.prod μ) := by
    simp_rw [s3]
    have i1 : Integrable (fun p : Torus d × Torus d => h p.1 p.2 ^ 2) (μ.prod μ) :=
      (hBMh.mul hBMh).integrable.congr (Filter.Eventually.of_forall fun p => by simp [sq])
    have i2 : Integrable (fun p : Torus d × Torus d => A p.1 * h p.1 p.2) (μ.prod μ) :=
      (hBMa.mul hBMh).integrable
    have i3 : Integrable (fun p : Torus d × Torus d => A p.2 * h p.1 p.2) (μ.prod μ) :=
      (hBMb.mul hBMh).integrable
    have i4 : Integrable (fun p : Torus d × Torus d => c * h p.1 p.2) (μ.prod μ) :=
      (hBMc.mul hBMh).integrable
    have j1 : Integrable (fun p : Torus d × Torus d => h p.1 p.2 ^ 2 - A p.1 * h p.1 p.2)
        (μ.prod μ) := i1.sub i2
    have j2 : Integrable (fun p : Torus d × Torus d => h p.1 p.2 ^ 2 - A p.1 * h p.1 p.2 -
        A p.2 * h p.1 p.2) (μ.prod μ) := j1.sub i3
    rw [integral_add j2 i4, integral_sub j1 i3, integral_sub i1 i2]
  have w1 : ∫ p : Torus d × Torus d, A p.1 * h p.1 p.2 ∂(μ.prod μ) = ∫ x, A x ^ 2 ∂μ := by
    rw [integral_fst_mul hm (fun p => hM _ _) hAm hAb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hA]; ring
  have w2 : ∫ p : Torus d × Torus d, A p.2 * h p.1 p.2 ∂(μ.prod μ) = ∫ x, A x ^ 2 ∂μ := by
    rw [integral_snd_mul hm (fun p => hM _ _) hAm hAb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have : ∫ x, h x y ∂μ = A y := by
      simp only [hA]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => hs x y)
    show A y * ∫ x, h x y ∂μ = A y ^ 2
    rw [this]; ring
  have w3 : ∫ p : Torus d × Torus d, c * h p.1 p.2 ∂(μ.prod μ) = c ^ 2 := by
    rw [integral_const_mul, integral_prod _ hBMh.integrable]
    simp only [hc, hA]; ring
  rw [s2, z1, z2, z3, s4, w1, w2, w3]
  simp only [hc, hA]
  ring

end Center
end HRS.LocalDivAux
