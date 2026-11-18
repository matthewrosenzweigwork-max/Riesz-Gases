import HRS.MS.S113X2B3

/-!
# S11.3 X2 part B (worker S11Z3), Kato / renormalization identity

Exact integration by parts on `ℝⁿ`: for `q > 0` of class `C²`, `r ≥ 0` of class `C²` with compact support,
`Φ' = Φ₁`, `Φ₁' = Φ₂ ≥ 0` (on `[0,∞)`), `Φ 0 = Φ₁ 0 = 0`, the integral of
`Φ₁(r) (ν Δ(q r) - div(q r b)) - (ν Δq - div(q b)) (r Φ₁(r) - Φ(r))` equals `-ν ∫ q Φ₂(r) |∇r|²`, hence is `≤ 0`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HRS.MS.S113X2B

variable {n : ℕ}

/-- The integral of a directional derivative of a compactly supported `C¹` function vanishes. -/
lemma s113b_int_fderiv_zero {g : s113b_E n → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (v : s113b_E n) : ∫ x, fderiv ℝ g x v = 0 := by
  have hgc : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgcs : HasCompactSupport (fun x => fderiv ℝ g x v) :=
    (hc.fderiv ℝ).comp_left (g := fun L : s113b_E n →L[ℝ] ℝ => L v) (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : s113b_E n => (1 : ℝ)) (g := g) (v := v)
    (by simp) (by simpa using hgc.integrable_of_hasCompactSupport hgcs)
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => differentiableAt_const _) (fun x _ => hgd x)
  simpa using h

/-- A `C¹` composition `F ∘ r` with the chain rule, using `F' = F1` only on `[0,∞)`. -/
lemma s113b_comp_c1 {r : s113b_E n → ℝ} (hr : ContDiff ℝ 1 r) (hr0 : ∀ x, 0 ≤ r x)
    {F F1 : ℝ → ℝ} (hF : ∀ z, 0 ≤ z → HasDerivAt F (F1 z) z) (hF1c : ContinuousOn F1 (Ici 0)) :
    ContDiff ℝ 1 (fun y => F (r y)) ∧ ∀ y, fderiv ℝ (fun y => F (r y)) y = F1 (r y) • fderiv ℝ r y := by
  have hrd : Differentiable ℝ r := hr.differentiable (by norm_num)
  have hD : ∀ y, HasFDerivAt (fun y => F (r y)) (F1 (r y) • fderiv ℝ r y) y := fun y =>
    (hF (r y) (hr0 y)).comp_hasFDerivAt y (hrd y).hasFDerivAt
  have hfd : ∀ y, fderiv ℝ (fun y => F (r y)) y = F1 (r y) • fderiv ℝ r y := fun y => (hD y).fderiv
  refine ⟨contDiff_one_iff_fderiv.2 ⟨fun y => (hD y).differentiableAt, ?_⟩, hfd⟩
  have hc1 : Continuous (fun y => F1 (r y)) := hF1c.comp_continuous hr.continuous (fun y => hr0 y)
  have : fderiv ℝ (fun y => F (r y)) = fun y => F1 (r y) • fderiv ℝ r y := funext hfd
  rw [this]
  exact hc1.smul (hr.continuous_fderiv (by norm_num))

/-- Directional derivative of a `C²` function is `C¹`. -/
lemma s113b_dD {f : s113b_E n → ℝ} (hf : ContDiff ℝ 2 f) (v : s113b_E n) :
    ContDiff ℝ 1 (fun y => fderiv ℝ f y v) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- The Laplacian as a sum of iterated directional derivatives. -/
lemma s113b_lap_eq {f : s113b_E n → ℝ} (hf : ContDiff ℝ 2 f) (x : s113b_E n) :
    s113b_lap f x = ∑ k : Fin n, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single k 1)) x
      (EuclideanSpace.single k 1) := by
  unfold s113b_lap
  refine Finset.sum_congr rfl fun k _ => ?_
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single k (1 : ℝ)) x)
  rw [h.fderiv]
  simp

/-- Second directional derivative of a product. -/
lemma s113b_D2_mul {q r : s113b_E n → ℝ} (hq : ContDiff ℝ 2 q) (hr : ContDiff ℝ 2 r) (k : Fin n)
    (x : s113b_E n) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => q z * r z) y (EuclideanSpace.single k 1)) x
        (EuclideanSpace.single k 1) =
      q x * fderiv ℝ (fun y => fderiv ℝ r y (EuclideanSpace.single k 1)) x (EuclideanSpace.single k 1)
      + 2 * (fderiv ℝ q x (EuclideanSpace.single k 1) * fderiv ℝ r x (EuclideanSpace.single k 1))
      + r x * fderiv ℝ (fun y => fderiv ℝ q y (EuclideanSpace.single k 1)) x (EuclideanSpace.single k 1) := by
  have hqd : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hrd : Differentiable ℝ r := hr.differentiable (by norm_num)
  have h1 : (fun y => fderiv ℝ (fun z => q z * r z) y (EuclideanSpace.single k 1)) =
      fun y => q y * fderiv ℝ r y (EuclideanSpace.single k 1) + r y * fderiv ℝ q y (EuclideanSpace.single k 1) := by
    funext y
    have := ((hqd y).hasFDerivAt.mul (hrd y).hasFDerivAt)
    have h2 : fderiv ℝ (fun z => q z * r z) y = q y • fderiv ℝ r y + r y • fderiv ℝ q y := this.fderiv
    rw [h2]; simp
  have hDq := ((s113b_dD hq (EuclideanSpace.single k 1)).differentiable (by norm_num) x).hasFDerivAt
  have hDr := ((s113b_dD hr (EuclideanSpace.single k 1)).differentiable (by norm_num) x).hasFDerivAt
  have h3 : HasFDerivAt (fun y => q y * fderiv ℝ r y (EuclideanSpace.single k 1)
      + r y * fderiv ℝ q y (EuclideanSpace.single k 1)) _ x :=
    ((hqd x).hasFDerivAt.mul hDr).add ((hrd x).hasFDerivAt.mul hDq)
  rw [h1]
  have h4 := h3.fderiv
  rw [h4]
  simp
  ring

/-- Divergence of `c • b` in coordinates. -/
lemma s113b_div_smul (c : s113b_E n → ℝ) (b : s113b_E n → s113b_E n) (x : s113b_E n) :
    s113b_div (fun y => c y • b y) x =
      ∑ k : Fin n, fderiv ℝ (fun y => c y * b y k) x (EuclideanSpace.single k 1) := by
  simp [s113b_div]

/-- The exact primitive: the integrand minus the dissipation term is `∑_k ∂_k (H k)`. -/
def s113b_H (ν : ℝ) (b : s113b_E n → s113b_E n) (q r : s113b_E n → ℝ) (Φ Φ1 : ℝ → ℝ) (k : Fin n)
    (y : s113b_E n) : ℝ :=
  ν * (q y * Φ1 (r y) * fderiv ℝ r y (EuclideanSpace.single k 1)
      + fderiv ℝ q y (EuclideanSpace.single k 1) * Φ (r y)) - q y * b y k * Φ (r y)

lemma s113b_coord_cd {b : s113b_E n → s113b_E n} (hb : ContDiff ℝ 1 b) (k : Fin n) :
    ContDiff ℝ 1 (fun y => b y k) :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hb

/-- Pointwise identity. -/
lemma s113b_pointwise {ν : ℝ} {b : s113b_E n → s113b_E n} (hb : ContDiff ℝ 1 b)
    {q r : s113b_E n → ℝ} (hq : ContDiff ℝ 2 q) (hr : ContDiff ℝ 2 r) (hr0 : ∀ x, 0 ≤ r x)
    {Φ Φ1 Φ2 : ℝ → ℝ} (hΦ : ∀ z, 0 ≤ z → HasDerivAt Φ (Φ1 z) z)
    (hΦ1 : ∀ z, 0 ≤ z → HasDerivAt Φ1 (Φ2 z) z) (x : s113b_E n) :
    Φ1 (r x) * (ν * s113b_lap (fun y => q y * r y) x - s113b_div (fun y => (q y * r y) • b y) x)
        - (ν * s113b_lap q x - s113b_div (fun y => q y • b y) x) * (r x * Φ1 (r x) - Φ (r x)) =
      ∑ k : Fin n, (fderiv ℝ (s113b_H ν b q r Φ Φ1 k) x (EuclideanSpace.single k 1)
        - ν * (q x * Φ2 (r x) * (fderiv ℝ r x (EuclideanSpace.single k 1)) ^ 2)) := by
  rw [s113b_lap_eq (hq.mul hr), s113b_lap_eq hq, s113b_div_smul (fun y => q y * r y) b x,
    s113b_div_smul q b x]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hqd : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hrd : Differentiable ℝ r := hr.differentiable (by norm_num)
  have hbk := (s113b_coord_cd hb k).differentiable (by norm_num) x
  have hDq := ((s113b_dD hq (EuclideanSpace.single k 1)).differentiable (by norm_num) x).hasFDerivAt
  have hDr := ((s113b_dD hr (EuclideanSpace.single k 1)).differentiable (by norm_num) x).hasFDerivAt
  have hP : HasFDerivAt (fun y => Φ (r y)) (Φ1 (r x) • fderiv ℝ r x) x :=
    (hΦ (r x) (hr0 x)).comp_hasFDerivAt x (hrd x).hasFDerivAt
  have hP1 : HasFDerivAt (fun y => Φ1 (r y)) (Φ2 (r x) • fderiv ℝ r x) x :=
    (hΦ1 (r x) (hr0 x)).comp_hasFDerivAt x (hrd x).hasFDerivAt
  have e1 : HasFDerivAt (fun y => q y * r y * b y k) _ x :=
    ((hqd x).hasFDerivAt.mul (hrd x).hasFDerivAt).mul hbk.hasFDerivAt
  have e2 : HasFDerivAt (fun y => q y * b y k) _ x := (hqd x).hasFDerivAt.mul hbk.hasFDerivAt
  have e3 : HasFDerivAt (fun y => ν * (q y * Φ1 (r y) * fderiv ℝ r y (EuclideanSpace.single k 1)
      + fderiv ℝ q y (EuclideanSpace.single k 1) * Φ (r y)) - q y * b y k * Φ (r y)) _ x :=
    ((((hqd x).hasFDerivAt.mul hP1).mul hDr).add (hDq.mul hP)).const_mul ν |>.sub
      (((hqd x).hasFDerivAt.mul hbk.hasFDerivAt).mul hP)
  unfold s113b_H
  rw [s113b_D2_mul hq hr k x, e1.fderiv, e2.fderiv, e3.fderiv]
  simp only [Pi.mul_apply, add_apply, smul_apply, sub_apply, smul_eq_mul]
  ring

/-- **Kato identity** (exact integration by parts). -/
theorem s113b_kato_identity {ν : ℝ} {b : s113b_E n → s113b_E n} (hb : ContDiff ℝ 1 b)
    {q r : s113b_E n → ℝ} (hq : ContDiff ℝ 2 q) (hr : ContDiff ℝ 2 r) (hrc : HasCompactSupport r)
    (hr0 : ∀ x, 0 ≤ r x) {Φ Φ1 Φ2 : ℝ → ℝ} (hΦ : ∀ z, 0 ≤ z → HasDerivAt Φ (Φ1 z) z)
    (hΦ1 : ∀ z, 0 ≤ z → HasDerivAt Φ1 (Φ2 z) z) (hΦ2c : ContinuousOn Φ2 (Set.Ici 0))
    (hΦ0 : Φ 0 = 0) (hΦ10 : Φ1 0 = 0) :
    ∫ x, (Φ1 (r x) * (ν * s113b_lap (fun y => q y * r y) x - s113b_div (fun y => (q y * r y) • b y) x)
        - (ν * s113b_lap q x - s113b_div (fun y => q y • b y) x) * (r x * Φ1 (r x) - Φ (r x))) =
      -ν * ∫ x, q x * Φ2 (r x) * ∑ k : Fin n, (fderiv ℝ r x (EuclideanSpace.single k 1)) ^ 2 := by
  have _ := hΦ10
  have hr1 : ContDiff ℝ 1 r := hr.of_le (by norm_num)
  have hq1 : ContDiff ℝ 1 q := hq.of_le (by norm_num)
  have hΦ1c : ContinuousOn Φ1 (Set.Ici 0) := fun z hz => (hΦ1 z hz).continuousAt.continuousWithinAt
  obtain ⟨hPc, -⟩ := s113b_comp_c1 hr1 hr0 hΦ hΦ1c
  obtain ⟨hP1c, -⟩ := s113b_comp_c1 hr1 hr0 hΦ1 hΦ2c
  have hout : ∀ x, x ∉ tsupport r → r x = 0 ∧ fderiv ℝ r x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport hx,
      image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))⟩
  have hHc : ∀ k, ContDiff ℝ 1 (s113b_H ν b q r Φ Φ1 k) := fun k => by
    unfold s113b_H
    exact (contDiff_const.mul (((hq1.mul hP1c).mul (s113b_dD hr _)).add ((s113b_dD hq _).mul hPc))).sub
      ((hq1.mul (s113b_coord_cd hb k)).mul hPc)
  have hHcs : ∀ k, HasCompactSupport (s113b_H ν b q r Φ Φ1 k) := fun k =>
    HasCompactSupport.intro hrc.isCompact (fun x hx => by
      obtain ⟨h1, h2⟩ := hout x hx
      simp [s113b_H, h1, h2, hΦ0])
  have hHint : ∀ k, Integrable (fun x => fderiv ℝ (s113b_H ν b q r Φ Φ1 k) x (EuclideanSpace.single k 1)) := fun k =>
    Continuous.integrable_of_hasCompactSupport
      ((hHc k).continuous_fderiv (by norm_num) |>.clm_apply continuous_const)
      (((hHcs k).fderiv ℝ).comp_left (g := fun L : s113b_E n →L[ℝ] ℝ => L (EuclideanSpace.single k 1)) (by simp))
  have hTint : ∀ k : Fin n, Integrable (fun x => q x * Φ2 (r x) * (fderiv ℝ r x (EuclideanSpace.single k 1)) ^ 2) := fun k =>
    Continuous.integrable_of_hasCompactSupport
      ((hq.continuous.mul (hΦ2c.comp_continuous hr.continuous (fun y => hr0 y))).mul
        ((hr.continuous_fderiv (by norm_num) |>.clm_apply continuous_const).pow 2))
      (HasCompactSupport.intro hrc.isCompact (fun x hx => by
        obtain ⟨h1, h2⟩ := hout x hx
        simp [h2]))
  have hsum : ∫ x, q x * Φ2 (r x) * ∑ k : Fin n, (fderiv ℝ r x (EuclideanSpace.single k 1)) ^ 2 =
      ∑ k : Fin n, ∫ x, q x * Φ2 (r x) * (fderiv ℝ r x (EuclideanSpace.single k 1)) ^ 2 := by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ (fun k _ => hTint k)
  calc _ = ∫ x, ∑ k : Fin n, (fderiv ℝ (s113b_H ν b q r Φ Φ1 k) x (EuclideanSpace.single k 1)
          - ν * (q x * Φ2 (r x) * (fderiv ℝ r x (EuclideanSpace.single k 1)) ^ 2)) :=
        integral_congr_ae (Eventually.of_forall fun x => s113b_pointwise hb hq hr hr0 hΦ hΦ1 x)
    _ = ∑ k : Fin n, ∫ x, (fderiv ℝ (s113b_H ν b q r Φ Φ1 k) x (EuclideanSpace.single k 1)
          - ν * (q x * Φ2 (r x) * (fderiv ℝ r x (EuclideanSpace.single k 1)) ^ 2)) :=
        integral_finsetSum _ (fun k _ => (hHint k).sub ((hTint k).const_mul ν))
    _ = ∑ k : Fin n, (-ν * ∫ x, q x * Φ2 (r x) * (fderiv ℝ r x (EuclideanSpace.single k 1)) ^ 2) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_sub (hHint k) ((hTint k).const_mul ν), integral_const_mul,
          s113b_int_fderiv_zero (hHc k) (hHcs k)]
        ring
    _ = _ := by rw [hsum, Finset.mul_sum]

/-- **Kato inequality**: the integral is `≤ 0`. -/
theorem s113b_kato {ν : ℝ} (hν : 0 < ν) {b : s113b_E n → s113b_E n} (hb : ContDiff ℝ 1 b)
    {q r : s113b_E n → ℝ} (hq : ContDiff ℝ 2 q) (hq0 : ∀ x, 0 < q x) (hr : ContDiff ℝ 2 r)
    (hrc : HasCompactSupport r) (hr0 : ∀ x, 0 ≤ r x)
    {Φ Φ1 Φ2 : ℝ → ℝ} (hΦ : ∀ z, 0 ≤ z → HasDerivAt Φ (Φ1 z) z)
    (hΦ1 : ∀ z, 0 ≤ z → HasDerivAt Φ1 (Φ2 z) z) (hΦ2c : ContinuousOn Φ2 (Set.Ici 0))
    (hΦ2 : ∀ z, 0 ≤ z → 0 ≤ Φ2 z) (hΦ0 : Φ 0 = 0) (hΦ10 : Φ1 0 = 0) :
    ∫ x, (Φ1 (r x) * (ν * s113b_lap (fun y => q y * r y) x - s113b_div (fun y => (q y * r y) • b y) x)
        - (ν * s113b_lap q x - s113b_div (fun y => q y • b y) x) * (r x * Φ1 (r x) - Φ (r x))) ≤ 0 := by
  rw [s113b_kato_identity hb hq hr hrc hr0 hΦ hΦ1 hΦ2c hΦ0 hΦ10]
  have h : 0 ≤ ∫ x, q x * Φ2 (r x) * ∑ k : Fin n, (fderiv ℝ r x (EuclideanSpace.single k 1)) ^ 2 :=
    integral_nonneg fun x => mul_nonneg (mul_nonneg (hq0 x).le (hΦ2 _ (hr0 x)))
      (Finset.sum_nonneg fun k _ => sq_nonneg _)
  nlinarith [mul_nonneg hν.le h]

end HRS.MS.S113X2B
