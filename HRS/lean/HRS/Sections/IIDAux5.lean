import HRS.Sections.IIDAux4

/-!
# IID helper chain, part 5: finite-mode theorem (see the chain plan in `IIDAux1`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Convolution

namespace HRS.IID

section Law

open HRS.InitialDataAux
open scoped Matrix

variable {p : ℕ}

lemma inner_eq_sum (w y : EuclideanSpace ℝ (Fin p)) : inner ℝ w y = ∑ c, w c * y c := by
  simp [PiLp.inner_apply, mul_comm]

lemma bilin_momentMatrix (ρ : Measure (EuclideanSpace ℝ (Fin p)))
    (h2 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => ‖x‖ ^ 2) ρ) (v v' : Fin p → ℝ) :
    v ⬝ᵥ (Yurinskii.momentMatrix ρ *ᵥ v') =
      ∫ x, (∑ c, v c * x c) * (∑ c, v' c * x c) ∂ρ := by
  have hI := Yurinskii.integrable_coord_mul h2
  have e : ∀ x : EuclideanSpace ℝ (Fin p), (∑ c, v c * x c) * (∑ c, v' c * x c) =
      ∑ c, ∑ d, (v c * v' d) * (x c * x d) := fun x => by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => (hI c d).const_mul _]
  simp only [dotProduct, Matrix.mulVec, Yurinskii.momentMatrix, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun d _ => (hI c d).const_mul _]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [integral_const_mul]; ring

lemma momMatch_of_matrix {ρ0 : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure ρ0]
    (h2 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => ‖x‖ ^ 2) ρ0)
    (h0 : ∀ c, ∫ y, y c ∂ρ0 = 0)
    {B : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)} {N : ℕ} (hN : 1 ≤ N)
    (hB : ∀ w w', inner ℝ (B w) (B w') =
      w.ofLp ⬝ᵥ (∑ _i : Fin N, Yurinskii.momentMatrix ρ0) *ᵥ w'.ofLp) :
    MomMatch B (N : ℝ)⁻¹ ρ0 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hI := Yurinskii.integrable_coord_mul h2
  have hIc : ∀ c, Integrable (fun y : EuclideanSpace ℝ (Fin p) => y c) ρ0 := fun c => by
    have := (Yurinskii.integrable_coord_mul h2 c c)
    refine (h2.add (integrable_const (1 : ℝ))).mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    have h1 : |y c| ≤ ‖y‖ := by simpa using PiLp.norm_apply_le y c
    show |y c| ≤ ‖y‖ ^ 2 + 1
    nlinarith [sq_nonneg (‖y‖ - 1), abs_nonneg (y c)]
  refine ⟨h2, fun w => ?_, fun w w' => ?_⟩
  · simp_rw [inner_eq_sum]
    rw [integral_finsetSum _ fun c _ => (hIc c).const_mul _]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [integral_const_mul, h0, mul_zero]
  · rw [hB]
    simp_rw [inner_eq_sum]
    rw [← bilin_momentMatrix ρ0 h2]
    have : ∑ _i : Fin N, Yurinskii.momentMatrix ρ0 = (N : ℝ) • Yurinskii.momentMatrix ρ0 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
    rw [this, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]

lemma lip_test_le (μ₁ μ₂ : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h1 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => ‖x‖ ^ 2) μ₁)
    (h2 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => ‖x‖ ^ 2) μ₂) {t : ℝ}
    (hfd : ∀ (R : ℝ) (f : EuclideanSpace ℝ (Fin p) → ℝ), LipschitzWith 1 f → (∀ z, |f z| ≤ R) →
      ∫ z, f z ∂μ₁ - ∫ z, f z ∂μ₂ ≤ t)
    {h : EuclideanSpace ℝ (Fin p) → ℝ} (hh : LipschitzWith 1 h) :
    ∫ z, h z ∂μ₁ - ∫ z, h z ∂μ₂ ≤ t := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  set m : ℝ := ∫ x, ‖x‖ ^ 2 ∂μ₁ + ∫ x, ‖x‖ ^ 2 ∂μ₂ with hm
  have hm0 : 0 ≤ m := add_nonneg (integral_nonneg fun _ => by positivity)
    (integral_nonneg fun _ => by positivity)
  set R : ℝ := m / (4 * η) + 1 with hR
  have hRpos : 0 < R := by positivity
  set u : EuclideanSpace ℝ (Fin p) → ℝ := fun x => h x - h 0 with hu
  have hul : LipschitzWith 1 u := LipschitzWith.of_dist_le_mul fun x y => by
    simpa [hu, Real.dist_eq] using hh.dist_le_mul x y
  set f : EuclideanSpace ℝ (Fin p) → ℝ := fun x => max (-R) (min R (u x)) with hf
  have hfl : LipschitzWith 1 f := (hul.const_min R).const_max (-R)
  have hfR : ∀ y, |f y| ≤ R := fun y => by
    rw [abs_le]; simp only [hf]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have huf : ∀ x, |u x - f x| ≤ ‖x‖ ^ 2 / (4 * R) := fun x => by
    refine clamp_err hRpos ?_
    have := hul.dist_le_mul x 0
    simpa [hu, Real.dist_eq] using this
  have hn1 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => ‖x‖) μ₁ :=
    ((integrable_const (1 : ℝ)).add h1).mono' (by fun_prop) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      show ‖y‖ ≤ 1 + ‖y‖ ^ 2
      nlinarith [sq_nonneg (‖y‖ - 1)])
  have hn2 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => ‖x‖) μ₂ :=
    ((integrable_const (1 : ℝ)).add h2).mono' (by fun_prop) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      show ‖y‖ ≤ 1 + ‖y‖ ^ 2
      nlinarith [sq_nonneg (‖y‖ - 1)])
  have ihh1 : Integrable h μ₁ := integrable_lip_comp μ₁ hh (Z := id) measurable_id hn1
  have ihh2 : Integrable h μ₂ := integrable_lip_comp μ₂ hh (Z := id) measurable_id hn2
  have iu1 : Integrable u μ₁ := ihh1.sub (integrable_const _)
  have iu2 : Integrable u μ₂ := ihh2.sub (integrable_const _)
  have if1 : Integrable f μ₁ := Integrable.of_bound hfl.continuous.aestronglyMeasurable R
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hfR y)
  have if2 : Integrable f μ₂ := Integrable.of_bound hfl.continuous.aestronglyMeasurable R
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hfR y)
  have ie1 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => ‖x‖ ^ 2 / (4 * R)) μ₁ := h1.div_const _
  have ie2 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => ‖x‖ ^ 2 / (4 * R)) μ₂ := h2.div_const _
  have hcu1 : ∫ z, h z ∂μ₁ = ∫ z, u z ∂μ₁ + h 0 := by
    simp only [hu]; rw [integral_sub ihh1 (integrable_const _)]; simp
  have hcu2 : ∫ z, h z ∂μ₂ = ∫ z, u z ∂μ₂ + h 0 := by
    simp only [hu]; rw [integral_sub ihh2 (integrable_const _)]; simp
  have hA : ∫ z, u z ∂μ₁ ≤ ∫ z, f z ∂μ₁ + ∫ x, ‖x‖ ^ 2 / (4 * R) ∂μ₁ := by
    rw [← integral_add if1 ie1]
    exact integral_mono iu1 (if1.add ie1) fun x => by
      have := (abs_le.1 (huf x)).2; simp only [Pi.add_apply]; linarith
  have hB : ∫ z, f z ∂μ₂ - ∫ x, ‖x‖ ^ 2 / (4 * R) ∂μ₂ ≤ ∫ z, u z ∂μ₂ := by
    rw [← integral_sub if2 ie2]
    exact integral_mono (if2.sub ie2) iu2 fun x => by
      have := (abs_le.1 (huf x)).1; simp only [Pi.sub_apply]; linarith
  have hfd' := hfd R f hfl hfR
  have hmR : m / (4 * R) ≤ η := by
    rw [div_le_iff₀ (by positivity)]
    have : η * (4 * R) = m + 4 * η := by rw [hR]; field_simp
    rw [mul_comm] at this ⊢
    linarith
  have hsum : ∫ x, ‖x‖ ^ 2 / (4 * R) ∂μ₁ + ∫ x, ‖x‖ ^ 2 / (4 * R) ∂μ₂ = m / (4 * R) := by
    rw [integral_div, integral_div, hm]; ring
  rw [hcu1, hcu2]
  linarith

lemma ae_bound_cpow {μ : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure μ] {b : ℝ}
    (hb : ∀ᵐ y ∂μ, ‖y‖ ≤ b) (k : ℕ) : ∀ᵐ z ∂(cpow μ k), ‖z‖ ≤ k * b := by
  induction k with
  | zero =>
    simp only [cpow, Nat.cast_zero, zero_mul]
    rw [ae_dirac_iff (measurableSet_le (by fun_prop) (by fun_prop))]
    simp
  | succ k ih =>
    simp only [cpow, Measure.conv]
    rw [ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) (by fun_prop))]
    have h1 : ∀ᵐ q ∂(μ.prod (cpow μ k)), ‖q.1‖ ≤ b :=
      (measurePreserving_fst (μ := μ) (ν := cpow μ k)).quasiMeasurePreserving.ae hb
    have h2 : ∀ᵐ q ∂(μ.prod (cpow μ k)), ‖q.2‖ ≤ k * b :=
      (measurePreserving_snd (μ := μ) (ν := cpow μ k)).quasiMeasurePreserving.ae ih
    filter_upwards [h1, h2] with q hq1 hq2
    calc ‖q.1 + q.2‖ ≤ ‖q.1‖ + ‖q.2‖ := norm_add_le _ _
      _ ≤ b + k * b := add_le_add hq1 hq2
      _ = ((k + 1 : ℕ) : ℝ) * b := by push_cast; ring

lemma integrable_norm_sq_cpow {μ : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure μ] {b : ℝ}
    (hb : ∀ᵐ y ∂μ, ‖y‖ ≤ b) (k : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin p) => ‖z‖ ^ 2) (cpow μ k) := by
  refine Integrable.of_bound (by fun_prop) ((k * b) ^ 2) ((ae_bound_cpow hb k).mono fun z hz => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) hz 2

theorem w1_cpow_nuS {B binv : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)}
    (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (hBb : ∀ y, B (binv y) = y)
    (hbB : ∀ y, binv (B y) = y) {N : ℕ} (hN : 1 ≤ N)
    {μ : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure μ]
    (hμ : MomMatch B (N : ℝ)⁻¹ μ) {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ᵐ y ∂μ, ‖y‖ ≤ b) :
    wassersteinE 1 (cpow μ N) (nuS B 1) ≤
      ENNReal.ofReal (b * (p * Real.log (Real.exp 1 * N) + 2)) := by
  set P : Measure (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p)) := (cpow μ N).prod (nuS B 1) with hP
  have hm1 : MemLp (id : EuclideanSpace ℝ (Fin p) → _) 2 (cpow μ N) :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).2 (integrable_norm_sq_cpow hb N)
  have hm2 : MemLp (id : EuclideanSpace ℝ (Fin p) → _) 2 (nuS B 1) :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).2 (integrable_nuS_norm_sq 1)
  have hX2 : MemLp Prod.fst 2 P := hm1.comp_measurePreserving (measurePreserving_fst (μ := cpow μ N) (ν := nuS B 1))
  have hY2 : MemLp Prod.snd 2 P := hm2.comp_measurePreserving (measurePreserving_snd (μ := cpow μ N) (ν := nuS B 1))
  have hd := wassersteinE_one_le_of_dual P Prod.fst Prod.snd measurable_fst measurable_snd hX2 hY2
    (b * (p * Real.log (Real.exp 1 * N) + 2)) (by
      intro h hh
      have e1 : ∫ ω, h (ω.1) ∂P = ∫ z, h z ∂(cpow μ N) := by
        have := integral_map (μ := P) (φ := Prod.fst) measurable_fst.aemeasurable
          (f := h) hh.continuous.aestronglyMeasurable
        rw [← this, hP, Measure.map_fst_prod]; simp
      have e2 : ∫ ω, h (ω.2) ∂P = ∫ z, h z ∂(nuS B 1) := by
        have := integral_map (μ := P) (φ := Prod.snd) measurable_snd.aemeasurable
          (f := h) hh.continuous.aestronglyMeasurable
        rw [← this, hP, Measure.map_snd_prod]; simp
      rw [e1, e2]
      refine lip_test_le (cpow μ N) (nuS B 1) (integrable_norm_sq_cpow hb N) (integrable_nuS_norm_sq 1)
        (fun R f hf hR => ?_) hh
      exact (le_abs_self _).trans (fd_lip hBs hBb hbB hN hμ hb0 hb hf hR))
  have e1 : law P Prod.fst = cpow μ N := by
    show P.map Prod.fst = _
    rw [hP, Measure.map_fst_prod]; simp
  have e2 : law P Prod.snd = nuS B 1 := by
    show P.map Prod.snd = _
    rw [hP, Measure.map_snd_prod]; simp
  rw [e1, e2] at hd
  exact hd

end Law

end HRS.IID

namespace HRS.IID

section FM

open HRS.InitialDataAux
open scoped Matrix

variable {d : ℕ}

/-- The Hilbert-space tail `∑_{k ∉ T} 2 ⟨k⟩^{-2m}`. -/
def tailR (d : ℕ) (m : ℝ) (T : Finset (NonzeroLattice d)) : ℝ :=
  ∑' k : NonzeroLattice d, if k ∈ T then 0 else 2 * Lattice.jp k.1 ^ (-(2 * m))

lemma summable_two_jp {m : ℝ} (hm : (d : ℝ) < 2 * m) :
    Summable fun k : NonzeroLattice d => 2 * Lattice.jp k.1 ^ (-(2 * m)) :=
  (summable_jp_rpow (d := d) m hm).mul_left 2

lemma tail_S {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (T : Finset (NonzeroLattice d)) :
    ∫⁻ X, ‖fld m N μ X - projT T (fld m N μ X)‖ₑ ∂(Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (Real.sqrt (tailR d m T)) := by
  have hF : Measurable (fld m N μ) := (continuous_fld hm hN μ).measurable
  exact lintegral_tail_le (Measure.pi fun _ : Fin N => μ) (fld m N μ) hF T (summable_two_jp hm)
    (fun k => mul_nonneg zero_le_two (Real.rpow_nonneg (Torus.jp_pos _).le _)) (fun k => coord_fld_sq_lintegral hm hN μ k)

lemma tail_G {m : ℝ} (hm : (d : ℝ) < 2 * m) {ρ : Measure (Torus d)} [IsProbabilityMeasure ρ]
    {γ : Measure (NegSobolev d m)} [IsProbabilityMeasure γ] (hγ : IsCenteredGaussianWithCov m γ (iidCov ρ))
    (T : Finset (NonzeroLattice d)) :
    ∫⁻ F, ‖F - projT T F‖ₑ ∂γ ≤ ENNReal.ofReal (Real.sqrt (tailR d m T)) := by
  have := negSobolev_secondCountable d m
  exact lintegral_tail_le γ id measurable_id T (summable_two_jp hm)
    (fun k => mul_nonneg zero_le_two (Real.rpow_nonneg (Torus.jp_pos _).le _))
    (fun k => coord_gauss_sq_lintegral hγ k)

lemma coordVec_fld {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (T : Finset (NonzeroLattice d)) (X : Config d N) :
    coordVec T (fld m N μ X) = ∑ i, xiVec μ N (blk m T) (X i) := by
  ext j
  have h1 : (∑ i, xiVec μ N (blk m T) (X i)) j = ∑ i, xiVec μ N (blk m T) (X i) j := by
    simp
  rw [h1]
  show NegSobolev.coord (fld m N μ X) (kOf T j) = _
  rw [coord_fld hm hN μ X (kOf T j)]
  simp only [xiVec_apply, blk, ← Finset.mul_sum]

lemma law_coordVec_fld {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (T : Finset (NonzeroLattice d)) :
    (Measure.pi fun _ : Fin N => μ).map (fun X => coordVec T (fld m N μ X)) =
      cpow (μ.map (xiVec μ N (blk m T))) N := by
  have hfc : ∀ a, Continuous (blk m T a) := fun a => continuous_scMode m _
  have hξc := continuous_xiVec μ N (blk m T) hfc
  have hξm : Measurable (xiVec μ N (blk m T)) := hξc.measurable
  rw [← pi_map_sum_eq_cpow]
  have hsm : Measurable (fun q : Fin N → EuclideanSpace ℝ (Fin T.card) => ∑ i, q i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hξi : Measurable (fun (X : Config d N) (i : Fin N) => xiVec μ N (blk m T) (X i)) :=
    Measurable.of_eval fun i => hξm.comp (measurable_pi_apply i)
  have e : (fun X : Config d N => coordVec T (fld m N μ X)) =
      (fun q : Fin N → EuclideanSpace ℝ (Fin T.card) => ∑ i, q i) ∘
        (fun (X : Config d N) (i : Fin N) => xiVec μ N (blk m T) (X i)) := by
    funext X; exact coordVec_fld hm hN μ T X
  rw [e, ← Measure.map_map hsm hξi, Measure.pi_map_pi (fun i => hξm.aemeasurable)]

lemma lip_diff_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {Φ : E → ℝ} (hΦ : Φ ∈ CbUnitBall E 1) {X Y : Ω → E} (hX : Measurable X) (hY : Measurable Y)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : ∫⁻ ω, ‖X ω - Y ω‖ₑ ∂P ≤ ENNReal.ofReal τ) :
    |∫ ω, Φ (X ω) ∂P - ∫ ω, Φ (Y ω) ∂P| ≤ τ := by
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hb : ∀ z, |Φ z| ≤ 1 := fun z => abs_apply_le_of_mem hΦ z
  have hiX : Integrable (fun ω => Φ (X ω)) P :=
    Integrable.of_bound (hΦc.measurable.comp hX).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hb _)
  have hiY : Integrable (fun ω => Φ (Y ω)) P :=
    Integrable.of_bound (hΦc.measurable.comp hY).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hb _)
  have hmeas : AEStronglyMeasurable (fun ω => X ω - Y ω) P := (hX.sub hY).aestronglyMeasurable
  have hfin : Integrable (fun ω => ‖X ω - Y ω‖) P := by
    refine ⟨hmeas.norm, ?_⟩
    show ∫⁻ ω, ‖‖X ω - Y ω‖‖ₑ ∂P < ⊤
    simp only [enorm_norm]
    exact lt_of_le_of_lt hτ ENNReal.ofReal_lt_top
  rw [← integral_sub hiX hiY]
  have hn : ∫ ω, ‖X ω - Y ω‖ ∂P ≤ τ := by
    rw [integral_norm_eq_lintegral_enorm hmeas]
    exact ENNReal.toReal_le_of_le_ofReal hτ0 hτ
  calc |∫ ω, (Φ (X ω) - Φ (Y ω)) ∂P| ≤ ∫ ω, ‖Φ (X ω) - Φ (Y ω)‖ ∂P := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := P) (fun ω => Φ (X ω) - Φ (Y ω))
    _ ≤ ∫ ω, ‖X ω - Y ω‖ ∂P := integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hfin (Filter.Eventually.of_forall fun ω => norm_sub_le_of_mem_one hΦ _ _)
    _ ≤ τ := hn

lemma continuous_coordVec {m : ℝ} (T : Finset (NonzeroLattice d)) :
    Continuous (fun F : NegSobolev d m => coordVec T F) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => continuous_coord (kOf T j))

theorem fm_d2 {m : ℝ} (hm : (d : ℝ) < 2 * m) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {ρ : Measure (Torus d)} [IsProbabilityMeasure ρ]
    {γ : Measure (NegSobolev d m)} [IsProbabilityMeasure γ]
    (hγ : IsCenteredGaussianWithCov m γ (iidCov ρ)) (T : Finset (NonzeroLattice d)) {N : ℕ}
    (hN : 1 ≤ N) (Γ : Measure (EuclideanSpace ℝ (Fin T.card)))
    (hΓ : γ.map (coordVec T) = Γ) {J2 : ℝ}
    (hJ : ∀ Φ' : EuclideanSpace ℝ (Fin T.card) → ℝ, ContDiff ℝ 2 Φ' → (∀ z, |Φ' z| ≤ 1) →
      (∀ z, ‖fderiv ℝ Φ' z‖ ≤ 1) → (∀ z, ‖iteratedFDeriv ℝ 2 Φ' z‖ ≤ 1) →
      |∫ z, Φ' z ∂(cpow (μ.map (xiVec μ N (blk m T))) N) - ∫ z, Φ' z ∂Γ| ≤ J2) :
    smoothDist 2 ((Measure.pi fun _ : Fin N => μ).map (fld m N μ)) γ ≤
      J2 + 2 * Real.sqrt (tailR d m T) := by
  have := negSobolev_secondCountable d m
  set Pm : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hPm
  have hSm : Measurable (fld m N μ) := (continuous_fld hm hN μ).measurable
  have hJ0 : 0 ≤ J2 := by
    have := hJ 0 contDiff_const (by simp) (by simp) (by simp)
    simpa using this
  have hτ0 : 0 ≤ Real.sqrt (tailR d m T) := Real.sqrt_nonneg _
  have : Nonempty (CbUnitBall (NegSobolev d m) 2) := ⟨⟨0, zero_mem_cbUnitBall 2⟩⟩
  refine Real.iSup_le (fun Φ => ?_) (by positivity)
  have hΦ2 : Φ.1 ∈ CbUnitBall (NegSobolev d m) 2 := Φ.2
  have hΦ1 : Φ.1 ∈ CbUnitBall (NegSobolev d m) 1 := cbUnitBall_mono hΦ2
  have hΦc : Continuous Φ.1 := hΦ2.1.continuous
  rw [integral_map hSm.aemeasurable hΦc.aestronglyMeasurable]
  have hPS : Measurable (fun X => projT T (fld m N μ X)) := (continuous_projT T).measurable.comp hSm
  have hPF : Measurable (fun F : NegSobolev d m => projT T F) := (continuous_projT T).measurable
  have hcv : Measurable (fun F : NegSobolev d m => coordVec T F) := (continuous_coordVec T).measurable
  -- three pieces
  have h1 := lip_diff_le Pm hΦ1 hSm hPS hτ0 (tail_S hm hN μ T)
  have h3 := lip_diff_le γ hΦ1 hPF (measurable_id : Measurable (id : NegSobolev d m → _)) hτ0 (by
    have := tail_G hm hγ T
    refine le_trans (le_of_eq ?_) this
    refine lintegral_congr fun F => ?_
    simp only [id]
    exact _root_.enorm_sub_rev _ _)
  have h2 : |∫ X, Φ.1 (projT T (fld m N μ X)) ∂Pm - ∫ F, Φ.1 (projT T F) ∂γ| ≤ J2 := by
    obtain ⟨hcd, hb0, hb1, hb2⟩ := embed_comp_bounds T hΦ2
    have e1 : ∫ X, Φ.1 (projT T (fld m N μ X)) ∂Pm =
        ∫ z, (fun v => Φ.1 (embedT m T v)) z ∂(cpow (μ.map (xiVec μ N (blk m T))) N) := by
      rw [← law_coordVec_fld hm hN μ T,
        integral_map (φ := fun X => coordVec T (fld m N μ X)) (hcv.comp hSm).aemeasurable
          hcd.continuous.aestronglyMeasurable]
      refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      simp only [projT_eq_embedT]
    have e2 : ∫ F, Φ.1 (projT T F) ∂γ = ∫ z, (fun v => Φ.1 (embedT m T v)) z ∂Γ := by
      rw [← hΓ, integral_map hcv.aemeasurable hcd.continuous.aestronglyMeasurable]
      refine integral_congr_ae (Filter.Eventually.of_forall fun F => ?_)
      simp only [projT_eq_embedT]
    rw [e1, e2]
    exact hJ _ hcd hb0 hb1 hb2
  have e0 : ∫ F, Φ.1 F ∂γ = ∫ F, Φ.1 (id F) ∂γ := rfl
  calc |∫ X, Φ.1 (fld m N μ X) ∂Pm - ∫ F, Φ.1 F ∂γ|
      = |(∫ X, Φ.1 (fld m N μ X) ∂Pm - ∫ X, Φ.1 (projT T (fld m N μ X)) ∂Pm) +
          (∫ X, Φ.1 (projT T (fld m N μ X)) ∂Pm - ∫ F, Φ.1 (projT T F) ∂γ) +
          (∫ F, Φ.1 (projT T F) ∂γ - ∫ F, Φ.1 (id F) ∂γ)| := by
        simp only [id]; ring_nf
    _ ≤ |∫ X, Φ.1 (fld m N μ X) ∂Pm - ∫ X, Φ.1 (projT T (fld m N μ X)) ∂Pm| +
          |∫ X, Φ.1 (projT T (fld m N μ X)) ∂Pm - ∫ F, Φ.1 (projT T F) ∂γ| +
          |∫ F, Φ.1 (projT T F) ∂γ - ∫ F, Φ.1 (id F) ∂γ| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ Real.sqrt (tailR d m T) + J2 + Real.sqrt (tailR d m T) := add_le_add (add_le_add h1 h2) h3
    _ = J2 + 2 * Real.sqrt (tailR d m T) := by ring

theorem fm_coupling {m : ℝ} (hm : (d : ℝ) < 2 * m) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {ρ : Measure (Torus d)} [IsProbabilityMeasure ρ]
    {γ : Measure (NegSobolev d m)} [IsProbabilityMeasure γ]
    (hγ : IsCenteredGaussianWithCov m γ (iidCov ρ)) (T : Finset (NonzeroLattice d)) {N : ℕ}
    (hN : 1 ≤ N) (Γ : Measure (EuclideanSpace ℝ (Fin T.card)))
    (hΓ : γ.map (coordVec T) = Γ) {J : ℝ} (hJ0 : 0 ≤ J)
    (hJ : wassersteinE 1 (cpow (μ.map (xiVec μ N (blk m T))) N) Γ ≤ ENNReal.ofReal J)
    {η : ℝ} (hη : 0 < η) :
    ∃ P : Measure (Config d N × NegSobolev d m), IsProbabilityMeasure P ∧
      P.map Prod.fst = Measure.pi (fun _ : Fin N => μ) ∧ P.map Prod.snd = γ ∧
      ∫⁻ ω, ‖fld m N μ ω.1 - ω.2‖ₑ ∂P ≤
        ENNReal.ofReal (J + η + 2 * Real.sqrt (tailR d m T)) := by
  have := negSobolev_secondCountable d m
  have hSm : Measurable (fld m N μ) := (continuous_fld hm hN μ).measurable
  have hcv : Measurable (fun F : NegSobolev d m => coordVec T F) := (continuous_coordVec T).measurable
  have hT : Measurable (fun X : Config d N => coordVec T (fld m N μ X)) := hcv.comp hSm
  have hΓp : IsProbabilityMeasure Γ := by rw [← hΓ]; infer_instance
  obtain ⟨π, hπ, hπ1, hπ2, hcost⟩ := exists_coupling_of_w1 _ _ hJ0 hη hJ
  have := standardBorel_config d N
  have := standardBorel_negSobolev d m
  have : Nonempty (Config d N) := ⟨fun _ => 0⟩
  have : Nonempty (NegSobolev d m) := ⟨0⟩
  obtain ⟨P, hP, hP1, hP2, hP3⟩ := glue_two (Measure.pi fun _ : Fin N => μ) γ hT hcv π
    (by rw [hπ1, law_coordVec_fld hm hN μ T]) (by rw [hπ2, hΓ])
  refine ⟨P, hP, hP1, hP2, ?_⟩
  set τ := Real.sqrt (tailR d m T) with hτ
  have hτ0 : 0 ≤ τ := Real.sqrt_nonneg _
  have hpt : ∀ ω : Config d N × NegSobolev d m, ‖fld m N μ ω.1 - ω.2‖ₑ ≤
      ‖coordVec T (fld m N μ ω.1) - coordVec T ω.2‖ₑ +
        ‖fld m N μ ω.1 - projT T (fld m N μ ω.1)‖ₑ + ‖ω.2 - projT T ω.2‖ₑ := by
    intro ω
    have h := norm_sub_le_blocks T (fld m N μ ω.1) ω.2
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm]
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal h
  have hmeas1 : Measurable (fun ω : Config d N × NegSobolev d m =>
      ‖coordVec T (fld m N μ ω.1) - coordVec T ω.2‖ₑ) :=
    ((hT.comp measurable_fst).sub (hcv.comp measurable_snd)).enorm
  have hmeas2 : Measurable (fun ω : Config d N × NegSobolev d m =>
      ‖fld m N μ ω.1 - projT T (fld m N μ ω.1)‖ₑ) :=
    ((hSm.comp measurable_fst).sub (((continuous_projT T).measurable).comp (hSm.comp measurable_fst))).enorm
  have hmeas3 : Measurable (fun ω : Config d N × NegSobolev d m => ‖ω.2 - projT T ω.2‖ₑ) :=
    (measurable_snd.sub (((continuous_projT T).measurable).comp measurable_snd)).enorm
  have i1 : ∫⁻ ω, ‖coordVec T (fld m N μ ω.1) - coordVec T ω.2‖ₑ ∂P ≤ ENNReal.ofReal (J + η) := by
    have hf : Measurable (fun z : EuclideanSpace ℝ (Fin T.card) × EuclideanSpace ℝ (Fin T.card) =>
        ‖z.1 - z.2‖ₑ) := (measurable_fst.sub measurable_snd).enorm
    have hmm : Measurable (fun ω : Config d N × NegSobolev d m =>
        (coordVec T (fld m N μ ω.1), coordVec T ω.2)) :=
      (hT.comp measurable_fst).prodMk (hcv.comp measurable_snd)
    have : ∫⁻ ω, ‖coordVec T (fld m N μ ω.1) - coordVec T ω.2‖ₑ ∂P = ∫⁻ z, ‖z.1 - z.2‖ₑ ∂π := by
      rw [← hP3, lintegral_map hf hmm]
    rw [this]; exact hcost
  have i2 : ∫⁻ ω, ‖fld m N μ ω.1 - projT T (fld m N μ ω.1)‖ₑ ∂P ≤ ENNReal.ofReal τ := by
    have hg : Measurable (fun X : Config d N => ‖fld m N μ X - projT T (fld m N μ X)‖ₑ) :=
      (hSm.sub (((continuous_projT T).measurable).comp hSm)).enorm
    have : ∫⁻ ω, ‖fld m N μ ω.1 - projT T (fld m N μ ω.1)‖ₑ ∂P =
        ∫⁻ X, ‖fld m N μ X - projT T (fld m N μ X)‖ₑ ∂(Measure.pi fun _ : Fin N => μ) := by
      rw [← hP1, lintegral_map hg measurable_fst]
    rw [this]; exact tail_S hm hN μ T
  have i3 : ∫⁻ ω, ‖ω.2 - projT T ω.2‖ₑ ∂P ≤ ENNReal.ofReal τ := by
    have hg : Measurable (fun F : NegSobolev d m => ‖F - projT T F‖ₑ) :=
      (measurable_id.sub ((continuous_projT T).measurable)).enorm
    have : ∫⁻ ω, ‖ω.2 - projT T ω.2‖ₑ ∂P = ∫⁻ F, ‖F - projT T F‖ₑ ∂γ := by
      rw [← hP2, lintegral_map hg measurable_snd]
    rw [this]; exact tail_G hm hγ T
  calc ∫⁻ ω, ‖fld m N μ ω.1 - ω.2‖ₑ ∂P
      ≤ ∫⁻ ω, (‖coordVec T (fld m N μ ω.1) - coordVec T ω.2‖ₑ +
        ‖fld m N μ ω.1 - projT T (fld m N μ ω.1)‖ₑ + ‖ω.2 - projT T ω.2‖ₑ) ∂P :=
        lintegral_mono hpt
    _ = ∫⁻ ω, ‖coordVec T (fld m N μ ω.1) - coordVec T ω.2‖ₑ ∂P +
        ∫⁻ ω, ‖fld m N μ ω.1 - projT T (fld m N μ ω.1)‖ₑ ∂P + ∫⁻ ω, ‖ω.2 - projT T ω.2‖ₑ ∂P := by
        rw [lintegral_add_left (f := fun ω : Config d N × NegSobolev d m =>
            ‖coordVec T (fld m N μ ω.1) - coordVec T ω.2‖ₑ +
              ‖fld m N μ ω.1 - projT T (fld m N μ ω.1)‖ₑ) (hmeas1.add hmeas2),
          lintegral_add_left (f := fun ω : Config d N × NegSobolev d m =>
            ‖coordVec T (fld m N μ ω.1) - coordVec T ω.2‖ₑ) hmeas1]
    _ ≤ ENNReal.ofReal (J + η) + ENNReal.ofReal τ + ENNReal.ofReal τ := by gcongr
    _ = ENNReal.ofReal (J + η + 2 * τ) := by
        rw [← ENNReal.ofReal_add (by linarith) hτ0, ← ENNReal.ofReal_add (by linarith) hτ0]
        congr 1; ring

end FM

end HRS.IID
