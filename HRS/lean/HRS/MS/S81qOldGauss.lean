import HRS.MS.S81qItoTD
import HRS.MS.S81pAssemble
import HRS.MS.SpecAux66
import HRS.MS.WsInitGAux10

/-!
# S8.1 (worker S81Q): the Gaussian old block `Y_G(h) = ∫_0^h e^{-(h-r)Ω} Sb_r dB_r`

Namespace `HRS.Whole.S81Q`, prefix `s81q_`.

On any probability space carrying a cylindrical Brownian motion `B` indexed by a Hilbert basis `eb` of `ℓ²`, the deterministic diagonal operator family
`Sb''_r = diag(√d_l e^{-(h-r)ω_l} 1_{[0,h]}(r))`, `d_l = 2β⁻¹ ω_l e^{-τω_l}`, satisfies `PCDetData` (through `pc_detData`), hence the Hilbert integral
`G = ∫ Sb'' dB` (`pc_exists_G`) has at time `h` a centered Gaussian law on `ℓ²` with covariance `∑_l β⁻¹ e^{-τω_l}(1 - e^{-2hω_l}) x_l y_l`, is independent
of the initial σ-field (`pc_G_gaussian`), and its coordinates are the scalar Itô integrals of `√d_l e^{-(h-r)ω_l}⟨eb_j, b_l⟩`.  The operators are written
through the coordinatewise multiplier `s81q_diag`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
open HRS HRS.Whole HRS.MS.SuppU11 HRS.MS.Spec

namespace HRS.Whole.S81Q

section Diag

/-- Coordinatewise multiplication `z ↦ (c_l z_l)_l` (junk `0` if not square summable, which never happens for bounded `c`). -/
def s81q_mulSeq (c : ℕ → ℝ) (z : SeqL2) : SeqL2 := SeqL2.ofSeq fun l => c l * SeqL2.coord z l

theorem s81q_mulSeq_mem {c : ℕ → ℝ} {K : ℝ} (hK : ∀ l, |c l| ≤ K) (z : SeqL2) :
    Memℓp (fun l => c l * SeqL2.coord z l) 2 := by
  refine memℓp_two_iff.2 (Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => ?_)
    ((u11_coord_summable z).mul_left (K ^ 2)))
  rw [mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact sq_le_sq' (abs_le.1 (hK l)).1 (abs_le.1 (hK l)).2

theorem s81q_coord_mulSeq {c : ℕ → ℝ} {K : ℝ} (hK : ∀ l, |c l| ≤ K) (z : SeqL2) (l : ℕ) :
    SeqL2.coord (s81q_mulSeq c z) l = c l * SeqL2.coord z l :=
  u11_coord_ofSeq (s81q_mulSeq_mem hK z) l

theorem s81q_seqL2_ext {z z' : SeqL2} (h : ∀ l, SeqL2.coord z l = SeqL2.coord z' l) : z = z' := by
  have : (show lp (fun _ : ℕ => ℝ) 2 from z) = (show lp (fun _ : ℕ => ℝ) 2 from z') :=
    lp.ext (funext h)
  exact this

theorem s81q_norm_mulSeq_le {c : ℕ → ℝ} {K : ℝ} (hK : ∀ l, |c l| ≤ K) (z : SeqL2) :
    ‖s81q_mulSeq c z‖ ≤ |K| * ‖z‖ := by
  have h2 : ‖s81q_mulSeq c z‖ ^ 2 ≤ (|K| * ‖z‖) ^ 2 := by
    rw [← u11_norm_sq, mul_pow, ← u11_norm_sq, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun l => ?_) ?_ ((u11_coord_summable z).mul_left _)
    · rw [s81q_coord_mulSeq hK, mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [sq_abs]
      exact sq_le_sq' (abs_le.1 (hK l)).1 (abs_le.1 (hK l)).2
    · exact u11_coord_summable _
  exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2

/-- The bounded diagonal operator with multiplier `c`. -/
def s81q_diag (c : ℕ → ℝ) (K : ℝ) (hK : ∀ l, |c l| ≤ K) : SeqL2 →L[ℝ] SeqL2 :=
  LinearMap.mkContinuous
    { toFun := s81q_mulSeq c
      map_add' := fun z z' => s81q_seqL2_ext fun l => by
        rw [s81q_coord_mulSeq hK, s8p_coord_add, s8p_coord_add, s81q_coord_mulSeq hK,
          s81q_coord_mulSeq hK]; ring
      map_smul' := fun a z => s81q_seqL2_ext fun l => by
        rw [s81q_coord_mulSeq hK, s8p_coord_smul]
        simp only [RingHom.id_apply]
        rw [s8p_coord_smul, s81q_coord_mulSeq hK]; ring }
    |K| (fun z => s81q_norm_mulSeq_le hK z)

theorem s81q_diag_coord {c : ℕ → ℝ} {K : ℝ} (hK : ∀ l, |c l| ≤ K) (z : SeqL2) (l : ℕ) :
    SeqL2.coord (s81q_diag c K hK z) l = c l * SeqL2.coord z l :=
  s81q_coord_mulSeq hK z l

theorem s81q_inner_eq (x y : SeqL2) :
    inner ℝ x y = ∑' l, SeqL2.coord x l * SeqL2.coord y l := by
  have h := lp.inner_eq_tsum (𝕜 := ℝ) (G := fun _ : ℕ => ℝ)
    (show lp (fun _ : ℕ => ℝ) 2 from x) (show lp (fun _ : ℕ => ℝ) 2 from y)
  refine h.trans (tsum_congr fun l => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  exact mul_comm _ _

theorem s81q_diag_inner {c : ℕ → ℝ} {K : ℝ} (hK : ∀ l, |c l| ≤ K) (x y : SeqL2) :
    inner ℝ (s81q_diag c K hK x) y = ∑' l, c l * SeqL2.coord x l * SeqL2.coord y l := by
  rw [s81q_inner_eq]
  exact tsum_congr fun l => by rw [s81q_diag_coord hK]

end Diag

section Old

variable {β τ : ℝ} {om : ℕ → ℝ}

/-- The multiplier `√d_l e^{-(h-r)ω_l} 1_{[0,h]}(r)` of the deterministic diagonal root. -/
def s81q_cOld (β τ h : ℝ) (om : ℕ → ℝ) (l : ℕ) (r : ℝ) : ℝ :=
  if r ∈ Set.Icc 0 h then Real.sqrt (s8p_dv β om τ l) * Real.exp (-(h - r) * om l) else 0

theorem s81q_cOld_nonneg (β τ h : ℝ) (om : ℕ → ℝ) (l : ℕ) (r : ℝ) : 0 ≤ s81q_cOld β τ h om l r := by
  unfold s81q_cOld
  split_ifs
  · exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  · exact le_rfl

theorem s81q_cOld_sq (hβ : 0 < β) (hom : ∀ l, 0 < om l) (h : ℝ) (l : ℕ) (r : ℝ) :
    s81q_cOld β τ h om l r ^ 2 =
      if r ∈ Set.Icc 0 h then s8p_dv β om τ l * Real.exp (-2 * (h - r) * om l) else 0 := by
  unfold s81q_cOld
  split_ifs
  · rw [mul_pow, Real.sq_sqrt (s8p_dv_nonneg hβ hom τ l), ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  · simp

theorem s81q_cOld_abs_le (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ) (h : ℝ) (l : ℕ) (r : ℝ) :
    |s81q_cOld β τ h om l r| ≤ Real.sqrt (4 / (β * τ)) := by
  rw [abs_of_nonneg (s81q_cOld_nonneg β τ h om l r)]
  unfold s81q_cOld
  split_ifs with hr
  · have h1 : Real.exp (-(h - r) * om l) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := hom l
      nlinarith [hr.2]
    calc Real.sqrt (s8p_dv β om τ l) * Real.exp (-(h - r) * om l) ≤ Real.sqrt (s8p_dv β om τ l) * 1 :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (4 / (β * τ)) := by
          rw [mul_one]
          exact Real.sqrt_le_sqrt (s8p_dv_le hβ hom hτ l)
  · exact Real.sqrt_nonneg _

/-- The deterministic diagonal root family. -/
def s81q_SbOld (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ) (h : ℝ) (r : ℝ) : SeqL2 →L[ℝ] SeqL2 :=
  s81q_diag (fun l => s81q_cOld β τ h om l r) (Real.sqrt (4 / (β * τ)))
    (fun l => s81q_cOld_abs_le hβ hom hτ h l r)

theorem s81q_SbOld_coord (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ) (h r : ℝ) (z : SeqL2)
    (l : ℕ) : SeqL2.coord (s81q_SbOld hβ hom hτ h r z) l = s81q_cOld β τ h om l r * SeqL2.coord z l :=
  s81q_diag_coord _ z l

theorem s81q_SbOld_basis (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ) (h r : ℝ) (i : ℕ) :
    s81q_SbOld hβ hom hτ h r (S45.s45_seqBasis i) = s81q_cOld β τ h om i r • S45.s45_seqBasis i := by
  refine s81q_seqL2_ext fun l => ?_
  rw [s81q_SbOld_coord, s8p_coord_smul, s8p_coord_basis]
  by_cases hl : l = i
  · subst hl; simp
  · simp [hl]

theorem s81q_SbOld_opMeas (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ) (h : ℝ) :
    OpMeas (s81q_SbOld hβ hom hτ h) := by
  intro x
  refine measurable_of_inner_basis S45.s45_seqBasis fun i => ?_
  have e : (fun r => inner ℝ (S45.s45_seqBasis i) (s81q_SbOld hβ hom hτ h r x)) =
      fun r => (if r ∈ Set.Icc 0 h then Real.sqrt (s8p_dv β om τ i) * Real.exp (-(h - r) * om i)
        else 0) * SeqL2.coord x i := by
    funext r
    rw [S45.s45_inner_seqBasis, s81q_SbOld_coord]
    rfl
  rw [e]
  exact (Measurable.ite measurableSet_Icc (measurable_const.mul
    (Real.measurable_exp.comp (by fun_prop))) measurable_const).mul measurable_const

theorem s81q_SbOld_zero (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ) (h r : ℝ)
    (hr : r ∉ Set.Icc 0 h) : s81q_SbOld hβ hom hτ h r = 0 := by
  refine ContinuousLinearMap.ext fun z => s81q_seqL2_ext fun l => ?_
  rw [s81q_SbOld_coord]
  have h0 : SeqL2.coord (0 : SeqL2) l = 0 := rfl
  simp [s81q_cOld, hr, h0]

/-- The covariance form of the deterministic root. -/
def s81q_sbOld (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ) (h r : ℝ) :
    SeqL2 →L[ℝ] SeqL2 →L[ℝ] ℝ :=
  (innerSL ℝ : SeqL2 →L[ℝ] SeqL2 →L[ℝ] ℝ).bilinearComp (s81q_SbOld hβ hom hτ h r)
    (s81q_SbOld hβ hom hτ h r)

theorem s81q_sbOld_apply (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ) (h r : ℝ) (x y : SeqL2) :
    s81q_sbOld hβ hom hτ h r x y = ∑' l, s81q_cOld β τ h om l r ^ 2 * SeqL2.coord x l * SeqL2.coord y l := by
  unfold s81q_sbOld
  simp only [ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]
  rw [s81q_inner_eq]
  refine tsum_congr fun l => ?_
  rw [s81q_SbOld_coord, s81q_SbOld_coord]; ring

theorem s81q_cOld_sq_le (hβ : 0 < β) (hom : ∀ l, 0 < om l) (h : ℝ) (hh : 0 ≤ h) (l : ℕ) (r : ℝ) :
    s81q_cOld β τ h om l r ^ 2 ≤ s8p_dv β om τ l := by
  rw [s81q_cOld_sq hβ hom]
  split_ifs with hr
  · have h1 : Real.exp (-2 * (h - r) * om l) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := hom l
      nlinarith [hr.2]
    have := s8p_dv_nonneg hβ hom τ l
    nlinarith
  · exact s8p_dv_nonneg hβ hom τ l

theorem s81q_sbOld_basis (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ) (h r : ℝ) (i : ℕ) :
    s81q_sbOld hβ hom hτ h r (S45.s45_seqBasis i) (S45.s45_seqBasis i) =
      s81q_cOld β τ h om i r ^ 2 := by
  unfold s81q_sbOld
  simp only [ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]
  rw [s81q_SbOld_basis, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
  have h1 : ‖S45.s45_seqBasis i‖ = 1 := (S45.s45_seqBasis.orthonormal.1 i)
  simp [h1, sq]

theorem s81q_sbOld_isTraceClass (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ)
    (hsum : Summable (s8p_dv β om τ)) (h : ℝ) (hh : 0 ≤ h) (r : ℝ) :
    IsTraceClassCov (s81q_sbOld hβ hom hτ h r) where
  symm := fun x y => by
    unfold s81q_sbOld
    simp only [ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]
    exact real_inner_comm _ _
  nonneg := fun x => by
    unfold s81q_sbOld
    simp only [ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]
    exact real_inner_self_nonneg
  trace := ⟨ℕ, S45.s45_seqBasis, by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hsum
    · rw [s81q_sbOld_basis]; exact sq_nonneg _
    · rw [s81q_sbOld_basis]; exact s81q_cOld_sq_le hβ hom h hh i r⟩

theorem s81q_sbOld_detCov (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ)
    (hsum : Summable (s8p_dv β om τ)) (h : ℝ) (hh : 0 ≤ h) :
    IsDetCovDensity h (s81q_sbOld hβ hom hτ h) := by
  have hmeas : ∀ x y : SeqL2, Measurable fun r => s81q_sbOld hβ hom hτ h r x y := by
    intro x y
    unfold s81q_sbOld
    simp only [ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]
    exact (s81q_SbOld_opMeas hβ hom hτ h x).inner (s81q_SbOld_opMeas hβ hom hτ h y)
  refine ⟨hmeas, fun r _ => s81q_sbOld_isTraceClass hβ hom hτ hsum h hh r, ?_⟩
  have hm : Measurable fun r => traceNormForm (s81q_sbOld hβ hom hτ h r) :=
    measurable_traceNormForm (s81q_sbOld hβ hom hτ h) hmeas
  refine Measure.integrableOn_of_bounded (M := ∑' l, s8p_dv β om τ l) (by simp)
    hm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => ?_)
  rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
  refine (traceNormForm_le_basis_trace (s81q_sbOld_isTraceClass hβ hom hτ hsum h hh r)
    S45.s45_seqBasis).trans ?_
  refine Summable.tsum_le_tsum (fun i => ?_) ?_ hsum
  · rw [s81q_sbOld_basis]; exact s81q_cOld_sq_le hβ hom h hh i r
  · refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hsum
    · rw [s81q_sbOld_basis]; exact sq_nonneg _
    · rw [s81q_sbOld_basis]; exact s81q_cOld_sq_le hβ hom h hh i r

theorem s81q_SbOld_sqrt (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ) (h r : ℝ) :
    IsSqrtOfForm (s81q_SbOld hβ hom hτ h r) (s81q_sbOld hβ hom hτ h r) where
  symm := fun x y => by
    have h1 := s81q_diag_inner (fun l => s81q_cOld_abs_le hβ hom hτ h l r) x y
    have h2 := s81q_diag_inner (fun l => s81q_cOld_abs_le hβ hom hτ h l r) y x
    show inner ℝ (s81q_diag _ _ _ x) y = inner ℝ x (s81q_diag _ _ _ y)
    rw [h1, ← real_inner_comm x, h2]
    exact tsum_congr fun l => by ring
  nonneg := fun x => by
    have h1 := s81q_diag_inner (fun l => s81q_cOld_abs_le hβ hom hτ h l r) x x
    show 0 ≤ inner ℝ (s81q_diag _ _ _ x) x
    rw [h1]
    refine tsum_nonneg fun l => ?_
    have := s81q_cOld_nonneg β τ h om l r
    nlinarith [sq_nonneg (SeqL2.coord x l)]
  sq := fun x y => rfl

/-- The variance of the `l`-th coordinate of `Y_G(h)`. -/
def s81q_sOld (β τ h : ℝ) (om : ℕ → ℝ) (l : ℕ) : ℝ :=
  β⁻¹ * Real.exp (-τ * om l) * (1 - Real.exp (-2 * h * om l))

theorem s81q_cOld_int (hβ : 0 < β) (hom : ∀ l, 0 < om l) (h : ℝ) (hh : 0 ≤ h) (l : ℕ) :
    ∫ r in Set.Icc 0 h, s81q_cOld β τ h om l r ^ 2 = s81q_sOld β τ h om l := by
  have hw := hom l
  have e1 : ∫ r in Set.Icc 0 h, s81q_cOld β τ h om l r ^ 2 =
      ∫ r in Set.Icc 0 h, s8p_dv β om τ l * Real.exp (-2 * (h - r) * om l) := by
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    simp only [s81q_cOld_sq hβ hom, hr, if_true]
  rw [e1, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hh,
    intervalIntegral.integral_const_mul]
  have e2 : ∫ r in (0 : ℝ)..h, Real.exp (-2 * (h - r) * om l) =
      (1 - Real.exp (-2 * h * om l)) / (2 * om l) := by
    have : ∫ r in (0 : ℝ)..h, Real.exp (-2 * (h - r) * om l) =
        ∫ r in (0 : ℝ)..h, Real.exp ((-2 * om l) * (h - r)) := by
      refine intervalIntegral.integral_congr fun r _ => ?_
      show Real.exp (-2 * (h - r) * om l) = Real.exp ((-2 * om l) * (h - r))
      congr 1; ring
    rw [this, intervalIntegral.integral_comp_sub_left (fun u => Real.exp ((-2 * om l) * u)) h,
      intervalIntegral.integral_comp_mul_left (fun u => Real.exp u) (by linarith : (-2 * om l) ≠ 0),
      integral_exp]
    simp only [sub_self, sub_zero, mul_zero, Real.exp_zero, smul_eq_mul]
    field_simp
    ring_nf
  rw [e2]
  unfold s81q_sOld s8p_dv
  field_simp

/-- The covariance of the Gaussian old block. -/
theorem s81q_sbOld_integral (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ)
    (hsum : Summable (s8p_dv β om τ)) (h : ℝ) (hh : 0 ≤ h) (x y : SeqL2) :
    ∫ r in Set.Icc 0 h, s81q_sbOld hβ hom hτ h r x y =
      ∑' l, s81q_sOld β τ h om l * SeqL2.coord x l * SeqL2.coord y l := by
  simp_rw [s81q_sbOld_apply hβ hom hτ]
  set F : ℕ → ℝ → ℝ := fun l r => s81q_cOld β τ h om l r ^ 2 * SeqL2.coord x l * SeqL2.coord y l with hF
  have hFm : ∀ l, Measurable (F l) := fun l => by
    have : Measurable fun r => s81q_cOld β τ h om l r := by
      unfold s81q_cOld
      exact Measurable.ite measurableSet_Icc (measurable_const.mul
        (Real.measurable_exp.comp (by fun_prop))) measurable_const
    exact ((this.pow_const 2).mul_const _).mul_const _
  have hFb : ∀ l, ∀ r, |F l r| ≤ s8p_dv β om τ l * (|SeqL2.coord x l| * |SeqL2.coord y l|) := by
    intro l r
    simp only [hF, abs_mul]
    have h1 : |s81q_cOld β τ h om l r ^ 2| ≤ s8p_dv β om τ l := by
      rw [abs_of_nonneg (sq_nonneg _)]; exact s81q_cOld_sq_le hβ hom h hh l r
    calc |s81q_cOld β τ h om l r ^ 2| * |SeqL2.coord x l| * |SeqL2.coord y l|
        = |s81q_cOld β τ h om l r ^ 2| * (|SeqL2.coord x l| * |SeqL2.coord y l|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)
  have hint : ∀ l, Integrable (F l) (volume.restrict (Set.Icc 0 h)) := fun l =>
    Measure.integrableOn_of_bounded (M := s8p_dv β om τ l * (|SeqL2.coord x l| * |SeqL2.coord y l|))
      (by simp) (hFm l).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r _ => by
        rw [Real.norm_eq_abs]; exact hFb l r))
  have hcs : Summable fun l => |SeqL2.coord x l| * |SeqL2.coord y l| := by
    have := (s8p_series_cs _ _ (u11_coord_summable x) (u11_coord_summable y)).1
    exact this.abs.congr fun l => by rw [abs_mul]
  have hD : ∃ M, ∀ l, s8p_dv β om τ l ≤ M := ⟨4 / (β * τ), fun l => s8p_dv_le hβ hom hτ l⟩
  obtain ⟨M, hM⟩ := hD
  have hsumI : Summable fun l => ∫ r, ‖F l r‖ ∂(volume.restrict (Set.Icc 0 h)) := by
    refine Summable.of_nonneg_of_le (fun l => integral_nonneg fun r => norm_nonneg _) (fun l => ?_)
      (hcs.mul_left (M * h))
    calc ∫ r, ‖F l r‖ ∂(volume.restrict (Set.Icc 0 h)) ≤
        ∫ r, s8p_dv β om τ l * (|SeqL2.coord x l| * |SeqL2.coord y l|) ∂(volume.restrict (Set.Icc 0 h)) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun r => norm_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall fun r => ?_)
          show ‖F l r‖ ≤ _
          rw [Real.norm_eq_abs]; exact hFb l r
      _ = s8p_dv β om τ l * (|SeqL2.coord x l| * |SeqL2.coord y l|) * h := by
          rw [setIntegral_const]; simp [Real.volume_Icc, hh]; ring
      _ ≤ M * h * (|SeqL2.coord x l| * |SeqL2.coord y l|) := by
          have := hM l
          have h0 : 0 ≤ |SeqL2.coord x l| * |SeqL2.coord y l| := by positivity
          nlinarith [mul_nonneg h0 hh, mul_nonneg (sub_nonneg.2 this) (mul_nonneg h0 hh)]
  rw [← integral_tsum_of_summable_integral_norm hint hsumI]
  refine tsum_congr fun l => ?_
  have e : ∫ r in Set.Icc 0 h, F l r = (∫ r in Set.Icc 0 h, s81q_cOld β τ h om l r ^ 2) *
      SeqL2.coord x l * SeqL2.coord y l := by
    simp only [hF]
    rw [integral_mul_const, integral_mul_const]
  rw [e, s81q_cOld_int hβ hom h hh]

/-- **The Gaussian old block.**  For a cylindrical Brownian motion `B` indexed by a Hilbert basis `eb` of `ℓ²` there is an `ℓ²`-valued process `G`
(the Hilbert Itô integral of `Sb''`) whose value at time `h` is a centered Gaussian vector with the covariance `∑_l s_l x_l y_l`, independent of
the initial σ-field `ℱ' 0`, and whose coordinates are the scalar Itô integrals of the deterministic integrands `√d_l e^{-(h-r)ω_l} ⟨eb_j, b_l⟩`. -/
theorem s81q_old_gaussian (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ)
    (hsum : Summable (s8p_dv β om τ)) (h : ℝ) (hh : 0 ≤ h) {Ω' : Type} {mΩ' : MeasurableSpace Ω'}
    (P' : Measure Ω') [IsProbabilityMeasure P'] (ℱ' : Filtration ℝ mΩ') {ι : Type} [Countable ι]
    (eb : HilbertBasis ι ℝ SeqL2) {B : ℝ≥0 → Ω' → ι → ℝ} (hB : IsCylindricalBrownian P' ℱ' B) :
    ∃ G : ℝ → Ω' → SeqL2, Measurable[ℱ' h] (G h) ∧ IsCenteredGaussian (law P' (G h)) ∧
      (∀ x y, covarianceBilin (law P' (G h)) x y =
        ∑' l, s81q_sOld β τ h om l * SeqL2.coord x l * SeqL2.coord y l) ∧
      Indep (ℱ' 0) (MeasurableSpace.comap (G h) inferInstance) P' ∧
      ∀ l : ℕ, IsCtbl P' ℱ' (fun r (_ : Ω') (j : ι) =>
          if r ≤ h then s81q_cOld β τ h om l r * inner ℝ (eb j) (S45.s45_seqBasis l) else 0) ∧
        ∃ J : ℝ → Ω' → ℝ, IsItoC P' ℱ' B (fun r (_ : Ω') (j : ι) =>
          if r ≤ h then s81q_cOld β τ h om l r * inner ℝ (eb j) (S45.s45_seqBasis l) else 0) J ∧
        (fun ω => SeqL2.coord (G h ω) l) =ᵐ[P'] J h := by
  obtain ⟨T, hD⟩ := pc_detData eb h (s81q_sbOld hβ hom hτ h) (s81q_sbOld_detCov hβ hom hτ hsum h hh)
    (s81q_SbOld_opMeas hβ hom hτ h) (fun r hr => s81q_SbOld_zero hβ hom hτ h r hr)
    (fun r _ => s81q_SbOld_sqrt hβ hom hτ h r)
  obtain ⟨G, hGI, hGJ⟩ := pc_exists_G hD hB
  have hGad : Measurable[ℱ' h] (G h) := hGI.adapted h
  have hGm : Measurable (G h) := hGad.mono (ℱ'.le h) le_rfl
  have hGauss := pc_G_gaussian hD hB hGJ hh hGm ⟨ℱ' 0, le_rfl⟩
  refine ⟨G, hGad, hGauss.2.1, fun x y => ?_, hGauss.1, fun l => ?_⟩
  · rw [hGauss.2.2 x y, ← s81q_sbOld_integral hβ hom hτ hsum h hh x y]
    rfl
  · obtain ⟨J, hJ, hGae⟩ := hGJ (S45.s45_seqBasis l)
    have e : fSb eb h (s81q_SbOld hβ hom hτ h) (S45.s45_seqBasis l) =
        fun r (_ : Ω') (j : ι) =>
          if r ≤ h then s81q_cOld β τ h om l r * inner ℝ (eb j) (S45.s45_seqBasis l) else 0 := by
      funext r ω j
      unfold fSb
      by_cases hr : r ≤ h
      · simp only [hr, if_true]
        rw [s8p_inner_basis, s81q_SbOld_coord, s8p_inner_basis]
      · simp [hr]
    refine ⟨e ▸ hD.ctbl (S45.s45_seqBasis l), J, e ▸ hJ, ?_⟩
    filter_upwards [hGae h hh] with ω hω
    rw [← hω, s8p_inner_basis]

end Old

section Fdd

/-- A centered Gaussian `ℓ²`-vector `Y` with covariance `∑ s_l x_l y_l` has Gaussian laws for any finite family of continuous linear
functionals, with covariance matrix `∑_l s_l L_i(b_l) L_j(b_l)`. -/
theorem s81q_fdd_of_gaussian {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → SeqL2} (hY : Measurable Y) (hG : IsCenteredGaussian (law P Y)) (s : ℕ → ℝ)
    (hcov : ∀ x y, covarianceBilin (law P Y) x y =
      ∑' l, s l * SeqL2.coord x l * SeqL2.coord y l) {p : ℕ} (L : Fin p → SeqL2 →L[ℝ] ℝ) :
    P.map (fun ω => (WithLp.toLp 2 fun i => L i (Y ω) : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun i j =>
        ∑' l, s l * L i (S45.s45_seqBasis l) * L j (S45.s45_seqBasis l)) := by
  haveI hGg : IsGaussian (law P Y) := hG.1
  haveI : IsProbabilityMeasure (law P Y) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
  have hmean : ∫ x, id x ∂(law P Y) = 0 := HRS.HilbertCLTAux.gaussian_mean_zero hG
  set w : Fin p → SeqL2 := fun i => (InnerProductSpace.toDual ℝ SeqL2).symm (L i) with hw
  have hLw : ∀ i z, L i z = inner ℝ (w i) z := fun i z => by
    rw [hw]; exact (InnerProductSpace.toDual_symm_apply (x := z) (y := L i)).symm
  have hcw : ∀ i l, SeqL2.coord (w i) l = L i (S45.s45_seqBasis l) := fun i l => by
    rw [hLw, ← s8p_inner_basis l (w i), real_inner_comm]
  obtain ⟨-, hlaw⟩ := HRS.MS.S21.s21g_fdd_gaussian (law P Y) hmean w
  have e1 : (fun ω => (WithLp.toLp 2 fun i => L i (Y ω) : EuclideanSpace ℝ (Fin p))) =
      fun ω => HRS.MS.S21.s21gAw w (Y ω) := by
    funext ω
    ext i
    simp [HRS.MS.S21.s21gAw_apply, hLw]
  rw [e1]
  have e2 : P.map (fun ω => HRS.MS.S21.s21gAw w (Y ω)) = (law P Y).map (HRS.MS.S21.s21gAw w) := by
    rw [Measure.map_map (HRS.MS.S21.s21gAw w).continuous.measurable hY]; rfl
  rw [e2, hlaw]
  congr 2
  ext i j
  rw [hcov]
  exact tsum_congr fun l => by rw [hcw i l, hcw j l]

end Fdd

end HRS.Whole.S81Q
