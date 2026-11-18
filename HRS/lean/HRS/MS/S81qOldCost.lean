import HRS.MS.S81qOldGauss
import HRS.MS.SpecAux66
import HRS.Uniform.Q07cAux5

/-!
# S8.1 (worker S81Q): the old-current coupling cost in coordinates

Namespace `HRS.Whole.S81Q`, prefix `s81q_`.

Let `Sx_r(ω)` be the polar root of the spectral empirical covariance, `Sb` the deterministic diagonal root, `Z` a uniform bound of
`E ∑_j ‖(Sx_r - Sb_r) e_j‖²`.  With the clamped weights `f_l(r) = e^{-(h - min(r,h)) ω_l}`, the weighted coordinate Itô integrals
`J_l = ∫ f_l ⟨Sx e_j, b_l⟩ dB^j` of the killed integrand and the coordinates of the Gaussian old block `G(h)` (`s81q_old_gaussian`) satisfy
`E ∑_l |J_l(h) - G_l(h)|² ≤ Z / (2 ω_0)` (`s81q_old_cost`), without any Hilbert-valued stochastic integral with random integrand.
-/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
open HRS HRS.Whole HRS.MS.SuppU11 HRS.MS.Spec

namespace HRS.Whole.S81Q

section Weights

/-- The clamped bounded continuous weight `r ↦ e^{-(h - min(r,h)) ω_l}`. -/
def s81q_fcl (om : ℕ → ℝ) (h : ℝ) (l : ℕ) (r : ℝ) : ℝ := Real.exp (-(h - min r h) * om l)

theorem s81q_fcl_cont (om : ℕ → ℝ) (h : ℝ) (l : ℕ) : Continuous (s81q_fcl om h l) := by
  unfold s81q_fcl; fun_prop

theorem s81q_fcl_le_one {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) (h : ℝ) (l : ℕ) (r : ℝ) :
    s81q_fcl om h l r ≤ 1 := by
  unfold s81q_fcl
  rw [Real.exp_le_one_iff]
  have := hom l
  have : 0 ≤ h - min r h := sub_nonneg.2 (min_le_right _ _)
  nlinarith

theorem s81q_fcl_abs_le {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) (h : ℝ) (l : ℕ) (r : ℝ) :
    |s81q_fcl om h l r| ≤ 1 := by
  rw [abs_of_pos (by unfold s81q_fcl; exact Real.exp_pos _)]; exact s81q_fcl_le_one hom h l r

theorem s81q_fcl_sq_le {om : ℕ → ℝ} (hmono : Monotone om) (h : ℝ) (l : ℕ)
    {r : ℝ} (hr : r ∈ Set.Icc 0 h) :
    s81q_fcl om h l r ^ 2 ≤ Real.exp (-(2 * (h - r) * om 0)) := by
  unfold s81q_fcl
  rw [min_eq_left hr.2, ← Real.exp_nat_mul]
  rw [Real.exp_le_exp]
  have h1 := hmono (Nat.zero_le l)
  have h2 : 0 ≤ h - r := sub_nonneg.2 hr.2
  push_cast
  nlinarith

end Weights

section Master

variable {Ω' : Type} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ℱ' : Filtration ℝ mΩ'} {ι : Type} [Countable ι]

/-- The master estimate (the coordinate form of `s8p_conv_bound`): the weighted square sum is controlled by `Z / (2 ω_0)`. -/
theorem s81q_master {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) (hmono : Monotone om) {h : ℝ} (hh : 0 ≤ h)
    (v : ℝ → Ω' → ι → SeqL2) (hv : ∀ j l, IsProgressive ℱ' (fun r ω => SeqL2.coord (v r ω j) l))
    {Z : ℝ≥0∞} (hZ : Z ≠ ⊤)
    (hb : ∀ r ∈ Set.Icc 0 h, ∫⁻ ω, ∑' j, ‖v r ω j‖ₑ ^ 2 ∂P' ≤ Z) :
    ∫⁻ ω, (∫⁻ r in Set.Icc 0 h, ∑' j, ∑' l,
      ENNReal.ofReal (s81q_fcl om h l r ^ 2 * SeqL2.coord (v r ω j) l ^ 2)) ∂P' ≤
        Z * ENNReal.ofReal (1 / (2 * om 0)) := by
  set Zf : ℝ → Ω' → ℝ≥0∞ := fun r ω => ∑' j, ‖v r ω j‖ₑ ^ 2 with hZf
  set K : ℝ → ℝ≥0∞ := Set.indicator (Set.Icc 0 h)
    (fun r => ENNReal.ofReal (Real.exp (-(2 * (h - r) * om 0)))) with hK
  have hKm : Measurable K := (ENNReal.measurable_ofReal.comp
    (by fun_prop : Measurable fun r : ℝ => Real.exp (-(2 * (h - r) * om 0)))).indicator measurableSet_Icc
  have hpt : ∀ r ω, r ∈ Set.Icc 0 h → ∑' j, ∑' l,
      ENNReal.ofReal (s81q_fcl om h l r ^ 2 * SeqL2.coord (v r ω j) l ^ 2) ≤ K r * Zf r ω := by
    intro r ω hr
    simp only [hK, Set.indicator_of_mem hr, hZf, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [s8p_seq_enorm_sq, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun l => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (s81q_fcl_sq_le hmono h l hr)
      (sq_nonneg _))
  have hZfm : Measurable fun q : Ω' × ℝ => Zf q.2 q.1 := by
    have : ∀ q : Ω' × ℝ, Zf q.2 q.1 = ∑' j, ∑' l, ENNReal.ofReal (SeqL2.coord (v q.2 q.1 j) l ^ 2) := by
      intro q; simp only [hZf]; exact tsum_congr fun j => s8p_seq_enorm_sq _
    simp_rw [this]
    refine Measurable.ennreal_tsum fun j => Measurable.ennreal_tsum fun l =>
      ENNReal.measurable_ofReal.comp ((?_ : Measurable _).pow_const 2)
    exact (HRS.MRep.isProgressive_measurable_uncurry (hv j l)).comp measurable_swap
  have hLm : Measurable fun q : Ω' × ℝ => ∑' j, ∑' l,
      ENNReal.ofReal (s81q_fcl om h l q.2 ^ 2 * SeqL2.coord (v q.2 q.1 j) l ^ 2) := by
    refine Measurable.ennreal_tsum fun j => Measurable.ennreal_tsum fun l =>
      ENNReal.measurable_ofReal.comp ?_
    have h1 : Measurable fun q : Ω' × ℝ => s81q_fcl om h l q.2 :=
      (s81q_fcl_cont om h l).measurable.comp measurable_snd
    have h2 : Measurable fun q : Ω' × ℝ => SeqL2.coord (v q.2 q.1 j) l :=
      (HRS.MRep.isProgressive_measurable_uncurry (hv j l)).comp measurable_swap
    exact (h1.pow_const 2).mul (h2.pow_const 2)
  have hZfb : ∀ r ∈ Set.Icc 0 h, ∫⁻ ω, Zf r ω ∂P' ≤ Z := fun r hr => hb r hr
  have hKint : ∫⁻ r in Set.Icc 0 h, K r ≤ ENNReal.ofReal (1 / (2 * om 0)) := by
    have h1 : ∫⁻ r in Set.Icc 0 h, K r = ∫⁻ r in Set.Icc 0 h,
        ENNReal.ofReal (Real.exp (-(2 * (h - r) * om 0))) := by
      rw [hK, lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
        Set.inter_self]
    rw [h1]
    have := s8p_lintegral_exp_le (c := 2 * om 0) (by linarith [hom 0]) hh
    refine le_trans (le_of_eq ?_) this
    refine lintegral_congr fun r => ?_
    congr 2
    ring
  calc ∫⁻ ω, (∫⁻ r in Set.Icc 0 h, ∑' j, ∑' l,
        ENNReal.ofReal (s81q_fcl om h l r ^ 2 * SeqL2.coord (v r ω j) l ^ 2)) ∂P'
      ≤ ∫⁻ ω, (∫⁻ r in Set.Icc 0 h, K r * Zf r ω) ∂P' := by
        refine lintegral_mono fun ω => ?_
        exact setLIntegral_mono' measurableSet_Icc fun r hr => hpt r ω hr
    _ = ∫⁻ r in Set.Icc 0 h, (∫⁻ ω, K r * Zf r ω ∂P') := by
        refine lintegral_lintegral_swap ?_
        refine (?_ : Measurable fun q : Ω' × ℝ => K q.2 * Zf q.2 q.1).aemeasurable
        exact (hKm.comp measurable_snd).mul hZfm
    _ ≤ ∫⁻ r in Set.Icc 0 h, K r * Z := by
        refine lintegral_mono fun r => ?_
        by_cases hr : r ∈ Set.Icc 0 h
        · rw [lintegral_const_mul' _ _ (by simp [hK, Set.indicator_of_mem hr])]
          exact mul_le_mul_right (hZfb r hr) _
        · simp [hK, Set.indicator_of_notMem hr]
    _ = (∫⁻ r in Set.Icc 0 h, K r) * Z := lintegral_mul_const' _ _ hZ
    _ ≤ ENNReal.ofReal (1 / (2 * om 0)) * Z := by gcongr
    _ = _ := mul_comm _ _

end Master

section Cost

variable {β τ : ℝ} {om : ℕ → ℝ}

/-- The constant diagonal root `diag(√d_l)`. -/
def s81q_SbD (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ) : SeqL2 →L[ℝ] SeqL2 :=
  s81q_diag (fun l => Real.sqrt (s8p_dv β om τ l)) (Real.sqrt (4 / (β * τ)))
    (fun l => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (s8p_dv_le hβ hom hτ l))

theorem s81q_SbD_coord (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ) (z : SeqL2) (l : ℕ) :
    SeqL2.coord (s81q_SbD hβ hom hτ z) l = Real.sqrt (s8p_dv β om τ l) * SeqL2.coord z l :=
  s81q_diag_coord _ z l

/-- Every square root of `Cdet` is the constant diagonal root. -/
theorem s81q_Sb_eq_SbD (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hτ : 0 < τ) {S : SeqL2 →L[ℝ] SeqL2}
    (hS : IsSqrtOfForm S (s8p_Cdet hβ hom hτ)) : S = s81q_SbD hβ hom hτ := by
  refine ContinuousLinearMap.ext fun z => s81q_seqL2_ext fun l => ?_
  rw [s81q_SbD_coord, ← s8p_inner_basis l (S z), hS.symm, s8p_sqrt_basis hβ hom hτ hS l,
    inner_smul_right, s8p_inner_basis]

theorem s81q_cOld_eq (h : ℝ) (l : ℕ) {r : ℝ} (hr : r ∈ Set.Icc 0 h) :
    s81q_cOld β τ h om l r = Real.sqrt (s8p_dv β om τ l) * s81q_fcl om h l r := by
  unfold s81q_cOld s81q_fcl
  rw [if_pos hr, min_eq_left hr.2]

theorem s81q_isCtbl_sub {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    {A : Type*} {ξ ξ' : ℝ → Ω → A → ℝ} (hξ : IsCtbl P ℱ ξ) (hξ' : IsCtbl P ℱ ξ') :
    IsCtbl P ℱ (fun r ω a => ξ r ω a - ξ' r ω a) := by
  have h2 := hξ'.mul_bdd (w := fun _ (_ : Ω) => (-1 : ℝ)) (pc_isProgressive_det measurable_const)
    (C := 1) (fun _ _ => by simp)
  have h3 := hξ.add h2
  have e : (fun r ω a => ξ r ω a - ξ' r ω a) =
      fun r ω a => ξ r ω a + (fun _ (_ : Ω) => (-1 : ℝ)) r ω * ξ' r ω a := by
    funext r ω a; ring
  rw [e]; exact h3

/-- Exchange of the sums with the two integrals (all terms nonnegative, jointly measurable). -/
theorem s81q_swap_sums {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (P' : Measure Ω') {ι : Type} [Countable ι]
    (h : ℝ) (F : ℕ → ι → ℝ → Ω' → ℝ≥0∞) (hF : ∀ l j, Measurable fun q : Ω' × ℝ => F l j q.2 q.1) :
    ∑' j, ∑' l, ∫⁻ ω, (∫⁻ r in Set.Icc 0 h, F l j r ω) ∂P' =
      ∫⁻ ω, (∫⁻ r in Set.Icc 0 h, ∑' j, ∑' l, F l j r ω) ∂P' := by
  have hA : ∀ l j, Measurable fun ω => ∫⁻ r in Set.Icc 0 h, F l j r ω := fun l j =>
    (hF l j).lintegral_prod_right' (ν := volume.restrict (Set.Icc 0 h))
  have hFr : ∀ l j ω, Measurable fun r => F l j r ω := fun l j ω =>
    (hF l j).comp (measurable_prodMk_left (m := mΩ') (x := ω))
  have hr : ∀ ω, ∫⁻ r in Set.Icc 0 h, ∑' j, ∑' l, F l j r ω =
      ∑' j, ∑' l, ∫⁻ r in Set.Icc 0 h, F l j r ω := by
    intro ω
    rw [lintegral_tsum fun j => (Measurable.ennreal_tsum fun l => hFr l j ω).aemeasurable]
    exact tsum_congr fun j => lintegral_tsum fun l => (hFr l j ω).aemeasurable
  simp_rw [hr]
  rw [lintegral_tsum fun j => (Measurable.ennreal_tsum fun l => hA l j).aemeasurable]
  refine tsum_congr fun j => ?_
  rw [lintegral_tsum fun l => (hA l j).aemeasurable]

/-- **The old-current cost** `E ∑_l |J_l(h) - G_l(h)|² ≤ Z / (2 ω_0)`. -/
theorem s81q_old_cost (hβ : 0 < β) (hom : ∀ l, 0 < om l) (hmono : Monotone om) (hτ : 0 < τ)
    (hsum : Summable (s8p_dv β om τ)) {h : ℝ} (hh : 0 ≤ h) {Ω' : Type} {mΩ' : MeasurableSpace Ω'}
    (P' : Measure Ω') [IsProbabilityMeasure P'] (ℱ' : Filtration ℝ mΩ') {ι : Type} [Countable ι]
    (eb : HilbertBasis ι ℝ SeqL2) {B : ℝ≥0 → Ω' → ι → ℝ} (hB : IsCylindricalBrownian P' ℱ' B)
    (Sx : ℝ → Ω' → SeqL2 →L[ℝ] SeqL2)
    (hSprog : ∀ x y, IsProgressive ℱ' (fun r ω => inner ℝ (Sx r ω x) y))
    (hHS : ∀ T : ℝ, IsHSIntegrand P' ℱ' T (fun r ω (j : ι) => if r ≤ h then Sx r ω (eb j) else 0))
    (Sb : ℝ → SeqL2 →L[ℝ] SeqL2) (hSb : ∀ r ∈ Set.Icc 0 h, IsSqrtOfForm (Sb r) (s8p_Cdet hβ hom hτ))
    {Z : ℝ≥0∞} (hZ : Z ≠ ⊤)
    (hbound : ∀ r ∈ Set.Icc 0 h, ∫⁻ ω, ∑' j, ‖(Sx r ω - Sb r) (eb j)‖ₑ ^ 2 ∂P' ≤ Z) :
    ∃ (G : ℝ → Ω' → SeqL2) (Js : ℕ → ℝ → Ω' → ℝ),
      Measurable[ℱ' h] (G h) ∧ IsCenteredGaussian (law P' (G h)) ∧
      (∀ x y, covarianceBilin (law P' (G h)) x y =
        ∑' l, s81q_sOld β τ h om l * SeqL2.coord x l * SeqL2.coord y l) ∧
      Indep (ℱ' 0) (MeasurableSpace.comap (G h) inferInstance) P' ∧
      (∀ l, IsItoC P' ℱ' B (fun r ω (j : ι) => s81q_fcl om h l r *
        inner ℝ (if r ≤ h then Sx r ω (eb j) else 0) (S45.s45_seqBasis l)) (Js l)) ∧
      ∫⁻ ω, ∑' l, ‖Js l h ω - SeqL2.coord (G h ω) l‖ₑ ^ 2 ∂P' ≤
        Z * ENNReal.ofReal (1 / (2 * om 0)) := by
  classical
  obtain ⟨G, hGad, hGg, hGcov, hGind, hGl⟩ := s81q_old_gaussian hβ hom hτ hsum h hh P' ℱ' eb hB
  have hGm : Measurable (G h) := hGad.mono (ℱ'.le h) le_rfl
  set b := S45.s45_seqBasis with hb
  have hctblW : ∀ l, IsCtbl P' ℱ' (fun r ω (j : ι) => s81q_fcl om h l r *
      inner ℝ (if r ≤ h then Sx r ω (eb j) else 0) (b l)) := fun l =>
    (HRS.Uniform.Q07c.ctbl_coord hHS (b l)).mul_bdd (w := fun r (_ : Ω') => s81q_fcl om h l r)
      (pc_isProgressive_det (s81q_fcl_cont om h l).measurable) (C := 1)
      (fun r _ => s81q_fcl_abs_le hom h l r)
  choose Js hJs using fun l => exists_isItoC hB (hctblW l)
  choose hGc JG hJG hGae using hGl
  refine ⟨G, Js, hGad, hGg, hGcov, hGind, hJs, ?_⟩
  set SbD := s81q_SbD hβ hom hτ with hSbD
  set v : ℝ → Ω' → ι → SeqL2 := fun r ω j => Sx r ω (eb j) - SbD (eb j) with hv
  -- the coordinates of `v`
  have hvc : ∀ r ω j l, SeqL2.coord (v r ω j) l =
      inner ℝ (Sx r ω (eb j)) (b l) - Real.sqrt (s8p_dv β om τ l) * SeqL2.coord (eb j) l := by
    intro r ω j l
    simp only [hv]
    rw [u11_coord_sub, s81q_SbD_coord, ← s8p_inner_basis l (Sx r ω (eb j))]
  have hvprog : ∀ j l, IsProgressive ℱ' (fun r ω => SeqL2.coord (v r ω j) l) := by
    intro j l
    have : (fun r ω => SeqL2.coord (v r ω j) l) = fun r ω =>
        inner ℝ (Sx r ω (eb j)) (b l) - Real.sqrt (s8p_dv β om τ l) * SeqL2.coord (eb j) l := by
      funext r ω; exact hvc r ω j l
    rw [this]
    exact fun i => (hSprog (eb j) (b l) i).sub measurable_const
  have hterm : ∀ l j, Measurable fun q : Ω' × ℝ =>
      ENNReal.ofReal (s81q_fcl om h l q.2 ^ 2 * SeqL2.coord (v q.2 q.1 j) l ^ 2) := by
    intro l j
    refine ENNReal.measurable_ofReal.comp ?_
    exact (((s81q_fcl_cont om h l).measurable.comp measurable_snd).pow_const 2).mul
      (((HRS.MRep.isProgressive_measurable_uncurry (hvprog j l)).comp measurable_swap).pow_const 2)
  -- the per-coordinate bound
  have hper : ∀ l, ∫⁻ ω, ‖Js l h ω - SeqL2.coord (G h ω) l‖ₑ ^ 2 ∂P' ≤
      ∑' j, ∫⁻ ω, (∫⁻ r in Set.Icc 0 h,
        ENNReal.ofReal (s81q_fcl om h l r ^ 2 * SeqL2.coord (v r ω j) l ^ 2)) ∂P' := by
    intro l
    have hdiff := IsItoC.sub hB (hctblW l) (hGc l) (hJs l) (hJG l)
    have hdc := s81q_isCtbl_sub (hctblW l) (hGc l)
    have h1 := IsItoC.lintegral_sq_le hdc hB hdiff hh
    have h2 : ∫⁻ ω, ‖Js l h ω - SeqL2.coord (G h ω) l‖ₑ ^ 2 ∂P' =
        ∫⁻ ω, ‖Js l h ω - JG l h ω‖ₑ ^ 2 ∂P' := by
      refine lintegral_congr_ae ?_
      filter_upwards [hGae l] with ω hω
      rw [hω]
    rw [h2]
    refine h1.trans (ENNReal.tsum_le_tsum fun j => ?_)
    unfold cT
    refine lintegral_mono fun ω => ?_
    rw [← setLIntegral_congr (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := h) (μ := volume)),
      ← setLIntegral_congr (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := h) (μ := volume))]
    refine le_of_eq (setLIntegral_congr_fun measurableSet_Ioc fun r hr => ?_)
    have hrI : r ∈ Set.Icc 0 h := ⟨hr.1.le, hr.2⟩
    show ‖s81q_fcl om h l r * inner ℝ (if r ≤ h then Sx r ω (eb j) else 0) (b l) -
        (if r ≤ h then s81q_cOld β τ h om l r * inner ℝ (eb j) (b l) else 0)‖ₑ ^ 2 = _
    rw [if_pos hr.2, if_pos hr.2, s81q_cOld_eq h l hrI, hvc, s8p_enorm_sq_eq,
      ← s8p_inner_basis l (eb j)]
    congr 1
    ring
  have hb : ∀ r ∈ Set.Icc (0 : ℝ) h, ∫⁻ ω, ∑' j, ‖v r ω j‖ₑ ^ 2 ∂P' ≤ Z := by
    intro r hr
    refine le_trans (le_of_eq ?_) (hbound r hr)
    have e : ∀ ω j, v r ω j = (Sx r ω - Sb r) (eb j) := by
      intro ω j
      rw [s81q_Sb_eq_SbD hβ hom hτ (hSb r hr)]
      rfl
    simp_rw [e]
  have hmaster := s81q_master hom hmono hh v hvprog hZ hb
  -- the total
  calc ∫⁻ ω, ∑' l, ‖Js l h ω - SeqL2.coord (G h ω) l‖ₑ ^ 2 ∂P'
      = ∑' l, ∫⁻ ω, ‖Js l h ω - SeqL2.coord (G h ω) l‖ₑ ^ 2 ∂P' := by
        refine lintegral_tsum fun l => ?_
        have h1 : Measurable (Js l h) := ((hJs l).adapted h).mono (ℱ'.le h) le_rfl
        exact ((h1.sub (s8p_coord_measurable hGm l)).enorm.pow_const 2).aemeasurable
    _ ≤ ∑' l, ∑' j, ∫⁻ ω, (∫⁻ r in Set.Icc 0 h,
          ENNReal.ofReal (s81q_fcl om h l r ^ 2 * SeqL2.coord (v r ω j) l ^ 2)) ∂P' :=
        ENNReal.tsum_le_tsum hper
    _ = ∑' j, ∑' l, ∫⁻ ω, (∫⁻ r in Set.Icc 0 h,
          ENNReal.ofReal (s81q_fcl om h l r ^ 2 * SeqL2.coord (v r ω j) l ^ 2)) ∂P' :=
        ENNReal.tsum_comm
    _ = ∫⁻ ω, (∫⁻ r in Set.Icc 0 h, ∑' j, ∑' l,
          ENNReal.ofReal (s81q_fcl om h l r ^ 2 * SeqL2.coord (v r ω j) l ^ 2)) ∂P' :=
        s81q_swap_sums P' h (fun l j r ω =>
          ENNReal.ofReal (s81q_fcl om h l r ^ 2 * SeqL2.coord (v r ω j) l ^ 2)) hterm
    _ ≤ _ := hmaster

end Cost

end HRS.Whole.S81Q
