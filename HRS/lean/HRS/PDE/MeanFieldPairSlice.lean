import HRS.PDE.MeanFieldDefs
import HRS.Prob.Gaussian

/-!
# Lemma 4.14, packet P12a: Fourier slices of a `C^J` kernel of two torus variables (package MF-01)

For `R : 𝕋^d → 𝕋^d → ℝ` of class `C^J` (`IsCk2 J R`, i.e. `lift2 R` is `C^J` on `ℝ^d × ℝ^d`),
`sliceCoeff R k y = R̂(k; y)` is the `k`-th Fourier coefficient of the slice `x ↦ R(x,y)`.

* `exists_sliceCoeff_bound`: `Re/Im R̂(k;·)` is `C^n` with `C^n` norm `≲ cbNorm2 J R ⟨k⟩^{-N}` for
  `n + N ≤ J`, with a constant depending only on `n, N` (and `d`).  Proof: differentiation under the
  `x`-integral (`HRS.contDiff_integral_dominated`, `slice_integral_contDiff`) and `N` integrations by
  parts in `x` along the direction `k/|k|` (`dX`, `acas_dX`, `Phi_dXn`, `slice_norm_bound`).
* `eq_toFun_sliceCoeff`: reconstruction `R(x,y) = ∑_k Re(R̂(k;y) e_k(x))` with `ℓ¹` coefficients
  (a `C^J` function with `J > d/2` has `H^J` coefficients; local copies of `memHs_of_isCk`,
  `toFun_coeffOf` avoid importing `MeanFieldThermalReg`, which depends on `MeanFieldInputs`).
* `sliceCoeff_centered`: a doubly centered kernel has `μ_β`-centered slice coefficients (Fubini).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFPair

variable {d : ℕ}

/-- The `k`-th Fourier coefficient of the slice `x ↦ R(x,y)`, as a function of `y`. -/
def sliceCoeff (R : Torus d → Torus d → ℝ) (k : Lattice d) (y : Torus d) : ℂ :=
  coeffOf (fun x => R x y) k

/-! ### Periodicity and boundedness on `ℝ^d × ℝ^d` -/

/-- Invariance under lattice translations in the first variable. -/
def PerX {α : Type*} (g : Euc d × Euc d → α) : Prop :=
  ∀ (m : Lattice d) (p : Euc d × Euc d), g (p + (Lattice.toEuc m, 0)) = g p

/-- Invariance under lattice translations in the second variable. -/
def PerY {α : Type*} (g : Euc d × Euc d → α) : Prop :=
  ∀ (m : Lattice d) (p : Euc d × Euc d), g (p + (0, Lattice.toEuc m)) = g p

theorem perX_lift2 (R : Torus d → Torus d → ℝ) : PerX (lift2 R) := by
  intro m p
  simp [lift2, Torus.mk_add, Torus.mk_toEuc]

theorem perY_lift2 (R : Torus d → Torus d → ℝ) : PerY (lift2 R) := by
  intro m p
  simp [lift2, Torus.mk_add, Torus.mk_toEuc]

theorem PerX.iteratedFDeriv {g : Euc d × Euc d → ℝ} (h : PerX g) (i : ℕ) :
    PerX (fun p => iteratedFDeriv ℝ i g p) := by
  intro m p
  have e : (fun q => g (q + (Lattice.toEuc m, 0))) = g := funext fun q => h m q
  have h2 := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := g) i (Lattice.toEuc m, 0) p
  rw [e] at h2
  exact h2.symm

theorem PerY.iteratedFDeriv {g : Euc d × Euc d → ℝ} (h : PerY g) (i : ℕ) :
    PerY (fun p => iteratedFDeriv ℝ i g p) := by
  intro m p
  have e : (fun q => g (q + (0, Lattice.toEuc m))) = g := funext fun q => h m q
  have h2 := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := g) i (0, Lattice.toEuc m) p
  rw [e] at h2
  exact h2.symm

theorem PerX.fderiv {g : Euc d × Euc d → ℝ} (h : PerX g) :
    PerX (fun p => _root_.fderiv ℝ g p) := by
  intro m p
  have e : (fun q => g (q + (Lattice.toEuc m, 0))) = g := funext fun q => h m q
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := p) (Lattice.toEuc m, 0)
  rw [e] at h2
  exact h2.symm

theorem PerY.fderiv {g : Euc d × Euc d → ℝ} (h : PerY g) :
    PerY (fun p => _root_.fderiv ℝ g p) := by
  intro m p
  have e : (fun q => g (q + (0, Lattice.toEuc m))) = g := funext fun q => h m q
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := p) (0, Lattice.toEuc m)
  rw [e] at h2
  exact h2.symm

theorem exists_shift_mem_closedBall (x : Euc d) :
    ∃ m : Lattice d, x + Lattice.toEuc m ∈ Metric.closedBall (0 : Euc d) d := by
  refine ⟨fun i => -⌊x i⌋, ?_⟩
  have hyc : ∀ i, 0 ≤ (x + Lattice.toEuc (fun i => -⌊x i⌋)) i ∧
      (x + Lattice.toEuc (fun i => -⌊x i⌋)) i < 1 := by
    intro i
    have := Int.floor_le (x i)
    have h2 := Int.lt_floor_add_one (x i)
    simp only [Lattice.toEuc, PiLp.add_apply, Int.cast_neg]
    constructor <;> linarith
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  refine ⟨Nat.cast_nonneg d, ?_⟩
  calc ∑ i, ‖(x + Lattice.toEuc (fun i => -⌊x i⌋)) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [Real.norm_eq_abs, sq_abs]
        have := hyc i
        nlinarith
    _ = d := by simp
    _ ≤ (d : ℝ) ^ 2 := by
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · simp [h0]
        · have : (1 : ℝ) ≤ d := by exact_mod_cast h0
          nlinarith

theorem bddAbove_of_perXY {h : Euc d × Euc d → ℝ} (hc : Continuous h) (hx : PerX h)
    (hy : PerY h) : BddAbove (Set.range h) := by
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : Euc d) d).prod
    (isCompact_closedBall (0 : Euc d) d)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨‖M‖, ?_⟩
  rintro _ ⟨p, rfl⟩
  obtain ⟨m1, hm1⟩ := exists_shift_mem_closedBall p.1
  obtain ⟨m2, hm2⟩ := exists_shift_mem_closedBall p.2
  have e : h p = h (p.1 + Lattice.toEuc m1, p.2 + Lattice.toEuc m2) := by
    have h1 := hx m1 p
    have h2 := hy m2 (p + (Lattice.toEuc m1, 0))
    rw [← h1, ← h2]
    congr 1
    ext <;> simp
  rw [e]
  have := hM (p.1 + Lattice.toEuc m1, p.2 + Lattice.toEuc m2) ⟨hm1, hm2⟩
  exact (le_abs_self _).trans (this.trans (le_abs_self _))


theorem bddAbove_norm_iteratedFDeriv {g : Euc d × Euc d → ℝ} {n : ℕ} (hg : ContDiff ℝ n g)
    (hx : PerX g) (hy : PerY g) {i : ℕ} (hi : i ≤ n) :
    BddAbove (Set.range fun p => ‖iteratedFDeriv ℝ i g p‖) :=
  bddAbove_of_perXY (hg.continuous_iteratedFDeriv (by exact_mod_cast hi)).norm
    (fun m p => by simp only [(hx.iteratedFDeriv i) m p])
    (fun m p => by simp only [(hy.iteratedFDeriv i) m p])

/-! ### Directional derivatives in the first variable -/

/-- The derivative of `g` in the direction `(e, 0)`. -/
def dX (e : Euc d) (g : Euc d × Euc d → ℝ) : Euc d × Euc d → ℝ :=
  fun p => fderiv ℝ g p (e, 0)

theorem dX_eq (e : Euc d) (g : Euc d × Euc d → ℝ) :
    dX e g = (ContinuousLinearMap.apply ℝ ℝ ((e, (0 : Euc d)) : Euc d × Euc d)) ∘ (fderiv ℝ g) := rfl

theorem norm_apply_clm_le (v : Euc d × Euc d) :
    ‖(ContinuousLinearMap.apply ℝ ℝ v : ((Euc d × Euc d) →L[ℝ] ℝ) →L[ℝ] ℝ)‖ ≤ ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun f => ?_
  simpa [mul_comm] using f.le_opNorm v

theorem contDiff_dX {g : Euc d × Euc d → ℝ} {n : ℕ} (e : Euc d) (hg : ContDiff ℝ (n + 1 : ℕ) g) :
    ContDiff ℝ n (dX e g) := by
  rw [dX_eq]
  exact (ContinuousLinearMap.apply ℝ ℝ ((e, (0 : Euc d)) : Euc d × Euc d)).contDiff.comp
    (hg.fderiv_right (by push_cast; exact le_rfl))

theorem norm_iteratedFDeriv_dX {g : Euc d × Euc d → ℝ} {n : ℕ} (e : Euc d)
    (hg : ContDiff ℝ (n + 1 : ℕ) g) {i : ℕ} (hi : i ≤ n) (p : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ i (dX e g) p‖ ≤ ‖e‖ * ‖iteratedFDeriv ℝ (i + 1) g p‖ := by
  rw [dX_eq]
  have hf : ContDiff ℝ (n : ℕ) (fderiv ℝ g) := hg.fderiv_right (by push_cast; exact le_rfl)
  have h1 := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
    (ContinuousLinearMap.apply ℝ ℝ ((e, (0 : Euc d)) : Euc d × Euc d))
    (hf.contDiffAt (x := p)) (n := i) (by exact_mod_cast hi)
  rw [norm_iteratedFDeriv_fderiv] at h1
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine (norm_apply_clm_le _).trans ?_
  simp [Prod.norm_def]

theorem perX_dX {g : Euc d × Euc d → ℝ} (h : PerX g) (e : Euc d) : PerX (dX e g) := by
  intro m p
  simp only [dX]
  have := h.fderiv m p
  simp only at this
  rw [this]

theorem perY_dX {g : Euc d × Euc d → ℝ} (h : PerY g) (e : Euc d) : PerY (dX e g) := by
  intro m p
  simp only [dX]
  have := h.fderiv m p
  simp only at this
  rw [this]

/-- The `N`-fold derivative in the direction `(e, 0)`. -/
def dXn (e : Euc d) : ℕ → (Euc d × Euc d → ℝ) → (Euc d × Euc d → ℝ)
  | 0, g => g
  | N + 1, g => dXn e N (dX e g)

theorem dXn_spec (e : Euc d) : ∀ (N : ℕ) (g : Euc d × Euc d → ℝ) (n : ℕ),
    ContDiff ℝ (n + N : ℕ) g →
      ContDiff ℝ n (dXn e N g) ∧
      ∀ i ≤ n, ∀ p, ‖iteratedFDeriv ℝ i (dXn e N g) p‖ ≤ ‖e‖ ^ N * ‖iteratedFDeriv ℝ (i + N) g p‖ := by
  intro N
  induction N with
  | zero =>
    intro g n hg
    exact ⟨by simpa [dXn] using hg, fun i _ p => by simp [dXn]⟩
  | succ N ih =>
    intro g n hg
    have hg' : ContDiff ℝ (n + N + 1 : ℕ) g := by
      have : n + (N + 1) = n + N + 1 := by ring
      rwa [this] at hg
    have hd : ContDiff ℝ (n + N : ℕ) (dX e g) := contDiff_dX e hg'
    obtain ⟨h1, h2⟩ := ih (dX e g) n hd
    refine ⟨h1, fun i hi p => ?_⟩
    refine (h2 i hi p).trans ?_
    have := norm_iteratedFDeriv_dX e hg' (i := i + N) (by omega) p
    calc ‖e‖ ^ N * ‖iteratedFDeriv ℝ (i + N) (dX e g) p‖
        ≤ ‖e‖ ^ N * (‖e‖ * ‖iteratedFDeriv ℝ (i + N + 1) g p‖) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ‖e‖ ^ (N + 1) * ‖iteratedFDeriv ℝ (i + (N + 1)) g p‖ := by
          rw [pow_succ, show i + (N + 1) = i + N + 1 by ring]; ring

theorem perX_dXn (e : Euc d) : ∀ (N : ℕ) (g : Euc d × Euc d → ℝ), PerX g → PerX (dXn e N g) := by
  intro N
  induction N with
  | zero => intro g h; exact h
  | succ N ih => intro g h; exact ih _ (perX_dX h e)

theorem perY_dXn (e : Euc d) : ∀ (N : ℕ) (g : Euc d × Euc d → ℝ), PerY g → PerY (dXn e N g) := by
  intro N
  induction N with
  | zero => intro g h; exact h
  | succ N ih => intro g h; exact ih _ (perY_dX h e)


/-! ### Smoothness and bounds of the `x`-integral -/

theorem iteratedFDeriv_partial (G : Euc d × Euc d → ℝ) {n : ℕ} (hG : ContDiff ℝ n G) {i : ℕ}
    (hi : i ≤ n) (q v : Euc d) :
    iteratedFDeriv ℝ i (fun v' => G (q, v')) v =
      (iteratedFDeriv ℝ i G (q, v)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) := by
  have h1 : (fun v' => G (q, v')) =
      (fun p => G (p + (q, 0))) ∘ (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) := by
    funext v'; simp
  have hf : ContDiff ℝ n (fun p => G (p + (q, 0))) := hG.comp (contDiff_id.add contDiff_const)
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ hf v (by exact_mod_cast hi),
    iteratedFDeriv_comp_add_right]
  simp

theorem norm_iteratedFDeriv_partial_le (G : Euc d × Euc d → ℝ) {n : ℕ} (hG : ContDiff ℝ n G)
    {i : ℕ} (hi : i ≤ n) (q v : Euc d) :
    ‖iteratedFDeriv ℝ i (fun v' => G (q, v')) v‖ ≤ ‖iteratedFDeriv ℝ i G (q, v)‖ := by
  rw [iteratedFDeriv_partial G hG hi]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ‖ContinuousLinearMap.inr ℝ (Euc d) (Euc d)‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one _ _ _
  have : ∏ _i : Fin i, ‖ContinuousLinearMap.inr ℝ (Euc d) (Euc d)‖ ≤ 1 := by
    rw [Finset.prod_const]
    exact pow_le_one₀ (norm_nonneg _) h1
  calc _ ≤ ‖iteratedFDeriv ℝ i G (q, v)‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _

theorem continuous_descend_partial (G : Euc d × Euc d → ℝ) {n : ℕ} (hG : ContDiff ℝ n G)
    (hper : PerX G) {i : ℕ} (hi : i ≤ n) (v : Euc d) :
    Continuous fun x : Torus d => iteratedFDeriv ℝ i (fun v' => G (Torus.rep x, v')) v := by
  set Φ : Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ :=
    fun q => iteratedFDeriv ℝ i (fun v' => G (q, v')) v with hΦ
  have hc : Continuous Φ := by
    have e : Φ = fun q => (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin i => ContinuousLinearMap.inr ℝ (Euc d) (Euc d))) (iteratedFDeriv ℝ i G (q, v)) := by
      funext q
      exact iteratedFDeriv_partial G hG hi q v
    rw [e]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL _).continuous.comp
      ((hG.continuous_iteratedFDeriv (by exact_mod_cast hi)).comp (continuous_id.prodMk continuous_const))
  have hp : Torus.Per Φ := by
    intro q m
    simp only [hΦ]
    have : (fun v' => G (q + Lattice.toEuc m, v')) = fun v' => G (q, v') := by
      funext v'
      have := hper m (q, v')
      simpa using this
    rw [this]
  exact Torus.continuous_descend hp hc

theorem continuous_descend_first (G : Euc d × Euc d → ℝ) (hc : Continuous G) (hper : PerX G)
    (v : Euc d) : Continuous fun x : Torus d => G (Torus.rep x, v) := by
  have hp : Torus.Per (fun q => G (q, v)) := by
    intro q m
    have := hper m (q, v)
    simpa using this
  exact Torus.continuous_descend hp (hc.comp (continuous_id.prodMk continuous_const))


/-- Smoothness and derivative bounds for the `x`-integral `v ↦ ∫ w(x) G(x,v) dx` of a function
which is `C^n` and periodic in the first variable. -/
theorem slice_integral_contDiff (w : Torus d → ℝ) (hw : Continuous w) (hw1 : ∀ x, |w x| ≤ 1)
    (n : ℕ) (G : Euc d × Euc d → ℝ) (hG : ContDiff ℝ n G) (hper : PerX G) (B : ℕ → ℝ)
    (hB : ∀ i ≤ n, ∀ p, ‖iteratedFDeriv ℝ i G p‖ ≤ B i) :
    ContDiff ℝ n (fun v => ∫ x : Torus d, w x * G (Torus.rep x, v)) ∧
    ∀ i ≤ n, ∀ v, ‖iteratedFDeriv ℝ i (fun v => ∫ x : Torus d, w x * G (Torus.rep x, v)) v‖ ≤ B i := by
  have hGc : Continuous G := hG.continuous
  have hint : ∀ v, Integrable (fun x : Torus d => w x * G (Torus.rep x, v)) := fun v =>
    (hw.mul (continuous_descend_first G hGc hper v)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- pointwise bound on the integrand
  have hbd : ∀ i ≤ n, ∀ (x : Torus d) (v : Euc d),
      ‖iteratedFDeriv ℝ i (fun v' => w x * G (Torus.rep x, v')) v‖ ≤ B i := by
    intro i hi x v
    have e : (fun v' => w x * G (Torus.rep x, v')) = w x • (fun v' => G (Torus.rep x, v')) := by
      funext v'; simp
    have hcd : ContDiff ℝ i (fun v' => G (Torus.rep x, v')) :=
      (hG.of_le (by exact_mod_cast hi)).comp (contDiff_const.prodMk contDiff_id)
    rw [e, iteratedFDeriv_const_smul_apply hcd.contDiffAt, norm_smul, Real.norm_eq_abs]
    calc |w x| * ‖iteratedFDeriv ℝ i (fun v' => G (Torus.rep x, v')) v‖
        ≤ 1 * B i := by
          refine mul_le_mul (hw1 x) ?_ (norm_nonneg _) zero_le_one
          exact (norm_iteratedFDeriv_partial_le G hG hi _ _).trans (hB i hi _)
      _ = B i := one_mul _
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hcont : Continuous fun v => ∫ x : Torus d, w x * G (Torus.rep x, v) := by
      refine continuous_of_dominated (bound := fun _ => B 0) (fun v => (hint v).aestronglyMeasurable)
        (fun v => Filter.Eventually.of_forall fun x => ?_) (integrable_const _)
        (Filter.Eventually.of_forall fun x => ?_)
      · have := hbd 0 le_rfl x v
        simpa using this
      · exact continuous_const.mul (hGc.comp (continuous_const.prodMk continuous_id))
    refine ⟨contDiff_zero.2 hcont, fun i hi v => ?_⟩
    obtain rfl : i = 0 := by omega
    simp only [norm_iteratedFDeriv_zero]
    have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus d)))
      (f := fun x : Torus d => w x * G (Torus.rep x, v)) (C := B 0)
      (Filter.Eventually.of_forall fun x => by simpa using hbd 0 le_rfl x v)
    simpa using this
  · have key := contDiff_integral_dominated (B := Euc d) (S := Torus d) (volume : Measure (Torus d))
      (fun x v => w x * G (Torus.rep x, v)) n hpos
      (fun x => contDiff_const.mul (hG.comp (contDiff_const.prodMk contDiff_id)))
      hint
      (fun j hj v => by
        have e : (fun x : Torus d => iteratedFDeriv ℝ j (fun v' => w x * G (Torus.rep x, v')) v) =
            fun x => w x • iteratedFDeriv ℝ j (fun v' => G (Torus.rep x, v')) v := by
          funext x
          have e2 : (fun v' => w x * G (Torus.rep x, v')) = w x • (fun v' => G (Torus.rep x, v')) := by
            funext v'; simp
          have hcd : ContDiff ℝ j (fun v' => G (Torus.rep x, v')) :=
            (hG.of_le (by exact_mod_cast hj)).comp (contDiff_const.prodMk contDiff_id)
          rw [e2, iteratedFDeriv_const_smul_apply hcd.contDiffAt]
        rw [e]
        exact (hw.smul (continuous_descend_partial G hG hper hj v)).aestronglyMeasurable)
      (fun j _ => B j) (fun j _ _ => integrable_const _)
      (fun j _ hj x v => hbd j hj x v)
    refine ⟨key.1, fun i hi v => ?_⟩
    rw [key.2 i hi v]
    have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus d)))
      (f := fun x : Torus d => iteratedFDeriv ℝ i (fun v' => w x * G (Torus.rep x, v')) v) (C := B i)
      (Filter.Eventually.of_forall fun x => hbd i hi x v)
    simpa using this


/-! ### Integration by parts in the first variable -/

/-- `∫ cos(2π k·x) g(x,v) dx`. -/
def acF (k : Lattice d) (g : Euc d × Euc d → ℝ) (v : Euc d) : ℝ :=
  ∫ x : Torus d, Torus.cosMode k x * g (Torus.rep x, v)

/-- `∫ sin(2π k·x) g(x,v) dx`. -/
def asF (k : Lattice d) (g : Euc d × Euc d → ℝ) (v : Euc d) : ℝ :=
  ∫ x : Torus d, Torus.sinMode k x * g (Torus.rep x, v)

theorem fcoef_slice (k : Lattice d) (g : Euc d × Euc d → ℝ) (hc : Continuous g) (hper : PerX g)
    (v : Euc d) :
    Torus.fcoef (Torus.descend fun x => g (x, v)) k =
      ((acF k g v : ℝ) : ℂ) - Complex.I * ((asF k g v : ℝ) : ℂ) := by
  have hcont : Continuous fun x : Torus d => g (Torus.rep x, v) := continuous_descend_first g hc hper v
  have hi1 : Integrable (fun x : Torus d => Torus.cosMode k x * g (Torus.rep x, v)) :=
    ((Torus.continuous_cosMode k).mul hcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun x : Torus d => Torus.sinMode k x * g (Torus.rep x, v)) :=
    ((Torus.continuous_sinMode k).mul hcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ x : Torus d, Torus.mode (-k) x * ((g (Torus.rep x, v) : ℝ) : ℂ) =
      ((Torus.cosMode k x * g (Torus.rep x, v) : ℝ) : ℂ) -
        Complex.I * ((Torus.sinMode k x * g (Torus.rep x, v) : ℝ) : ℂ) := by
    intro x
    rw [Torus.mode_neg]
    apply Complex.ext <;> simp [Torus.cosMode, Torus.sinMode]
  unfold Torus.fcoef Torus.descend
  simp_rw [hpt]
  rw [integral_sub hi1.ofReal (hi2.ofReal.const_mul _), integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal]
  rfl


theorem continuous_dX {g : Euc d × Euc d → ℝ} (hg : ContDiff ℝ 1 g) (e : Euc d) :
    Continuous (dX e g) :=
  (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem fderiv_slice (g : Euc d × Euc d → ℝ) (hg : ContDiff ℝ 1 g) (e v y : Euc d) :
    fderiv ℝ (fun x => g (x, v)) y e = dX e g (y, v) := by
  have h1 : HasFDerivAt (fun x : Euc d => (x, v))
      ((ContinuousLinearMap.id ℝ (Euc d)).prod (0 : Euc d →L[ℝ] Euc d)) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const v y)
  have h2 := ((hg.differentiable one_ne_zero) (y, v)).hasFDerivAt.comp y h1
  have h3 : fderiv ℝ (fun x => g (x, v)) y = _ := h2.fderiv
  rw [h3]
  simp [dX]

/-- Integration by parts in the first variable. -/
theorem acas_dX (k : Lattice d) (g : Euc d × Euc d → ℝ) (hg : ContDiff ℝ 1 g) (hper : PerX g)
    (e : Euc d) (v : Euc d) :
    acF k (dX e g) v = (2 * Real.pi * Lattice.dot k e) * asF k g v ∧
    asF k (dX e g) v = -((2 * Real.pi * Lattice.dot k e) * acF k g v) := by
  have hG : Torus.Per (fun x => g (x, v)) := by
    intro q m
    have := hper m (q, v)
    simpa using this
  have hGd : ContDiff ℝ 1 (fun x => g (x, v)) := hg.comp (contDiff_id.prodMk contDiff_const)
  have h1 := Torus.fcoef_fderiv hG hGd e k
  have e1 : (fun y => fderiv ℝ (fun x => g (x, v)) y e) = fun y => dX e g (y, v) := by
    funext y; exact fderiv_slice g hg e v y
  rw [e1] at h1
  rw [fcoef_slice k (dX e g) (continuous_dX hg e) (perX_dX hper e) v, fcoef_slice k g hg.continuous hper v] at h1
  have hre := congrArg Complex.re h1
  have him := congrArg Complex.im h1
  simp at hre him
  constructor
  · linarith
  · linarith


/-! ### Good functions and the sine/cosine slice integrals -/

/-- Supremum of the norm of the `i`-th derivative. -/
def supD (i : ℕ) (g : Euc d × Euc d → ℝ) : ℝ := ⨆ p, ‖iteratedFDeriv ℝ i g p‖

theorem supD_nonneg (i : ℕ) (g : Euc d × Euc d → ℝ) : 0 ≤ supD i g :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- `C^n`, periodic in both variables. -/
structure Good (n : ℕ) (g : Euc d × Euc d → ℝ) : Prop where
  contDiff : ContDiff ℝ n g
  px : PerX g
  py : PerY g

theorem Good.of_le {n m : ℕ} {g : Euc d × Euc d → ℝ} (h : Good n g) (hm : m ≤ n) : Good m g :=
  ⟨h.contDiff.of_le (by exact_mod_cast hm), h.px, h.py⟩

theorem Good.dX {n : ℕ} {g : Euc d × Euc d → ℝ} (h : Good (n + 1) g) (e : Euc d) :
    Good n (dX e g) :=
  ⟨contDiff_dX e h.contDiff, perX_dX h.px e, perY_dX h.py e⟩

theorem Good.le_supD {n : ℕ} {g : Euc d × Euc d → ℝ} (h : Good n g) {i : ℕ} (hi : i ≤ n)
    (p : Euc d × Euc d) : ‖iteratedFDeriv ℝ i g p‖ ≤ supD i g :=
  le_ciSup (f := fun p => ‖iteratedFDeriv ℝ i g p‖)
    (bddAbove_norm_iteratedFDeriv h.contDiff h.px h.py hi) p

theorem Good.slice {n : ℕ} {g : Euc d × Euc d → ℝ} (h : Good n g) (k : Lattice d) :
    ContDiff ℝ n (acF k g) ∧ ContDiff ℝ n (asF k g) ∧
    (∀ i ≤ n, ∀ v, ‖iteratedFDeriv ℝ i (acF k g) v‖ ≤ supD i g) ∧
    (∀ i ≤ n, ∀ v, ‖iteratedFDeriv ℝ i (asF k g) v‖ ≤ supD i g) := by
  have h1 := slice_integral_contDiff (Torus.cosMode k) (Torus.continuous_cosMode k)
    (fun x => by simpa using Torus.norm_cosMode_le k x) n g h.contDiff h.px (fun i => supD i g)
    (fun i hi p => h.le_supD hi p)
  have h2 := slice_integral_contDiff (Torus.sinMode k) (Torus.continuous_sinMode k)
    (fun x => by simpa using Torus.norm_sinMode_le k x) n g h.contDiff h.px (fun i => supD i g)
    (fun i hi p => h.le_supD hi p)
  exact ⟨h1.1, h2.1, h1.2, h2.2⟩

/-- Sum of the norms of the `i`-th derivatives of the cosine and sine slice integrals. -/
def Phi (k : Lattice d) (i : ℕ) (g : Euc d × Euc d → ℝ) (v : Euc d) : ℝ :=
  ‖iteratedFDeriv ℝ i (acF k g) v‖ + ‖iteratedFDeriv ℝ i (asF k g) v‖

theorem Phi_dX {n : ℕ} {g : Euc d × Euc d → ℝ} (h : Good (n + 1) g) (k : Lattice d) (e : Euc d)
    {i : ℕ} (hi : i ≤ n) (v : Euc d) :
    Phi k i (dX e g) v = |2 * Real.pi * Lattice.dot k e| * Phi k i g v := by
  set μ : ℝ := 2 * Real.pi * Lattice.dot k e with hμ
  obtain ⟨hc, hs, -, -⟩ := h.slice k
  have e1 : acF k (dX e g) = μ • asF k g := by
    funext w; exact (acas_dX k g (h.contDiff.of_le (by exact_mod_cast Nat.le_add_left 1 n)) h.px e w).1
  have e2 : asF k (dX e g) = (-μ) • acF k g := by
    funext w
    have := (acas_dX k g (h.contDiff.of_le (by exact_mod_cast Nat.le_add_left 1 n)) h.px e w).2
    simpa using this
  have hi' : (i : WithTop ℕ∞) ≤ ((n + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast Nat.le_succ_of_le hi
  unfold Phi
  rw [e1, e2, iteratedFDeriv_const_smul_apply ((hs.of_le hi').contDiffAt),
    iteratedFDeriv_const_smul_apply ((hc.of_le hi').contDiffAt), norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
  ring

theorem Phi_dXn (k : Lattice d) (e : Euc d) : ∀ (N : ℕ) (g : Euc d × Euc d → ℝ) (n : ℕ),
    Good (n + N) g → ∀ i ≤ n, ∀ v,
      Phi k i (dXn e N g) v = |2 * Real.pi * Lattice.dot k e| ^ N * Phi k i g v := by
  intro N
  induction N with
  | zero => intro g n _ i _ v; simp [dXn]
  | succ N ih =>
    intro g n hg i hi v
    have hg' : Good (n + N + 1) g := by
      have : n + (N + 1) = n + N + 1 := by ring
      rwa [this] at hg
    have h1 := ih (dX e g) n (hg'.dX e) i hi v
    have h2 := Phi_dX (n := n + N) hg' k e (i := i) (by omega) v
    show Phi k i (dXn e N (dX e g)) v = _
    rw [h1, h2, pow_succ]
    ring


/-! ### Decay of the slice integrals in `k` -/

theorem enorm_pos_of_ne (k : Lattice d) (hk : k ≠ 0) : 0 < Lattice.enorm k := by
  have h1 := Torus.jp_ge_one k
  have h2 := jp_le_enorm (⟨k, hk⟩ : NonzeroLattice d)
  simp only at h2
  have := Real.pi_pos
  nlinarith

theorem slice_norm_bound (N n : ℕ) (g : Euc d × Euc d → ℝ) (hg : Good (n + N) g)
    (k : Lattice d) (hk : k ≠ 0) {i : ℕ} (hi : i ≤ n) (v : Euc d) :
    ‖iteratedFDeriv ℝ i (acF k g) v‖ ≤
      2 * (((1 + 2 * Real.pi) / (2 * Real.pi)) ^ N * (Lattice.jp k ^ N)⁻¹) * supD (i + N) g ∧
    ‖iteratedFDeriv ℝ i (asF k g) v‖ ≤
      2 * (((1 + 2 * Real.pi) / (2 * Real.pi)) ^ N * (Lattice.jp k ^ N)⁻¹) * supD (i + N) g := by
  have hpi := Real.pi_pos
  have hk0 := enorm_pos_of_ne k hk
  set e : Euc d := (Lattice.enorm k)⁻¹ • Lattice.toEuc k with he
  have hne : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hk0]
    exact inv_mul_cancel₀ hk0.ne'
  have hdot : Lattice.dot k e = Lattice.enorm k := by
    rw [Torus.dot_eq_inner, he, real_inner_smul_right, real_inner_self_eq_norm_sq]
    unfold Lattice.enorm
    field_simp
  set μ : ℝ := 2 * Real.pi * Lattice.dot k e with hμ
  have hμpos : 0 < μ := by rw [hμ, hdot]; positivity
  set K : ℝ := (1 + 2 * Real.pi) / (2 * Real.pi) with hK
  have hKpos : 0 < K := by positivity
  have hjp := Torus.jp_pos k
  have hjple : Lattice.jp k ≤ K * μ := by
    have := jp_le_enorm (⟨k, hk⟩ : NonzeroLattice d)
    simp only at this
    rw [hμ, hdot, hK]
    calc Lattice.jp k ≤ (1 + 2 * Real.pi) * Lattice.enorm k := this
      _ = _ := by field_simp
  -- the derivative bound for `dXn e N g`
  obtain ⟨hcd, hder⟩ := dXn_spec e N g n (by exact_mod_cast hg.contDiff)
  have hB : ∀ j ≤ n, ∀ p, ‖iteratedFDeriv ℝ j (dXn e N g) p‖ ≤ ‖e‖ ^ N * supD (j + N) g := by
    intro j hj p
    refine (hder j hj p).trans ?_
    exact mul_le_mul_of_nonneg_left (hg.le_supD (by omega) p) (by positivity)
  have hpx : PerX (dXn e N g) := perX_dXn e N g hg.px
  have h1 := slice_integral_contDiff (Torus.cosMode k) (Torus.continuous_cosMode k)
    (fun x => by simpa using Torus.norm_cosMode_le k x) n (dXn e N g) hcd hpx
    (fun j => ‖e‖ ^ N * supD (j + N) g) hB
  have h2 := slice_integral_contDiff (Torus.sinMode k) (Torus.continuous_sinMode k)
    (fun x => by simpa using Torus.norm_sinMode_le k x) n (dXn e N g) hcd hpx
    (fun j => ‖e‖ ^ N * supD (j + N) g) hB
  have hPhi : Phi k i (dXn e N g) v ≤ 2 * supD (i + N) g := by
    unfold Phi
    have a1 : ‖iteratedFDeriv ℝ i (acF k (dXn e N g)) v‖ ≤ ‖e‖ ^ N * supD (i + N) g := h1.2 i hi v
    have a2 : ‖iteratedFDeriv ℝ i (asF k (dXn e N g)) v‖ ≤ ‖e‖ ^ N * supD (i + N) g := h2.2 i hi v
    simp only [hne, one_pow, one_mul] at a1 a2
    linarith
  rw [Phi_dXn k e N g n hg i hi v, abs_of_pos hμpos] at hPhi
  -- `μ^N * Phi ≤ 2 supD`
  have hμN : 0 < μ ^ N := pow_pos hμpos N
  have hcomp : (μ ^ N)⁻¹ ≤ K ^ N * (Lattice.jp k ^ N)⁻¹ := by
    have h : Lattice.jp k ^ N ≤ K ^ N * μ ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hjp.le hjple N
    have h2 : (K ^ N * μ ^ N)⁻¹ ≤ (Lattice.jp k ^ N)⁻¹ := inv_anti₀ (pow_pos hjp N) h
    calc (μ ^ N)⁻¹ = K ^ N * (K ^ N * μ ^ N)⁻¹ := by
          have : K ^ N ≠ 0 := (pow_pos hKpos N).ne'
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hsup : 0 ≤ supD (i + N) g := supD_nonneg _ _
  have key : ∀ t : ℝ, 0 ≤ t → μ ^ N * t ≤ 2 * supD (i + N) g →
      t ≤ 2 * (K ^ N * (Lattice.jp k ^ N)⁻¹) * supD (i + N) g := by
    intro t ht htb
    have h3 : t ≤ (μ ^ N)⁻¹ * (2 * supD (i + N) g) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hμN]; linarith
    calc t ≤ (μ ^ N)⁻¹ * (2 * supD (i + N) g) := h3
      _ ≤ (K ^ N * (Lattice.jp k ^ N)⁻¹) * (2 * supD (i + N) g) :=
          mul_le_mul_of_nonneg_right hcomp (by positivity)
      _ = _ := by ring
  have hn1 := norm_nonneg (iteratedFDeriv ℝ i (acF k g) v)
  have hn2 := norm_nonneg (iteratedFDeriv ℝ i (asF k g) v)
  refine ⟨key _ hn1 ?_, key _ hn2 ?_⟩
  · unfold Phi at hPhi; nlinarith
  · unfold Phi at hPhi; nlinarith


theorem sliceCoeff_mk (R : Torus d → Torus d → ℝ) (hR : Continuous (lift2 R)) (k : Lattice d)
    (v : Euc d) :
    sliceCoeff R k (Torus.mk v) =
      ((acF k (lift2 R) v : ℝ) : ℂ) - Complex.I * ((asF k (lift2 R) v : ℝ) : ℂ) := by
  have e : (fun x => R x (Torus.mk v)) = Torus.descend fun x => lift2 R (x, v) := by
    funext x
    simp [Torus.descend, lift2, Torus.mk_rep]
  unfold sliceCoeff
  rw [coeffOf_eq_fcoef, e]
  exact fcoef_slice k (lift2 R) hR (perX_lift2 R) v

theorem re_sliceCoeff_lift (R : Torus d → Torus d → ℝ) (hR : Continuous (lift2 R)) (k : Lattice d) :
    Torus.lift (fun y => (sliceCoeff R k y).re) = acF k (lift2 R) := by
  funext v
  simp [Torus.lift, sliceCoeff_mk R hR k v]

theorem im_sliceCoeff_lift (R : Torus d → Torus d → ℝ) (hR : Continuous (lift2 R)) (k : Lattice d) :
    Torus.lift (fun y => (sliceCoeff R k y).im) = -(asF k (lift2 R)) := by
  funext v
  simp [Torus.lift, sliceCoeff_mk R hR k v]

theorem cbNorm2_eq_sum (J : ℕ) (R : Torus d → Torus d → ℝ) :
    cbNorm2 J R = ∑ j ∈ Finset.range (J + 1), supD j (lift2 R) := rfl

theorem sum_supD_shift_le (g : Euc d × Euc d → ℝ) (n N J : ℕ) (hJ : n + N ≤ J) :
    ∑ i ∈ Finset.range (n + 1), supD (i + N) g ≤ ∑ j ∈ Finset.range (J + 1), supD j g := by
  have h1 : ∑ i ∈ Finset.range (n + 1), supD (i + N) g =
      ∑ j ∈ (Finset.range (n + 1)).image (fun i => i + N), supD j g := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    simpa using hab
  rw [h1]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => supD_nonneg _ _)
  intro j hj
  simp only [Finset.mem_image, Finset.mem_range] at hj ⊢
  obtain ⟨i, hi, rfl⟩ := hj
  omega

/-- P12a: slice coefficients of a `C^J` kernel are `C^n` in `y` with decay `⟨k⟩^{-N}` for
`n + N ≤ J`. -/
theorem exists_sliceCoeff_bound (n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : ℕ), n + N ≤ J → ∀ R : Torus d → Torus d → ℝ, IsCk2 J R →
      ∀ k : Lattice d,
        Torus.IsCk n (fun y => (sliceCoeff R k y).re) ∧
        Torus.IsCk n (fun y => (sliceCoeff R k y).im) ∧
        Torus.cbNorm n (fun y => (sliceCoeff R k y).re) ≤ C * cbNorm2 J R * Lattice.jp k ^ (-(N : ℝ)) ∧
        Torus.cbNorm n (fun y => (sliceCoeff R k y).im) ≤ C * cbNorm2 J R * Lattice.jp k ^ (-(N : ℝ)) := by
  have hpi := Real.pi_pos
  refine ⟨2 * (((1 + 2 * Real.pi) / (2 * Real.pi)) ^ N), by positivity, ?_⟩
  intro J hJ R hR k
  have hgood : Good J (lift2 R) := ⟨hR, perX_lift2 R, perY_lift2 R⟩
  have hcont : Continuous (lift2 R) := hR.continuous
  have hgn : Good n (lift2 R) := hgood.of_le (by omega)
  obtain ⟨hc, hs, hcb, hsb⟩ := hgn.slice k
  have hre := re_sliceCoeff_lift R hcont k
  have him := im_sliceCoeff_lift R hcont k
  have hS : 0 ≤ cbNorm2 J R := by
    rw [cbNorm2_eq_sum]; exact Finset.sum_nonneg fun j _ => supD_nonneg _ _
  -- the common bound for the sup of the `i`-th derivative norms
  have main : ∀ (F : Euc d → ℝ), (∀ i ≤ n, ∀ v, ‖iteratedFDeriv ℝ i F v‖ ≤ supD i (lift2 R)) →
      (k ≠ 0 → ∀ i ≤ n, ∀ v, ‖iteratedFDeriv ℝ i F v‖ ≤
        2 * ((((1 + 2 * Real.pi) / (2 * Real.pi)) ^ N * (Lattice.jp k ^ N)⁻¹)) *
          supD (i + N) (lift2 R)) →
      ∑ i ∈ Finset.range (n + 1), ⨆ v, ‖iteratedFDeriv ℝ i F v‖ ≤
        2 * (((1 + 2 * Real.pi) / (2 * Real.pi)) ^ N) * cbNorm2 J R * Lattice.jp k ^ (-(N : ℝ)) := by
    intro F h0 h1
    by_cases hk : k = 0
    · subst hk
      have hjp : Lattice.jp (0 : Lattice d) ^ (-(N : ℝ)) = 1 := by
        rw [Torus.jp_zero]; simp
      rw [hjp, mul_one]
      calc ∑ i ∈ Finset.range (n + 1), ⨆ v, ‖iteratedFDeriv ℝ i F v‖
          ≤ ∑ i ∈ Finset.range (n + 1), supD i (lift2 R) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            exact Real.iSup_le (fun v => h0 i hi' v) (supD_nonneg _ _)
        _ ≤ cbNorm2 J R := by
            rw [cbNorm2_eq_sum]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => supD_nonneg _ _)
            intro j hj
            simp only [Finset.mem_range] at hj ⊢
            omega
        _ ≤ _ := by
            have : (1 : ℝ) ≤ 2 * (((1 + 2 * Real.pi) / (2 * Real.pi)) ^ N) := by
              have h1 : (1 : ℝ) ≤ (1 + 2 * Real.pi) / (2 * Real.pi) := by
                rw [le_div_iff₀ (by positivity)]; linarith
              have := one_le_pow₀ (n := N) h1
              linarith
            nlinarith
    · have hjpos : 0 < Lattice.jp k := Torus.jp_pos k
      have hjp : Lattice.jp k ^ (-(N : ℝ)) = (Lattice.jp k ^ N)⁻¹ := by
        rw [Real.rpow_neg (Torus.jp_pos k).le, Real.rpow_natCast]
      rw [hjp]
      calc ∑ i ∈ Finset.range (n + 1), ⨆ v, ‖iteratedFDeriv ℝ i F v‖
          ≤ ∑ i ∈ Finset.range (n + 1), 2 * ((((1 + 2 * Real.pi) / (2 * Real.pi)) ^ N *
              (Lattice.jp k ^ N)⁻¹)) * supD (i + N) (lift2 R) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            exact Real.iSup_le (fun v => h1 hk i hi' v)
              (mul_nonneg (by positivity) (supD_nonneg _ _))
        _ = 2 * ((((1 + 2 * Real.pi) / (2 * Real.pi)) ^ N * (Lattice.jp k ^ N)⁻¹)) *
              ∑ i ∈ Finset.range (n + 1), supD (i + N) (lift2 R) := by
            rw [Finset.mul_sum]
        _ ≤ 2 * ((((1 + 2 * Real.pi) / (2 * Real.pi)) ^ N * (Lattice.jp k ^ N)⁻¹)) *
              cbNorm2 J R := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [cbNorm2_eq_sum]
            exact sum_supD_shift_le _ n N J hJ
        _ = _ := by ring
  have hsl : k ≠ 0 → ∀ i ≤ n, ∀ v,
      ‖iteratedFDeriv ℝ i (acF k (lift2 R)) v‖ ≤
        2 * ((((1 + 2 * Real.pi) / (2 * Real.pi)) ^ N * (Lattice.jp k ^ N)⁻¹)) *
          supD (i + N) (lift2 R) ∧
      ‖iteratedFDeriv ℝ i (asF k (lift2 R)) v‖ ≤
        2 * ((((1 + 2 * Real.pi) / (2 * Real.pi)) ^ N * (Lattice.jp k ^ N)⁻¹)) *
          supD (i + N) (lift2 R) := by
    intro hk i hi v
    exact slice_norm_bound N n (lift2 R) (hgood.of_le hJ) k hk hi v
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Torus.IsCk; rw [hre]; exact hc
  · unfold Torus.IsCk; rw [him]; exact hs.neg
  · unfold Torus.cbNorm
    rw [hre]
    exact main _ hcb (fun hk i hi v => (hsl hk i hi v).1)
  · unfold Torus.cbNorm
    rw [him]
    refine main _ (fun i hi v => ?_) (fun hk i hi v => ?_)
    · rw [show (-(asF k (lift2 R)) : Euc d → ℝ) = (-1 : ℝ) • asF k (lift2 R) by
        funext w; simp,
        iteratedFDeriv_const_smul_apply (hs.contDiffAt (x := v) |>.of_le (by exact_mod_cast hi)), norm_smul]
      simpa using hsb i hi v
    · rw [show (-(asF k (lift2 R)) : Euc d → ℝ) = (-1 : ℝ) • asF k (lift2 R) by
        funext w; simp,
        iteratedFDeriv_const_smul_apply (hs.contDiffAt (x := v) |>.of_le (by exact_mod_cast hi)), norm_smul]
      simpa using (hsl hk i hi v).2


/-! ### Reconstruction of a `C^J` function from its slice coefficients -/

theorem continuous_toFun' (c : Coeff d) (hs : Summable fun k => ‖c k‖) : Continuous (toFun c) := by
  unfold toFun series
  refine Complex.continuous_re.comp ?_
  exact continuous_tsum (u := fun k => ‖c k‖)
    (fun k => continuous_const.mul (Torus.continuous_mode k)) hs
    (fun k x => by simp [Torus.norm_mode])

theorem toFun_coeffOf' {φ : Torus d → ℝ} (hφ : Continuous φ)
    (hs : Summable fun k => ‖coeffOf φ k‖) : toFun (coeffOf φ) = φ := by
  have hr : IsRealCoeff (coeffOf φ) :=
    isRealCoeff_coeffOf φ (MFThermal.integrable_of_continuous hφ)
  have h1 := coeffOf_toFun (coeffOf φ) hr hs
  exact MFAux.eq_of_funFourierCoeff_eq (continuous_toFun' _ hs) hφ (fun k => by
    have := congrFun h1 k
    exact this)

/-- `C^n` functions have coefficients in `H^n`. -/
theorem memHs_of_isCk' : ∀ (n : ℕ) (b : Torus d → ℝ), Torus.IsCk (n : WithTop ℕ∞) b →
    MemHs (n : ℝ) (coeffOf b)
  | 0, b, hb => by
    have hc : Continuous b := continuous_of_lift' hb.continuous
    simpa using (coeffOf_memHs_zero hc).1
  | n + 1, b, hb => by
    have hb1 : Torus.IsCk 1 b := hb.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hbn : Torus.IsCk (n : WithTop ℕ∞) b := hb.of_le (by exact_mod_cast Nat.le_succ n)
    have e : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [e, ProdAux.memHs_succ_iff]
    refine ⟨memHs_of_isCk' n b hbn, fun j => ?_⟩
    rw [← coeffOf_partialDeriv_eq j b hb1]
    exact memHs_of_isCk' n _ (ProdAux.isCk_partialDeriv hb j)

theorem isCk_slice (J : ℕ) (R : Torus d → Torus d → ℝ) (hR : IsCk2 J R) (y : Torus d) :
    Torus.IsCk (J : WithTop ℕ∞) (fun x => R x y) := by
  have e : Torus.lift (fun x => R x y) = fun u => lift2 R (u, Torus.rep y) := by
    funext u
    simp [Torus.lift, lift2, Torus.mk_rep]
  unfold Torus.IsCk
  rw [e]
  exact hR.comp (contDiff_id.prodMk contDiff_const)

/-- P12a: reconstruction `R(x,y) = ∑_k Re(R̂(k;y) e_k(x))`. -/
theorem eq_toFun_sliceCoeff (J : ℕ) (hJ : (d : ℝ) / 2 < J) (R : Torus d → Torus d → ℝ)
    (hR : IsCk2 J R) (x y : Torus d) :
    R x y = toFun (fun k => sliceCoeff R k y) x ∧
      Summable fun k : Lattice d => ‖sliceCoeff R k y‖ := by
  have hb := isCk_slice J R hR y
  have hs : Summable fun k : Lattice d => ‖coeffOf (fun x => R x y) k‖ :=
    summable_norm_of_memHs (J : ℝ) hJ _ (memHs_of_isCk' J _ hb)
  refine ⟨?_, hs⟩
  have := toFun_coeffOf' (continuous_of_lift' hb.continuous) hs
  exact (congrFun this x).symm


/-! ### Centering of the slice coefficients -/

theorem continuous_pair_of_continuous_lift2 {Φ : Torus d → Torus d → ℝ} (h : Continuous (lift2 Φ)) :
    Continuous (fun p : Torus d × Torus d => Φ p.1 p.2) := by
  let K : Set (Euc d) := (WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1)
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  have hK2 : IsCompact (K ×ˢ K) := hK.prod hK
  let f : (K ×ˢ K : Set (Euc d × Euc d)) → Torus d × Torus d :=
    fun x => (Torus.mk x.1.1, Torus.mk x.1.2)
  have hf : Continuous f :=
    ((Torus.continuous_mk.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (Torus.continuous_mk.comp (continuous_snd.comp continuous_subtype_val)))
  have : CompactSpace (K ×ˢ K : Set (Euc d × Euc d)) := isCompact_iff_compactSpace.mp hK2
  have hrep : ∀ x : Torus d, Torus.rep x ∈ K := by
    intro x
    refine ⟨fun i => Torus.rep x i, fun i _ => ?_, rfl⟩
    have := (AddCircle.equivIco (1 : ℝ) 0 (x i)).2
    simp only [zero_add] at this
    exact ⟨this.1, this.2.le⟩
  have hsurj : Function.Surjective f := by
    intro x
    refine ⟨⟨(Torus.rep x.1, Torus.rep x.2), hrep _, hrep _⟩, ?_⟩
    simp [f, Torus.mk_rep]
  have hq : Topology.IsQuotientMap f := hf.isClosedMap.isQuotientMap hf hsurj
  rw [hq.continuous_iff]
  exact h.comp continuous_subtype_val

theorem re_sliceCoeff_eq (R : Torus d → Torus d → ℝ) (hR : Continuous (lift2 R)) (k : Lattice d)
    (y : Torus d) :
    (sliceCoeff R k y).re = ∫ x : Torus d, Torus.cosMode k x * R x y := by
  have := sliceCoeff_mk R hR k (Torus.rep y)
  rw [Torus.mk_rep] at this
  rw [this]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, zero_mul, sub_zero, mul_zero, sub_self, acF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [lift2, Torus.mk_rep]

theorem im_sliceCoeff_eq (R : Torus d → Torus d → ℝ) (hR : Continuous (lift2 R)) (k : Lattice d)
    (y : Torus d) :
    (sliceCoeff R k y).im = -∫ x : Torus d, Torus.sinMode k x * R x y := by
  have := sliceCoeff_mk R hR k (Torus.rep y)
  rw [Torus.mk_rep] at this
  rw [this]
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.ofReal_re,
    Complex.I_im, zero_mul, one_mul, zero_sub, asF, zero_add]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [lift2, Torus.mk_rep]

theorem integral_weight_slice_eq_zero (R : Torus d → Torus d → ℝ)
    (hRc : Continuous fun p : Torus d × Torus d => R p.1 p.2) (ρβ : Torus d → ℝ)
    (hρc : Continuous ρβ) (w : Torus d → ℝ) (hw : Continuous w)
    (hcen : ∀ x, ∫ y : Torus d, ρβ y * R x y = 0) :
    ∫ y : Torus d, ρβ y * ∫ x : Torus d, w x * R x y = 0 := by
  have hint : Integrable (Function.uncurry fun (y x : Torus d) => ρβ y * (w x * R x y))
      ((volume : Measure (Torus d)).prod (volume : Measure (Torus d))) := by
    have hc : Continuous (Function.uncurry fun (y x : Torus d) => ρβ y * (w x * R x y)) :=
      (hρc.comp continuous_fst).mul ((hw.comp continuous_snd).mul (hRc.comp continuous_swap))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e1 : ∀ y : Torus d, ρβ y * ∫ x : Torus d, w x * R x y =
      ∫ x : Torus d, ρβ y * (w x * R x y) := fun y => (integral_const_mul _ _).symm
  simp_rw [e1]
  rw [integral_integral_swap (f := fun y x => ρβ y * (w x * R x y)) hint]
  have e2 : ∀ x : Torus d, ∫ y : Torus d, ρβ y * (w x * R x y) = w x * ∫ y : Torus d, ρβ y * R x y := by
    intro x
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  simp_rw [e2, hcen, mul_zero, integral_zero]

/-- P12a: a doubly centered kernel has `μβ`-centered slice coefficients in `y`. -/
theorem sliceCoeff_centered (J : ℕ) (hJ : (d : ℝ) / 2 < J) (R : Torus d → Torus d → ℝ)
    (hR : IsCk2 J R) (ρβ : Torus d → ℝ) (hρ : IsProbDensity ρβ) (hρc : Continuous ρβ)
    (hcen : DoublyCentered (withDensityReal ρβ) R) (k : Lattice d) :
    pair (withDensityReal ρβ) (fun y => (sliceCoeff R k y).re) = 0 ∧
      pair (withDensityReal ρβ) (fun y => (sliceCoeff R k y).im) = 0 := by
  have _ := hJ
  have hcont : Continuous (lift2 R) := hR.continuous
  have hRc := continuous_pair_of_continuous_lift2 hcont
  have hc2 : ∀ x : Torus d, ∫ y : Torus d, ρβ y * R x y = 0 := by
    intro x
    have := hcen.2 x
    unfold pair at this
    rwa [integral_withDensityReal_eq ρβ hρ.measurable hρ.nonneg] at this
  unfold pair
  rw [integral_withDensityReal_eq ρβ hρ.measurable hρ.nonneg,
    integral_withDensityReal_eq ρβ hρ.measurable hρ.nonneg]
  constructor
  · simp_rw [re_sliceCoeff_eq R hcont k]
    exact integral_weight_slice_eq_zero R hRc ρβ hρc _ (Torus.continuous_cosMode k) hc2
  · simp_rw [im_sliceCoeff_eq R hcont k, mul_neg, integral_neg]
    rw [integral_weight_slice_eq_zero R hRc ρβ hρc _ (Torus.continuous_sinMode k) hc2, neg_zero]

end HRS.PDE.MFPair
