import HRS.Energy.Commutator.Smear

/-!
# Auxiliary lemmas for `Stress.lean` (packet CM-S3)

Calculus on the torus with Lipschitz fields: the basic estimate `|∫ ψ ∂_iφ| ≤ L ∫|φ|` for a
Lipschitz scalar `ψ` (constant `L`) and `φ ∈ C¹`, proved by translation (no mollification), and the
stress-tensor bound `stress_regular`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.StressAux

variable {d : ℕ}

/-- The point `t e_i` of the torus. -/
def tr (i : Fin d) (t : ℝ) : Torus d := Torus.mk (t • (EuclideanSpace.single i 1 : Euc d))

theorem tr_zero (i : Fin d) : tr i 0 = 0 := by
  funext j
  simp [tr, Torus.mk]

theorem tdist_tr (i : Fin d) {t : ℝ} (ht : |t| ≤ 1 / 2) : KernelGrad.tdist (tr i t) 0 = |t| := by
  unfold tr
  rw [KernelGrad.tdist_mk]
  · rw [norm_smul]; simp
  · intro j
    simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
    split_ifs
    · simpa using ht
    · simp

theorem lift_add_tr (H : Torus d → ℝ) (x : Torus d) (i : Fin d) (t : ℝ) :
    Torus.lift H (Torus.rep x + t • (EuclideanSpace.single i 1 : Euc d)) = H (x + tr i t) := by
  simp [Torus.lift, Torus.mk_add, Torus.mk_rep, tr]


theorem hasDerivAt_translate (i : Fin d) (G φ : Torus d → ℝ) (hG : Continuous G)
    (hφ : Torus.IsCk 1 φ) :
    HasDerivAt (fun t : ℝ => ∫ x, G x * φ (x + tr i t)) (∫ x, G x * Torus.partialDeriv i φ x) 0 := by
  set e : Euc d := EuclideanSpace.single i 1 with he
  have hHc : Continuous φ := HRS.Torus.continuous_of_continuous_lift hφ.continuous
  have hGc := HRS.PDE.continuous_partialDeriv i φ hφ
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖Torus.partialDeriv i φ x‖ ≤ C := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hGc.continuousOn
    exact ⟨C, fun x => hC x (Set.mem_univ x)⟩
  obtain ⟨B, hB⟩ : ∃ B, ∀ x, ‖G x‖ ≤ B := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hG.continuousOn
    exact ⟨C, fun x => hC x (Set.mem_univ x)⟩
  have hF' : ∀ t x, fderiv ℝ (Torus.lift φ) (Torus.rep x + t • e) e =
      Torus.partialDeriv i φ (x + tr i t) := by
    intro t x
    have := HRS.PDE.partialDeriv_mk i φ hφ (Torus.rep x + t • e)
    rw [he, ← this]
    congr 1
    simp [Torus.mk_add, Torus.mk_rep, tr, he]
  have hcont : ∀ t, Continuous fun x : Torus d => G x * φ (x + tr i t) := fun t => by
    have : Continuous fun x : Torus d => φ (x + tr i t) := hHc.comp (continuous_id.add continuous_const)
    exact hG.mul this
  have hcont' : ∀ t, Continuous fun x : Torus d => G x * Torus.partialDeriv i φ (x + tr i t) :=
    fun t => hG.mul (hGc.comp (continuous_id.add continuous_const))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Torus d)))
    (𝕜 := ℝ) (x₀ := 0) (s := Set.univ) (F := fun t x => G x * φ (x + tr i t))
    (F' := fun t x => G x * Torus.partialDeriv i φ (x + tr i t)) (bound := fun _ => B * C)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hcont t).aestronglyMeasurable)
    ((hcont 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hcont' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t _ => by
      rw [norm_mul]
      exact mul_le_mul (hB x) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hB x)))
    (integrable_const _)
    (Filter.Eventually.of_forall fun x t _ => by
      have h1 : HasDerivAt (fun t : ℝ => Torus.rep x + t • e) e t := by
        simpa using ((hasDerivAt_id t).smul_const e).const_add (Torus.rep x)
      have h2 : DifferentiableAt ℝ (Torus.lift φ) (Torus.rep x + t • e) :=
        (hφ.differentiable one_ne_zero) _
      have h3 := h2.hasFDerivAt.comp_hasDerivAt t h1
      have h4 : (fun t : ℝ => φ (x + tr i t)) = (Torus.lift φ) ∘ fun t : ℝ => Torus.rep x + t • e := by
        funext t; exact (lift_add_tr φ x i t).symm
      have h5 := h3.const_mul (G x)
      rw [← h4, hF' t x] at h5
      exact h5)
  have := key.2
  simpa [tr_zero] using this


theorem lipA {L : ℝ} (hL : 0 ≤ L) (ψ : Torus d → ℝ) (hψ : ∀ x y, |ψ x - ψ y| ≤ L * KernelGrad.tdist x y)
    (φ : Torus d → ℝ) (hφ : Torus.IsCk 1 φ) (i : Fin d) :
    |∫ x, ψ x * Torus.partialDeriv i φ x| ≤ L * ∫ x, |φ x| := by
  have hψc : Continuous ψ := CoercAux.continuous_of_isLipschitz_aux (L := L) hψ
  have hφc : Continuous φ := HRS.Torus.continuous_of_continuous_lift hφ.continuous
  have h := hasDerivAt_translate i ψ φ hψc hφ
  have hint : Integrable (fun x : Torus d => |φ x|) :=
    hφc.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlip : ∀ᶠ t in 𝓝 (0 : ℝ), ‖(∫ x, ψ x * φ (x + tr i t)) - ∫ x, ψ x * φ (x + tr i 0)‖ ≤
      (L * ∫ x, |φ x|) * ‖t - 0‖ := by
    have : Metric.ball (0 : ℝ) (1 / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [this] with t ht
    have ht' : |t| ≤ 1 / 2 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht; exact ht.le
    have e1 : ∫ x, ψ x * φ (x + tr i t) = ∫ x, ψ (x - tr i t) * φ x := by
      have := integral_add_right_eq_self (μ := (volume : Measure (Torus d)))
        (fun y => ψ (y - tr i t) * φ y) (tr i t)
      simpa using this
    rw [e1, tr_zero]
    simp only [add_zero, Real.norm_eq_abs, sub_zero]
    have hc1 : Continuous fun x : Torus d => ψ (x - tr i t) * φ x :=
      (hψc.comp (continuous_id.sub continuous_const)).mul hφc
    have hi1 : Integrable fun x : Torus d => ψ (x - tr i t) * φ x :=
      hc1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi2 : Integrable fun x : Torus d => ψ x * φ x :=
      (hψc.mul hφc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← integral_sub hi1 hi2]
    calc |∫ x, (ψ (x - tr i t) * φ x - ψ x * φ x)|
        ≤ ∫ x, ‖ψ (x - tr i t) * φ x - ψ x * φ x‖ := by
          simpa using norm_integral_le_integral_norm (μ := (volume : Measure (Torus d)))
            (fun x => ψ (x - tr i t) * φ x - ψ x * φ x)
      _ ≤ ∫ x, (L * |t|) * |φ x| := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
            (hint.const_mul _) (Eventually.of_forall fun x => ?_)
          simp only []
          rw [← sub_mul, Real.norm_eq_abs, abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          refine (hψ _ _).trans (le_of_eq ?_)
          have : KernelGrad.tdist (x - tr i t) x = KernelGrad.tdist (-tr i t) 0 := by
            unfold KernelGrad.tdist; rw [sub_sub_cancel_left, sub_zero]
          rw [this, KernelGrad.tdist_neg, tdist_tr i ht']
      _ = (L * ∫ x, |φ x|) * |t| := by
          rw [integral_const_mul]; ring
  have := h.le_of_lip' (mul_nonneg hL (integral_nonneg fun x => abs_nonneg _)) hlip
  simpa using this


theorem pd_mul {a b : Torus d → ℝ} (ha : Torus.IsCk 1 a) (hb : Torus.IsCk 1 b) (i : Fin d)
    (x : Torus d) :
    Torus.partialDeriv i (fun y => a y * b y) x =
      Torus.partialDeriv i a x * b x + a x * Torus.partialDeriv i b x := by
  have e1 : Torus.lift (fun y => a y * b y) = fun y => Torus.lift a y * Torus.lift b y := rfl
  unfold Torus.partialDeriv
  rw [e1, fderiv_fun_mul ((ha.differentiable one_ne_zero) _) ((hb.differentiable one_ne_zero) _)]
  simp [Torus.lift, Torus.mk_rep]
  ring

theorem pd_sum {ι : Type*} (s : Finset ι) {f : ι → Torus d → ℝ} (hf : ∀ k, Torus.IsCk 1 (f k))
    (i : Fin d) (x : Torus d) :
    Torus.partialDeriv i (fun y => ∑ k ∈ s, f k y) x = ∑ k ∈ s, Torus.partialDeriv i (f k) x := by
  have h : ∀ k ∈ s, HasFDerivAt (Torus.lift (f k)) (fderiv ℝ (Torus.lift (f k)) (Torus.rep x))
      (Torus.rep x) := fun k _ => ((hf k).differentiable one_ne_zero _).hasFDerivAt
  have := HasFDerivAt.fun_sum h
  have e1 : Torus.lift (fun y => ∑ k ∈ s, f k y) = fun y => ∑ k ∈ s, Torus.lift (f k) y := rfl
  unfold Torus.partialDeriv
  rw [e1, this.fderiv]
  simp

theorem isCk_sum {ι : Type*} (s : Finset ι) {f : ι → Torus d → ℝ} (hf : ∀ k, Torus.IsCk 1 (f k)) :
    Torus.IsCk 1 (fun y => ∑ k ∈ s, f k y) :=
  ContDiff.sum fun k _ => hf k

theorem pd_symm {h : Torus d → ℝ} (hh : Torus.IsCk 2 h) (i j : Fin d) (x : Torus d) :
    Torus.partialDeriv i (Torus.partialDeriv j h) x = Torus.partialDeriv j (Torus.partialDeriv i h) x := by
  have h1 : Torus.IsCk 1 h := hh.of_le (by norm_num)
  have key : ∀ i j : Fin d, Torus.partialDeriv i (Torus.partialDeriv j h) x =
      fderiv ℝ (fderiv ℝ (Torus.lift h)) (Torus.rep x) (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) := by
    intro i j
    have hd : DifferentiableAt ℝ (fderiv ℝ (Torus.lift h)) (Torus.rep x) :=
      ((hh.fderiv_right (by norm_num) : ContDiff ℝ 1 (fderiv ℝ (Torus.lift h)))).differentiable
        one_ne_zero _
    have e : Torus.partialDeriv i (Torus.partialDeriv j h) x =
        fderiv ℝ (Torus.lift (Torus.partialDeriv j h)) (Torus.rep x) (EuclideanSpace.single i 1) := rfl
    rw [e, HRS.PDE.lift_partialDeriv j h h1, fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [key, key]
  have hs : IsSymmSndFDerivAt ℝ (Torus.lift h) (Torus.rep x) :=
    (hh.contDiffAt).isSymmSndFDerivAt (by simp)
  exact hs _ _

theorem grad_apply (f : Torus d → ℝ) (x : Torus d) (j : Fin d) :
    Torus.grad f x j = Torus.partialDeriv j f x := by
  unfold Torus.grad Torus.partialDeriv
  have h1 := EuclideanSpace.inner_single_right j (1 : ℝ) (gradient (Torus.lift f) (Torus.rep x))
  have h2 := InnerProductSpace.toDual_symm_apply (x := EuclideanSpace.single j (1 : ℝ))
    (y := fderiv ℝ (Torus.lift f) (Torus.rep x))
  simp only [one_mul, RCLike.conj_to_real] at h1
  rw [← h1]
  exact h2


theorem int_of_cont {f : Torus d → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem norm_grad_sq (f : Torus d → ℝ) (x : Torus d) :
    ‖Torus.grad f x‖ ^ 2 = ∑ k, Torus.partialDeriv k f x * Torus.partialDeriv k f x := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [grad_apply, Real.norm_eq_abs, sq_abs]; ring

theorem inner_grad (v : Euc d) (f : Torus d → ℝ) (x : Torus d) :
    inner ℝ v (Torus.grad f x) = ∑ j, v j * Torus.partialDeriv j f x := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [grad_apply]
  simp [mul_comm]

/-- The pointwise stress identity. -/
theorem stress_pointwise {l : ℝ} {v : Torus d → Euc d} {h : Torus d → ℝ} (hh : Torus.IsCk 2 h)
    (x : Torus d) :
    (l * h x - Torus.laplacian h x) * inner ℝ (v x) (Torus.grad h x) =
      ∑ j, (l / 2) * (v x j * Torus.partialDeriv j (fun y => h y * h y) x)
      + ∑ j, ∑ i, (-(v x j * Torus.partialDeriv i
          (fun y => Torus.partialDeriv i h y * Torus.partialDeriv j h y) x))
      + ∑ j, (1 / 2) * (v x j * Torus.partialDeriv j
          (fun y => ∑ k, Torus.partialDeriv k h y * Torus.partialDeriv k h y) x) := by
  have h1 : Torus.IsCk 1 h := hh.of_le (by norm_num)
  have hw1 : ∀ i, Torus.IsCk 1 (Torus.partialDeriv i h) := fun i => HRS.PDE.isCk_one_partialDeriv i h hh
  rw [HRS.PDE.laplacian_eq_sum h hh, inner_grad, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  set S := ∑ i, Torus.partialDeriv i (Torus.partialDeriv i h) x with hS
  set T := ∑ i, Torus.partialDeriv i h x * Torus.partialDeriv j (Torus.partialDeriv i h) x with hT
  have hA1 : Torus.partialDeriv j (fun y => h y * h y) x = 2 * (h x * Torus.partialDeriv j h x) := by
    rw [pd_mul h1 h1]; ring
  have hA2 : ∑ i, Torus.partialDeriv i
      (fun y => Torus.partialDeriv i h y * Torus.partialDeriv j h y) x =
        S * Torus.partialDeriv j h x + T := by
    simp_rw [pd_mul (hw1 _) (hw1 j), Finset.sum_add_distrib, ← Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pd_symm hh i j]
  have hA3 : Torus.partialDeriv j
      (fun y => ∑ k, Torus.partialDeriv k h y * Torus.partialDeriv k h y) x = 2 * T := by
    rw [pd_sum _ (f := fun k y => Torus.partialDeriv k h y * Torus.partialDeriv k h y)
      (fun k => (hw1 k).mul (hw1 k))]
    simp_rw [pd_mul (hw1 _) (hw1 _), Finset.sum_add_distrib]
    rw [hT, two_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hA2, hA1, hA3]
  ring


theorem stress_bound (d : ℕ) {l L : ℝ} (hl : 0 ≤ l) (hL : 0 ≤ L) {v : Torus d → Euc d}
    (hv : IsLipschitzVF L v) {h : Torus d → ℝ} (hh : Torus.IsCk 2 h) :
    |∫ x, (l * h x - Torus.laplacian h x) * inner ℝ (v x) (Torus.grad h x)| ≤
      (2 * d + 1) * L * ∫ x, (l * h x ^ 2 + ‖Torus.grad h x‖ ^ 2) := by
  have h1 : Torus.IsCk 1 h := hh.of_le (by norm_num)
  have hhc : Continuous h := HRS.Torus.continuous_of_continuous_lift h1.continuous
  set w : Fin d → Torus d → ℝ := fun i => Torus.partialDeriv i h with hw
  have hw1 : ∀ i, Torus.IsCk 1 (w i) := fun i => HRS.PDE.isCk_one_partialDeriv i h hh
  have hwc : ∀ i, Continuous (w i) := fun i => HRS.PDE.continuous_partialDeriv i h h1
  set vj : Fin d → Torus d → ℝ := fun j x => v x j with hvj
  have hvl : ∀ j x y, |vj j x - vj j y| ≤ L * KernelGrad.tdist x y := fun j x y =>
    calc |vj j x - vj j y| = |(v x - v y) j| := rfl
      _ ≤ ‖v x - v y‖ := by
          have := PiLp.norm_apply_le (v x - v y) j
          simpa using this
      _ ≤ _ := hv x y
  have hvc : ∀ j, Continuous (vj j) := fun j => CoercAux.continuous_of_isLipschitz_aux (hvl j)
  set φ0 : Torus d → ℝ := fun x => ∑ k, w k x * w k x with hφ0def
  have hφ0 : Torus.IsCk 1 φ0 := isCk_sum _ (f := fun k y => w k y * w k y) (fun k => (hw1 k).mul (hw1 k))
  have hφ0c : Continuous φ0 := continuous_finsetSum _ fun k _ => (hwc k).mul (hwc k)
  have hhh : Torus.IsCk 1 (fun y => h y * h y) := h1.mul h1
  have hww : ∀ i j, Torus.IsCk 1 (fun y => w i y * w j y) := fun i j => (hw1 i).mul (hw1 j)
  -- the three families of terms
  set Tj : Fin d → Torus d → ℝ := fun j x => (l / 2) * (vj j x * Torus.partialDeriv j (fun y => h y * h y) x) with hTj
  set Uij : Fin d → Fin d → Torus d → ℝ := fun j i x =>
    -(vj j x * Torus.partialDeriv i (fun y => w i y * w j y) x) with hUij
  set Sj : Fin d → Torus d → ℝ := fun j x => (1 / 2) * (vj j x * Torus.partialDeriv j φ0 x) with hSj
  have cT : ∀ j, Continuous (Tj j) := fun j =>
    continuous_const.mul ((hvc j).mul (HRS.PDE.continuous_partialDeriv j _ hhh))
  have cU : ∀ j i, Continuous (Uij j i) := fun j i =>
    ((hvc j).mul (HRS.PDE.continuous_partialDeriv i _ (hww i j))).neg
  have cS : ∀ j, Continuous (Sj j) := fun j =>
    continuous_const.mul ((hvc j).mul (HRS.PDE.continuous_partialDeriv j _ hφ0))
  have hpt : ∀ x, (l * h x - Torus.laplacian h x) * inner ℝ (v x) (Torus.grad h x) =
      ∑ j, Tj j x + ∑ j, ∑ i, Uij j i x + ∑ j, Sj j x := fun x => stress_pointwise hh x
  have iT : ∫ x, ∑ j, Tj j x = ∑ j, ∫ x, Tj j x :=
    integral_finsetSum _ fun j _ => int_of_cont (cT j)
  have iU : ∫ x, ∑ j, ∑ i, Uij j i x = ∑ j, ∑ i, ∫ x, Uij j i x := by
    rw [integral_finsetSum _ fun j _ => int_of_cont (continuous_finsetSum _ fun i _ => cU j i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact integral_finsetSum _ fun i _ => int_of_cont (cU j i)
  have iS : ∫ x, ∑ j, Sj j x = ∑ j, ∫ x, Sj j x :=
    integral_finsetSum _ fun j _ => int_of_cont (cS j)
  have hint : ∫ x, (l * h x - Torus.laplacian h x) * inner ℝ (v x) (Torus.grad h x) =
      ∑ j, (∫ x, Tj j x) + ∑ j, ∑ i, (∫ x, Uij j i x) + ∑ j, (∫ x, Sj j x) := by
    have aT : Integrable (fun x => ∑ j, Tj j x) := int_of_cont (continuous_finsetSum _ fun j _ => cT j)
    have aU : Integrable (fun x => ∑ j, ∑ i, Uij j i x) :=
      int_of_cont (continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun i _ => cU j i)
    have aS : Integrable (fun x => ∑ j, Sj j x) := int_of_cont (continuous_finsetSum _ fun j _ => cS j)
    simp_rw [hpt]
    have e1 := integral_add (aT.add aU) aS
    have e2 := integral_add aT aU
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2, iT, iU, iS]
  have hφ0nn : ∀ x, 0 ≤ φ0 x := fun x => Finset.sum_nonneg fun k _ => mul_self_nonneg _
  set Q : ℝ := ∫ x, h x ^ 2 with hQ
  set P : ℝ := ∫ x, φ0 x with hP
  have hQ0 : 0 ≤ Q := integral_nonneg fun x => sq_nonneg _
  have hP0 : 0 ≤ P := integral_nonneg hφ0nn
  have bT : ∀ j, |∫ x, Tj j x| ≤ (l / 2) * (L * Q) := by
    intro j
    have e : ∫ x, Tj j x = (l / 2) * ∫ x, vj j x * Torus.partialDeriv j (fun y => h y * h y) x :=
      integral_const_mul _ _
    have := lipA hL (vj j) (hvl j) _ hhh j
    have e2 : ∫ x, |h x * h x| = Q := by
      rw [hQ]; congr 1; funext x; rw [abs_mul_self]; ring
    rw [e2] at this
    rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ l / 2)]
    exact mul_le_mul_of_nonneg_left this (by linarith)
  have bU : ∀ j i, |∫ x, Uij j i x| ≤ L * ∫ x, |w i x * w j x| := by
    intro j i
    have e : ∫ x, Uij j i x = -∫ x, vj j x * Torus.partialDeriv i (fun y => w i y * w j y) x :=
      integral_neg _
    rw [e, abs_neg]
    exact lipA hL (vj j) (hvl j) _ (hww i j) i
  have bS : ∀ j, |∫ x, Sj j x| ≤ (1 / 2) * (L * P) := by
    intro j
    have e : ∫ x, Sj j x = (1 / 2) * ∫ x, vj j x * Torus.partialDeriv j φ0 x :=
      integral_const_mul _ _
    have := lipA hL (vj j) (hvl j) _ hφ0 j
    have e2 : ∫ x, |φ0 x| = P := by
      rw [hP]; congr 1; funext x; exact abs_of_nonneg (hφ0nn x)
    rw [e2] at this
    rw [e, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  -- the double sum
  have bW : ∑ j, ∑ i, ∫ x, |w i x * w j x| ≤ d * P := by
    have c1 : ∀ i j, Continuous fun x => |w i x * w j x| := fun i j => ((hwc i).mul (hwc j)).abs
    have e1 : ∑ j, ∑ i, ∫ x, |w i x * w j x| = ∫ x, ∑ j, ∑ i, |w i x * w j x| := by
      rw [integral_finsetSum _ fun j _ => int_of_cont (continuous_finsetSum _ fun i _ => c1 i j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finsetSum _ fun i _ => int_of_cont (c1 i j)]
    rw [e1, hP, ← integral_const_mul]
    refine integral_mono (int_of_cont (continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun i _ => c1 i j)) (int_of_cont (continuous_const.mul hφ0c)) fun x => ?_
    show ∑ j, ∑ i, |w i x * w j x| ≤ d * ∑ k, w k x * w k x
    have : ∑ j, ∑ i, |w i x * w j x| = (∑ i, |w i x|) ^ 2 := by
      rw [sq, Finset.sum_mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [abs_mul]
    rw [this]
    have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun i => |w i x|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h2
    refine h2.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun k _ => by ring
  have hrhs : ∫ x, (l * h x ^ 2 + ‖Torus.grad h x‖ ^ 2) = l * Q + P := by
    have e : ∀ x, l * h x ^ 2 + ‖Torus.grad h x‖ ^ 2 = l * h x ^ 2 + φ0 x := fun x => by
      rw [norm_grad_sq]
    simp_rw [e]
    have i1 : Integrable (fun x => l * h x ^ 2) := int_of_cont (continuous_const.mul (hhc.pow 2))
    have := integral_add i1 (int_of_cont hφ0c)
    rw [this, integral_const_mul]
  rw [hint, hrhs]
  have s1 : |∑ j, (∫ x, Tj j x)| ≤ d * ((l / 2) * (L * Q)) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (by
      refine (Finset.sum_le_sum fun j _ => bT j).trans (le_of_eq ?_); simp)
  have s3 : |∑ j, (∫ x, Sj j x)| ≤ d * ((1 / 2) * (L * P)) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (by
      refine (Finset.sum_le_sum fun j _ => bS j).trans (le_of_eq ?_); simp)
  have s2 : |∑ j, ∑ i, (∫ x, Uij j i x)| ≤ L * (d * P) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |∑ i, ∫ x, Uij j i x| ≤ ∑ j, ∑ i, |∫ x, Uij j i x| :=
          Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ∑ i, L * ∫ x, |w i x * w j x| :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => bU j i
      _ = L * ∑ j, ∑ i, ∫ x, |w i x * w j x| := by
          simp_rw [← Finset.mul_sum]
      _ ≤ L * (d * P) := mul_le_mul_of_nonneg_left bW hL
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hlQ : 0 ≤ l * Q := mul_nonneg hl hQ0
  calc _ ≤ |∑ j, (∫ x, Tj j x) + ∑ j, ∑ i, (∫ x, Uij j i x)| + |∑ j, (∫ x, Sj j x)| := abs_add_le _ _
    _ ≤ (|∑ j, (∫ x, Tj j x)| + |∑ j, ∑ i, (∫ x, Uij j i x)|) + |∑ j, (∫ x, Sj j x)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ (d * ((l / 2) * (L * Q)) + L * (d * P)) + d * ((1 / 2) * (L * P)) := by gcongr
    _ ≤ (2 * d + 1) * L * (l * Q + P) := by
        have h1 : 0 ≤ L * (l * Q) := mul_nonneg hL hlQ
        have h2 : 0 ≤ L * P := mul_nonneg hL hP0
        nlinarith [mul_nonneg hd0 h1, mul_nonneg hd0 h2]

end HRS.Commutator.StressAux
