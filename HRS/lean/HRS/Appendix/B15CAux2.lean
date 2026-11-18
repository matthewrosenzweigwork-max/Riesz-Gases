import HRS.Appendix.B15CAux1
import HRS.Stochastic.Particle

/-!
# Packet B15-C: relocated proofs of the sorried statements of `B15CAux1`

Each `b15c_*_proof` below proves the frozen statement of the same name in `HRS/Appendix/B15CAux1.lean`
(verbatim copy of the statement; the sorried original is left in place).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- Triangle-type estimate for differences in a normed group. -/
theorem b15c2_dist_sub_sub_le (a b c e : Euc d) : dist (a - b) (c - e) ≤ dist a c + dist b e := by
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  have h : (a - b) - (c - e) = (a - c) - (b - e) := by abel
  rw [h]
  exact norm_sub_le _ _

/-- Lipschitz bound for the pair-sum drift `Y ↦ (N⁻¹ ∑_{j≠i} H(y_i - y_j) - K(y_i))_i` on `(ℝ^d)^N`,
for globally Lipschitz `H, K : ℝ^d → ℝ^d` (sup-norm on the product). -/
theorem b15c2_drift_lipschitz_aux (N : ℕ) {H K : Euc d → Euc d} {h k : ℝ≥0}
    (hH : LipschitzWith h H) (hK : LipschitzWith k K) :
    LipschitzWith (2 * h + k)
      (fun Y : Fin N → Euc d => fun i =>
        (1 / (N : ℝ)) • (∑ j ∈ Finset.univ.erase i, H (Y i - Y j)) - K (Y i)) := by
  refine LipschitzWith.of_dist_le_mul fun Y Y' => ?_
  have hδ0 : 0 ≤ dist Y Y' := dist_nonneg
  have hrhs : 0 ≤ ((2 * h + k : ℝ≥0) : ℝ) * dist Y Y' := by positivity
  rw [dist_pi_le_iff hrhs]
  intro i
  have hYi : dist (Y i) (Y' i) ≤ dist Y Y' := dist_le_pi_dist Y Y' i
  have hterm : ∀ j ∈ Finset.univ.erase i,
      dist (H (Y i - Y j)) (H (Y' i - Y' j)) ≤ (h : ℝ) * (2 * dist Y Y') := by
    intro j _
    refine (hH.dist_le_mul _ _).trans ?_
    apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg h)
    refine (b15c2_dist_sub_sub_le _ _ _ _).trans ?_
    have hYj : dist (Y j) (Y' j) ≤ dist Y Y' := dist_le_pi_dist Y Y' j
    linarith
  have hsum := dist_sum_sum_le_of_le (Finset.univ.erase i) hterm
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : (Finset.univ.erase i).card ≤ N := by
    have := Finset.card_erase_le (s := (Finset.univ : Finset (Fin N))) (a := i)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact this
  have hc0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  have key : 1 / (N : ℝ) * ((Finset.univ.erase i).card : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · subst h0; simp
    · rw [div_mul_eq_mul_div, one_mul, div_le_one (by exact_mod_cast hN)]
      exact_mod_cast hc
  have hA : dist ((1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, H (Y i - Y j))
      ((1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, H (Y' i - Y' j)) ≤
      2 * (h : ℝ) * dist Y Y' := by
    rw [dist_smul₀, Real.norm_of_nonneg hc0]
    calc 1 / (N : ℝ) * dist (∑ j ∈ Finset.univ.erase i, H (Y i - Y j))
          (∑ j ∈ Finset.univ.erase i, H (Y' i - Y' j))
        ≤ 1 / (N : ℝ) * (((Finset.univ.erase i).card : ℝ) * ((h : ℝ) * (2 * dist Y Y'))) :=
          mul_le_mul_of_nonneg_left hsum hc0
      _ = (1 / (N : ℝ) * ((Finset.univ.erase i).card : ℝ)) * ((h : ℝ) * (2 * dist Y Y')) := by ring
      _ ≤ 1 * ((h : ℝ) * (2 * dist Y Y')) :=
          mul_le_mul_of_nonneg_right key (by positivity)
      _ = 2 * (h : ℝ) * dist Y Y' := by ring
  have hKd : dist (K (Y i)) (K (Y' i)) ≤ (k : ℝ) * dist Y Y' :=
    (hK.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hYi (NNReal.coe_nonneg k))
  refine (b15c2_dist_sub_sub_le _ _ _ _).trans ?_
  calc _ ≤ 2 * (h : ℝ) * dist Y Y' + (k : ℝ) * dist Y Y' := add_le_add hA hKd
    _ = ((2 * h + k : ℝ≥0) : ℝ) * dist Y Y' := by push_cast; ring

/-- The regularised drift is globally Lipschitz (uniformly in time; it is time-independent), for
`V ∈ C²`: `Torus.grad g_M` is `C^∞` and periodic hence bounded with bounded derivative, and `∇V` is
`C¹` and periodic.  This is the hypothesis of `exists_sde_solution_global`. -/
theorem b15c_liftedDriftReg_isLipschitz_proof (D : DynData d) (hV : Torus.IsCk 2 D.V) (M : ℝ) :
    IsLipschitzDrift (fun _ : ℝ => (b15c_liftedDriftReg D M : (Fin N → Euc d) → Fin N → Euc d)) := by
  have hd : 1 ≤ d := b15_one_le_d D
  -- kernel term: `G = lift (grad g_M)` is `C^1`, periodic, hence globally Lipschitz
  have hsmG0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (Torus.grad (b15c_gReg d D.s M))) :=
    b15c_grad_gReg_isSmooth hd D.hs0 D.hsd M
  have hsmG : ContDiff ℝ 1 (Torus.lift (Torus.grad (b15c_gReg d D.s M))) :=
    hsmG0.of_le (by exact_mod_cast le_top)
  obtain ⟨hg, hgL⟩ := rem_exists_lipschitz_of_periodic _ hsmG fun w n => Torus.lift_periodic _ w n
  -- potential term: `lift (grad V)` is globally Lipschitz
  obtain ⟨k, hkL⟩ := rem_exists_lipschitz_gradient D.V hV
  have hK : LipschitzWith k (Torus.lift (Torus.grad D.V)) := by
    have e : Torus.lift (Torus.grad D.V) = gradient (Torus.lift D.V) :=
      funext (KernelD1Aux.lift_grad D.V)
    rw [e]
    exact hkL
  -- matrix part
  let A : Euc d →L[ℝ] Euc d := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin D.M)
  have hH := A.lipschitzWith.comp hgL
  have hLip := b15c2_drift_lipschitz_aux N hH hK
  have hEq : (b15c_liftedDriftReg D M : (Fin N → Euc d) → Fin N → Euc d) =
      fun Y : Fin N → Euc d => fun i =>
        (1 / (N : ℝ)) • (∑ j ∈ Finset.univ.erase i,
          (A ∘ Torus.lift (Torus.grad (b15c_gReg d D.s M))) (Y i - Y j)) -
          Torus.lift (Torus.grad D.V) (Y i) := by
    funext Y i
    simp only [b15c_liftedDriftReg, b15c_liftedDriftOf, Function.comp_apply, Torus.lift,
      KernelGrad.mk_sub, A, LinearMap.coe_toContinuousLinearMap', Torus.matVec]
  have hL : LipschitzWith (2 * (‖A‖₊ * hg) + k) (b15c_liftedDriftReg D M : (Fin N → Euc d) → Fin N → Euc d) := by
    rw [hEq]; exact hLip
  refine ⟨?_, fun T => ⟨_, fun t _ => hL⟩⟩
  exact ((hL.continuous.comp continuous_snd).continuousOn).mono (Set.subset_univ _)

example := (@b15c_liftedDriftReg_isLipschitz_proof : type_of% @b15c_liftedDriftReg_isLipschitz)

/-! ### Target 3: spacetime convergence -/

/-- Continuity in the time variable of the torus configuration `r ↦ X^ε_{r⁺}(ω)` on `[0,t]`, for a
lifted path `Y` that is continuous on `[0,t]`. -/
theorem b15c3_regProcess_contOn {Ω : Type*} (Y : ℝ → Ω → (Fin N → Euc d)) (ω : Ω) {t : ℝ}
    (hc : ContinuousOn (fun s => Y s ω) (Set.Icc 0 t)) :
    ContinuousOn (fun r : ℝ => b15c_regProcess Y (Real.toNNReal r) ω) (Set.Icc 0 t) := by
  have hf : ContinuousOn (fun r : ℝ => ((Real.toNNReal r : NNReal) : ℝ)) (Set.Icc 0 t) :=
    (NNReal.continuous_coe.comp continuous_real_toNNReal).continuousOn
  have hmaps : Set.MapsTo (fun r : ℝ => ((Real.toNNReal r : NNReal) : ℝ))
      (Set.Icc 0 t) (Set.Icc 0 t) := by
    intro r hr
    show ((Real.toNNReal r : NNReal) : ℝ) ∈ Set.Icc 0 t
    rw [Real.coe_toNNReal _ hr.1]
    exact hr
  have hcomp : ContinuousOn (fun r : ℝ => Y ((Real.toNNReal r : NNReal) : ℝ) ω) (Set.Icc 0 t) :=
    hc.comp hf hmaps
  show ContinuousOn (fun r : ℝ => fun i => Torus.mk (Y ((Real.toNNReal r : NNReal) : ℝ) ω i))
    (Set.Icc 0 t)
  exact continuousOn_pi.2 fun i => Torus.continuous_mk.comp_continuousOn (continuousOn_pi.1 hcomp i)

/-- The time-`r` integral against the selected law is the integral over `ω` (`selectedLaw` is the
pushforward of `P` along `Z (r⁺)`). -/
theorem b15c3_selectedLaw_integral {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ≥0 → Ω → Config d N) (hZ : ∀ s, Measurable (Z s))
    (ψ : ℝ → Config d N → ℝ) (hψ : ∀ r, Continuous (ψ r)) (r : ℝ) :
    ∫ x, ψ r x ∂(selectedLaw P Z r) = ∫ ω, ψ r (Z (Real.toNNReal r) ω) ∂P := by
  unfold selectedLaw
  exact integral_map (hZ _).aemeasurable (hψ r).measurable.aestronglyMeasurable

/-- Continuity in `r ∈ [0,t]` of `∫ ω, ψ(r, Z_{r⁺} ω) dP`, by dominated convergence. -/
theorem b15c3_integral_contOn {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ≥0 → Ω → Config d N) (hZ : ∀ s, Measurable (Z s)) {t : ℝ}
    (hZc : ∀ ω, ContinuousOn (fun r : ℝ => Z (Real.toNNReal r) ω) (Set.Icc 0 t))
    {ψ : ℝ → Config d N → ℝ} (hψ : Continuous (Function.uncurry ψ)) {C : ℝ}
    (hC : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖ψ r x‖ ≤ C) :
    ContinuousOn (fun r : ℝ => ∫ ω, ψ r (Z (Real.toNNReal r) ω) ∂P) (Set.Icc 0 t) := by
  refine continuousOn_of_dominated (F := fun r ω => ψ r (Z (Real.toNNReal r) ω))
    (bound := fun _ => C) (fun r hr => ?_) (fun r hr => ?_) (integrable_const C) ?_
  · exact ((hψ.uncurry_left r).measurable.comp (hZ _)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ω => hC r hr _
  · refine Filter.Eventually.of_forall fun ω => ?_
    have hc : ContinuousOn (fun r : ℝ => (r, Z (Real.toNNReal r) ω)) (Set.Icc 0 t) :=
      continuousOn_id.prodMk (hZc ω)
    exact hψ.comp_continuousOn hc

/-- **Convergence of the spacetime laws** (TeX Step 4: "the convergence of the spacetime laws", L12218):
for `t ∈ [0,T]` and continuous `ψ : ℝ × (𝕋^d)^N → ℝ`,
`∫_0^t ∫ ψ(r,·) dP^r_{N,ε_n} dr → ∫_0^t ∫ ψ(r,·) dP^r_N dr`. -/
theorem b15c_spacetime_tendsto_proof
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} {T : ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (hS : IsStrongSolution P D T X₀ W X)
    {M : ℕ → ℝ} {Y₀ : Ω → Fin N → Euc d} {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hY : ∀ n, IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D (M n)) (liftedNoise D)
      Y₀ (fun _ => ⊤) (Y n))
    (hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T → b15c_regProcess (Y n) t ω = X t ω)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {ψ : ℝ → Config d N → ℝ}
    (hψ : Continuous (Function.uncurry ψ)) :
    Tendsto (fun n => ∫ r in Set.Icc (0 : ℝ) t, ∫ x, ψ r x ∂(selectedLaw P (b15c_regProcess (Y n)) r))
      atTop (𝓝 (∫ r in Set.Icc (0 : ℝ) t, ∫ x, ψ r x ∂(selectedLaw P X r))) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_univ (X := Config d N))).exists_bound_of_continuousOn
    hψ.continuousOn
  have hCr : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖ψ r x‖ ≤ C := fun r hr x =>
    hC (r, x) ⟨hr, Set.mem_univ x⟩
  have hZm : ∀ n s, Measurable (b15c_regProcess (Y n) s) := fun n s =>
    b15c_regProcess_measurable (hY n) s
  have hZc : ∀ n ω, ContinuousOn (fun r : ℝ => b15c_regProcess (Y n) (Real.toNNReal r) ω)
      (Set.Icc 0 t) := fun n ω =>
    b15c3_regProcess_contOn (Y n) ω ((hY n).cont ω t ht0 (WithTop.coe_lt_top t))
  have hGc : ∀ n, ContinuousOn (fun r : ℝ => ∫ x, ψ r x ∂(selectedLaw P (b15c_regProcess (Y n)) r))
      (Set.Icc 0 t) := by
    intro n
    refine ContinuousOn.congr (b15c3_integral_contOn P (b15c_regProcess (Y n)) (hZm n) (hZc n) hψ hCr) ?_
    intro r _
    exact b15c3_selectedLaw_integral P (b15c_regProcess (Y n)) (hZm n) ψ
      (fun r => hψ.uncurry_left r) r
  refine tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (hGc n).aestronglyMeasurable measurableSet_Icc) (integrable_const C) ?_ ?_
  · intro n
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => ?_)
    rw [b15c3_selectedLaw_integral P (b15c_regProcess (Y n)) (hZm n) ψ
      (fun r => hψ.uncurry_left r) r]
    refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun ω => hCr r hr _)).trans ?_
    simp
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => ?_)
    exact b15c_marginal_tendsto hS hY hev hr.1 (hr.2.trans htT) (hψ.uncurry_left r)

example := (@b15c_spacetime_tendsto_proof : type_of% @b15c_spacetime_tendsto)

/-! ### Target 1: gradient structure of the regularised potential -/

/-- The gradient of an even differentiable function is odd. -/
theorem b15c1_gradient_odd {f : Euc d → ℝ} (hf : Differentiable ℝ f) (heven : ∀ x, f (-x) = f x)
    (x : Euc d) : gradient f (-x) = -gradient f x := by
  have hfun : (fun y : Euc d => f (-y)) = f := funext heven
  have h1 : HasFDerivAt (fun y : Euc d => -y) (-ContinuousLinearMap.id ℝ (Euc d)) x :=
    (hasFDerivAt_id x).neg
  have hd : HasFDerivAt (fun y : Euc d => f (-y))
      ((fderiv ℝ f (-x)).comp (-ContinuousLinearMap.id ℝ (Euc d))) x :=
    (hf (-x)).hasFDerivAt.comp x h1
  rw [hfun] at hd
  have heq : fderiv ℝ f x = (fderiv ℝ f (-x)).comp (-ContinuousLinearMap.id ℝ (Euc d)) :=
    (hf x).hasFDerivAt.unique hd
  unfold gradient
  rw [heq]
  simp [ContinuousLinearMap.comp_neg]

/-- The Fréchet derivative of a function on `ℝ^d` is the inner product with its gradient. -/
theorem b15c1_fderiv_eq_inner (f : Euc d → ℝ) (x w : Euc d) :
    fderiv ℝ f x w = inner ℝ (gradient f x) w := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

/-- Symmetrisation of the pair sum: the kernel contribution `∑_{i≠j} ⟪∇g(y_i-y_j), v_i - v_j⟫` equals
twice `∑_{i≠j} ⟪∇g(y_i-y_j), v_i⟫` for an odd gradient. -/
theorem b15c1_kernel_sum {Gr : Euc d → Euc d} (hodd : ∀ x, Gr (-x) = -Gr x) (y v : Fin N → Euc d) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (Gr (y i - y j)) (v i - v j) =
      2 * ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (Gr (y i - y j)) (v i) := by
  have h1 : ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (Gr (y i - y j)) (v i - v j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (Gr (y i - y j)) (v i) -
        ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (Gr (y i - y j)) (v j) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sub_right]
  have h2 : ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (Gr (y i - y j)) (v j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (Gr (y j - y i)) (v i) := by
    refine Finset.sum_comm' (fun x y => ?_)
    simp only [Finset.mem_univ, Finset.mem_erase, true_and, and_true, ne_eq]
    exact ne_comm
  have h3 : ∀ i j, inner ℝ (Gr (y j - y i)) (v i) = -inner ℝ (Gr (y i - y j)) (v i) := by
    intro i j
    rw [← neg_sub, hodd, inner_neg_left]
  rw [h1, h2]
  simp only [h3, Finset.sum_neg_distrib]
  ring

/-- Chain rule for the pair-kernel plus one-body energy `Z ↦ (1/2N) ∑_{i≠j} g(z_i-z_j) + ∑_i Vt(z_i)`. -/
theorem b15c1_fderiv_general {g Vt : Euc d → ℝ} (hg : Differentiable ℝ g)
    (hgeven : ∀ x, g (-x) = g x) (hVt : Differentiable ℝ Vt) (Y v : Fin N → Euc d) :
    fderiv ℝ (fun Z : Fin N → Euc d =>
        (1 / (2 * (N : ℝ))) * (∑ i, ∑ j ∈ Finset.univ.erase i, g (Z i - Z j)) + ∑ i, Vt (Z i)) Y v =
      (1 / (N : ℝ)) * (∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (gradient g (Y i - Y j)) (v i)) +
        ∑ i, inner ℝ (gradient Vt (Y i)) (v i) := by
  have hK : ∀ i j : Fin N, HasFDerivAt (fun Z : Fin N → Euc d => g (Z i - Z j))
      ((fderiv ℝ g (Y i - Y j)).comp
        ((ContinuousLinearMap.proj i : (Fin N → Euc d) →L[ℝ] Euc d) - ContinuousLinearMap.proj j)) Y := by
    intro i j
    have h1 : HasFDerivAt (fun Z : Fin N → Euc d => Z i - Z j)
        ((ContinuousLinearMap.proj i : (Fin N → Euc d) →L[ℝ] Euc d) - ContinuousLinearMap.proj j) Y :=
      (hasFDerivAt_apply i Y).sub (hasFDerivAt_apply j Y)
    exact (hg (Y i - Y j)).hasFDerivAt.comp Y h1
  have hKs : HasFDerivAt (fun Z : Fin N → Euc d => ∑ i, ∑ j ∈ Finset.univ.erase i, g (Z i - Z j))
      (∑ i, ∑ j ∈ Finset.univ.erase i, (fderiv ℝ g (Y i - Y j)).comp
        ((ContinuousLinearMap.proj i : (Fin N → Euc d) →L[ℝ] Euc d) - ContinuousLinearMap.proj j)) Y := by
    convert HasFDerivAt.sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      HasFDerivAt.sum (fun j (_ : j ∈ Finset.univ.erase i) => hK i j)) using 1
    funext Z
    simp only [Finset.sum_apply]
  have hVi : ∀ i : Fin N, HasFDerivAt (fun Z : Fin N → Euc d => Vt (Z i))
      ((fderiv ℝ Vt (Y i)).comp (ContinuousLinearMap.proj i : (Fin N → Euc d) →L[ℝ] Euc d)) Y :=
    fun i => (hVt (Y i)).hasFDerivAt.comp Y (hasFDerivAt_apply i Y)
  have hVs : HasFDerivAt (fun Z : Fin N → Euc d => ∑ i, Vt (Z i))
      (∑ i, (fderiv ℝ Vt (Y i)).comp (ContinuousLinearMap.proj i : (Fin N → Euc d) →L[ℝ] Euc d)) Y := by
    convert HasFDerivAt.sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hVi i) using 1
    funext Z
    simp only [Finset.sum_apply]
  have hT := (hKs.const_mul (1 / (2 * (N : ℝ)))).add hVs
  have hfd : fderiv ℝ (fun Z : Fin N → Euc d =>
      (1 / (2 * (N : ℝ))) * (∑ i, ∑ j ∈ Finset.univ.erase i, g (Z i - Z j)) + ∑ i, Vt (Z i)) Y = _ :=
    hT.fderiv
  rw [hfd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, b15c1_fderiv_eq_inner]
  rw [b15c1_kernel_sum (b15c1_gradient_odd hg hgeven) Y v]
  ring

/-- `Torus.matVec` of the matrix `-I` is negation. -/
theorem b15c1_matVec_neg {M : Matrix (Fin d) (Fin d) ℝ} (hM : M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (w : Euc d) : Torus.matVec M w = -w := by
  subst hM
  unfold Torus.matVec
  simp

theorem b15c_fderiv_potentialReg_proof (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (hV : Torus.IsCk 2 D.V) (M : ℝ) (Y : Fin N → Euc d) (v : Fin N → Euc d) :
    fderiv ℝ (fun Z : Fin N → Euc d => b15c_potentialReg D M (fun i => Torus.mk (Z i))) Y v =
      -∑ i, inner ℝ (b15c_liftedDriftReg D M Y i) (v i) := by
  have hd : 1 ≤ d := b15_one_le_d D
  have hsm0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (b15c_gReg d D.s M)) :=
    b15c_gReg_isSmooth hd D.hs0 D.hsd M
  have hsm1 : ContDiff ℝ 1 (Torus.lift (b15c_gReg d D.s M)) :=
    hsm0.of_le (by exact_mod_cast le_top)
  have hg : Differentiable ℝ (Torus.lift (b15c_gReg d D.s M)) :=
    hsm1.differentiable (by norm_num)
  have hgeven : ∀ x, Torus.lift (b15c_gReg d D.s M) (-x) = Torus.lift (b15c_gReg d D.s M) x := by
    intro x
    show b15c_gReg d D.s M (Torus.mk (-x)) = b15c_gReg d D.s M (Torus.mk x)
    rw [KernelGrad.mk_neg, b15c_gReg_neg]
  have hVd : Differentiable ℝ (Torus.lift D.V) := hV.differentiable (by norm_num)
  have hF : (fun Z : Fin N → Euc d => b15c_potentialReg D M (fun i => Torus.mk (Z i))) =
      fun Z : Fin N → Euc d =>
        (1 / (2 * (N : ℝ))) * (∑ i, ∑ j ∈ Finset.univ.erase i, Torus.lift (b15c_gReg d D.s M) (Z i - Z j))
          + ∑ i, Torus.lift D.V (Z i) := by
    funext Z
    unfold b15c_potentialReg b15c_potentialOf
    simp only [Torus.lift, Function.comp_apply, ← KernelGrad.mk_sub]
  have hgr : ∀ z : Euc d, Torus.grad (b15c_gReg d D.s M) (Torus.mk z) =
      gradient (Torus.lift (b15c_gReg d D.s M)) z := fun z => KernelD1Aux.lift_grad _ z
  have hgV : ∀ z : Euc d, Torus.grad D.V (Torus.mk z) = gradient (Torus.lift D.V) z :=
    fun z => KernelD1Aux.lift_grad _ z
  have hdrift : ∀ i, b15c_liftedDriftReg D M Y i =
      (1 / (N : ℝ)) • (∑ j ∈ Finset.univ.erase i, -(gradient (Torus.lift (b15c_gReg d D.s M)) (Y i - Y j)))
        - gradient (Torus.lift D.V) (Y i) := by
    intro i
    unfold b15c_liftedDriftReg b15c_liftedDriftOf
    simp only [← KernelGrad.mk_sub, hgr, hgV, b15c1_matVec_neg hM]
  have hi : ∀ i, -inner ℝ (b15c_liftedDriftReg D M Y i) (v i) =
      (1 / (N : ℝ)) * (∑ j ∈ Finset.univ.erase i, inner ℝ (gradient (Torus.lift (b15c_gReg d D.s M)) (Y i - Y j)) (v i))
        + inner ℝ (gradient (Torus.lift D.V) (Y i)) (v i) := by
    intro i
    rw [hdrift i]
    simp only [inner_sub_left, real_inner_smul_left, sum_inner, inner_neg_left, Finset.sum_neg_distrib]
    ring
  rw [hF, b15c1_fderiv_general hg hgeven hVd Y v, ← Finset.sum_neg_distrib,
    Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_add_distrib, ← Finset.mul_sum]

example := (@b15c_fderiv_potentialReg_proof : type_of% @b15c_fderiv_potentialReg)

end HRS
