import HRS.Whole.AppendixA

/-!
# Packet Q09-B, part 2: deterministic estimates for `B:lem:moments` (S.A.18)

Kernel gradient formulas, the symmetrised interaction bound `|z·M∇g(z)| ≤ C(1_{s=0} + s g(z))`,
the linear growth of `∇V`, the second-moment drift bound on configurations.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

namespace HRS.Whole.Q09B

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-! ### Matrices and kernels -/

theorem q09b_matVec_apply (M : Matrix (Fin d) (Fin d) ℝ) (v : Euc d) (j : Fin d) :
    Torus.matVec M v j = ∑ i, M j i * v i := by
  simp [Torus.matVec, Matrix.mulVec, dotProduct]

theorem q09b_inner_euc (a b : Euc d) : inner ℝ a b = ∑ i, a i * b i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem q09b_matVec_smul (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (v : Euc d) :
    Torus.matVec M (c • v) = c • Torus.matVec M v := by
  unfold Torus.matVec
  exact map_smul _ _ _

/-- `|⟪z, M z⟫| ≤ MB d ‖z‖²` for `|M_{ij}| ≤ MB`. -/
theorem q09b_quad_bound {MB : ℝ} (hMB0 : 0 ≤ MB) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : PDE.MatBound MB M) (z : Euc d) : |inner ℝ z (Torus.matVec M z)| ≤ MB * d * ‖z‖ ^ 2 := by
  have hMB : ∀ i j, |M i j| ≤ MB := hM
  rw [q09b_inner_euc]
  simp only [q09b_matVec_apply]
  have h1 : |∑ a, z a * ∑ b, M a b * z b| ≤ ∑ a, |z a| * (MB * ∑ b, |z b|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hMB a b) (abs_nonneg _)
  have h2 : ∑ a, |z a| * (MB * ∑ b, |z b|) = MB * (∑ a, |z a|) ^ 2 := by
    rw [← Finset.sum_mul]; ring
  have h3 : (∑ a, |z a|) ^ 2 ≤ d * ∑ a, |z a| ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun a => |z a|)
    simpa using this
  have h4 : ∑ a, |z a| ^ 2 = ‖z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [sq_abs]
  calc |∑ a, z a * ∑ b, M a b * z b| ≤ MB * (∑ a, |z a|) ^ 2 := h1.trans h2.le
    _ ≤ MB * (d * ∑ a, |z a| ^ 2) := mul_le_mul_of_nonneg_left h3 hMB0
    _ = MB * d * ‖z‖ ^ 2 := by rw [h4]; ring

theorem q09b_hasGrad_sq (z : Euc d) {G : ℝ → ℝ} {G' : ℝ} (h : HasDerivAt G G' (‖z‖ ^ 2)) :
    HasGradientAt (fun x : Euc d => G (‖x‖ ^ 2)) ((2 * G') • z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 := h.comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  refine h1.congr_fderiv ?_
  ext w
  simp
  ring

theorem q09b_rkg_zero (z : Euc d) (hz : z ≠ 0) :
    rieszKernelGrad d 0 z = (-(‖z‖ ^ 2)⁻¹) • z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hn2 : 0 < ‖z‖ ^ 2 := by positivity
  unfold rieszKernelGrad
  have hf : rieszKernel d 0 = fun x : Euc d => (-(1 / 2 : ℝ)) * Real.log (‖x‖ ^ 2) := by
    funext x
    simp only [rieszKernel, ite_true]
    rw [Real.log_pow]
    push_cast
    ring
  rw [hf]
  have hD : HasDerivAt (fun t : ℝ => (-(1 / 2 : ℝ)) * Real.log t)
      ((-(1 / 2 : ℝ)) * (‖z‖ ^ 2)⁻¹) (‖z‖ ^ 2) :=
    (Real.hasDerivAt_log hn2.ne').const_mul _
  rw [(q09b_hasGrad_sq z hD).gradient]
  congr 1
  ring

theorem q09b_rkg_ne {s : ℝ} (hs : s ≠ 0) (z : Euc d) (hz : z ≠ 0) :
    rieszKernelGrad d s z = (-s * (‖z‖ ^ 2) ^ (-s / 2 - 1)) • z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hn2 : 0 < ‖z‖ ^ 2 := by positivity
  unfold rieszKernelGrad
  have hf : rieszKernel d s = fun x : Euc d => (‖x‖ ^ 2) ^ (-s / 2) := by
    funext x
    simp only [rieszKernel, hs, ite_false]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast
    ring
  rw [hf]
  have hD := Real.hasDerivAt_rpow_const (x := ‖z‖ ^ 2) (p := -s / 2) (Or.inl hn2.ne')
  rw [(q09b_hasGrad_sq z hD).gradient]
  congr 1
  ring

/-- The kernel gradient is odd (also at `0`, where both sides vanish). -/
theorem q09b_gradient_neg {f : Euc d → ℝ} (hf : ∀ x, f (-x) = f x) (z : Euc d) :
    gradient f (-z) = -gradient f z := by
  have aux : ∀ w : Euc d, DifferentiableAt ℝ f w →
      fderiv ℝ f (-w) = -fderiv ℝ f w ∧ DifferentiableAt ℝ f (-w) := by
    intro w hw
    have hneg : HasFDerivAt (fun x : Euc d => -x) (-(ContinuousLinearMap.id ℝ (Euc d))) (-w) :=
      (hasFDerivAt_id (-w)).neg
    have hcomp : HasFDerivAt (fun x : Euc d => f (-x))
        ((fderiv ℝ f w).comp (-(ContinuousLinearMap.id ℝ (Euc d)))) (-w) := by
      have hw' : HasFDerivAt f (fderiv ℝ f w) (-(-w)) := by rw [neg_neg]; exact hw.hasFDerivAt
      exact hw'.comp (-w) hneg
    have hfeq : (fun x : Euc d => f (-x)) = f := funext hf
    rw [hfeq] at hcomp
    refine ⟨?_, hcomp.differentiableAt⟩
    rw [hcomp.fderiv]
    ext v
    simp
  unfold gradient
  by_cases h : DifferentiableAt ℝ f z
  · rw [(aux z h).1, map_neg]
  · by_cases h2 : DifferentiableAt ℝ f (-z)
    · exact absurd (by simpa using (aux (-z) h2).2) h
    · rw [fderiv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt h2]
      simp

theorem q09b_rkg_neg (s : ℝ) (z : Euc d) :
    rieszKernelGrad d s (-z) = -rieszKernelGrad d s z :=
  q09b_gradient_neg (f := rieszKernel d s) (fun x => rieszKernel_neg x) z

/-- The symmetrised interaction bound, `|z · M ∇g(z)| ≤ MB d (1_{s=0} + s g(z))`. -/
theorem q09b_pair_bound {s : ℝ} (hs0 : 0 ≤ s) {MB : ℝ} (hMB : 0 ≤ MB)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : PDE.MatBound MB M) (z : Euc d) :
    |inner ℝ z (Torus.matVec M (rieszKernelGrad d s z))| ≤
      MB * d * (if s = 0 then 1 else s * rieszKernel d s z) := by
  by_cases hz : z = 0
  · subst hz
    by_cases hs : s = 0
    · simp [hs]
      positivity
    · have : rieszKernel d s 0 = 0 := by
        simp [rieszKernel, hs, Real.zero_rpow (neg_ne_zero.2 hs)]
      simp [hs, this]
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hn2 : 0 < ‖z‖ ^ 2 := by positivity
    have hq := q09b_quad_bound hMB hM z
    by_cases hs : s = 0
    · subst hs
      rw [q09b_rkg_zero z hz, q09b_matVec_smul, inner_smul_right, abs_mul]
      simp only [if_true, mul_one]
      have : |-(‖z‖ ^ 2)⁻¹| = (‖z‖ ^ 2)⁻¹ := by rw [abs_neg, abs_of_pos (inv_pos.2 hn2)]
      rw [this]
      calc (‖z‖ ^ 2)⁻¹ * |inner ℝ z (Torus.matVec M z)| ≤ (‖z‖ ^ 2)⁻¹ * (MB * d * ‖z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hq (inv_pos.2 hn2).le
        _ = MB * d := by field_simp
    · rw [q09b_rkg_ne hs z hz, q09b_matVec_smul, inner_smul_right, abs_mul]
      simp only [hs, if_false]
      have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      have hc : |-s * (‖z‖ ^ 2) ^ (-s / 2 - 1)| = s * (‖z‖ ^ 2) ^ (-s / 2 - 1) := by
        rw [abs_mul, abs_neg, abs_of_pos hspos, abs_of_pos (Real.rpow_pos_of_pos hn2 _)]
      rw [hc]
      have hk : rieszKernel d s z = (‖z‖ ^ 2) ^ (-s / 2) := by
        simp only [rieszKernel, hs, ite_false]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        push_cast
        ring
      rw [hk]
      have hp : (‖z‖ ^ 2) ^ (-s / 2) = (‖z‖ ^ 2) ^ (-s / 2 - 1) * ‖z‖ ^ 2 := by
        rw [← Real.rpow_add_one hn2.ne']
        congr 1
        ring
      calc s * (‖z‖ ^ 2) ^ (-s / 2 - 1) * |inner ℝ z (Torus.matVec M z)|
          ≤ s * (‖z‖ ^ 2) ^ (-s / 2 - 1) * (MB * d * ‖z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hq (by positivity)
        _ = MB * d * (s * (‖z‖ ^ 2) ^ (-s / 2)) := by rw [hp]; ring

/-! ### Linear growth of `∇V` -/

theorem q09b_gradV_bound {mV : ℕ} (hmV : 2 ≤ mV) {ΛV G₀ : ℝ} {V : Euc d → ℝ}
    (hV : VHypRd mV ΛV G₀ V) (x : Euc d) : ‖gradient V x‖ ≤ G₀ + ΛV * ‖x‖ := by
  obtain ⟨hsm, hder, hg0⟩ := hV
  have hnorm : ∀ y, ‖gradient V y‖ = ‖fderiv ℝ V y‖ := fun y => by
    unfold gradient; exact LinearIsometryEquiv.norm_map _ _
  have hd2 : ∀ y, ‖fderiv ℝ (fderiv ℝ V) y‖ ≤ ΛV := by
    intro y
    have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := V) (x := y) (n := 1)
    rw [norm_iteratedFDeriv_one] at h1
    rw [h1]
    exact hder 2 le_rfl hmV y
  have hV2 : ContDiff ℝ 2 V := by exact_mod_cast contDiff_infty.1 hsm 2
  have hdiff : Differentiable ℝ (fderiv ℝ V) :=
    (hV2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hmain := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fderiv ℝ V)
    (s := Set.univ) (x := 0) (y := x) (fun y _ => hdiff y) (fun y _ => hd2 y) convex_univ
    (Set.mem_univ _) (Set.mem_univ _)
  have h0 : ‖fderiv ℝ V 0‖ ≤ G₀ := by rw [← hnorm]; exact hg0
  rw [hnorm]
  calc ‖fderiv ℝ V x‖ ≤ ‖fderiv ℝ V 0‖ + ‖fderiv ℝ V x - fderiv ℝ V 0‖ := norm_le_insert' _ _
    _ ≤ G₀ + ΛV * ‖x‖ := by
        simp only [sub_zero] at hmain
        linarith

/-! ### The second moment on configurations -/

/-- `N⁻¹ ∑_i q(Y_i)`. -/
def q09b_sl (N : ℕ) (q : Euc d → ℝ) (Y : Fin N → Euc d) : ℝ := (N : ℝ)⁻¹ * ∑ i, q (Y i)

/-- The normalised second moment `N⁻¹ ∑ |x_i|²` of a configuration. -/
def q09b_g (d N : ℕ) : EucConfig d N → ℝ := q09b_sl N fun y : Euc d => ‖y‖ ^ 2

theorem q09b_hasFDerivAt_sl {N : ℕ} {q : Euc d → ℝ} (hq : Differentiable ℝ q)
    (Y : Fin N → Euc d) :
    HasFDerivAt (q09b_sl N q)
      ((N : ℝ)⁻¹ • ∑ i, (fderiv ℝ q (Y i)).comp (ContinuousLinearMap.proj i)) Y := by
  have h : ∀ i ∈ Finset.univ, HasFDerivAt (fun Z : Fin N → Euc d => q (Z i))
      ((fderiv ℝ q (Y i)).comp (ContinuousLinearMap.proj i)) Y := fun i _ =>
    (hq (Y i)).hasFDerivAt.comp Y
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).hasFDerivAt
  exact (HasFDerivAt.fun_sum h).const_mul ((N : ℝ)⁻¹)

theorem q09b_fderiv_sl_apply {N : ℕ} {q : Euc d → ℝ} (hq : Differentiable ℝ q)
    (Y u : Fin N → Euc d) :
    fderiv ℝ (q09b_sl N q) Y u = (N : ℝ)⁻¹ * ∑ i, fderiv ℝ q (Y i) (u i) := by
  rw [(q09b_hasFDerivAt_sl hq Y).fderiv]
  simp

theorem q09b_iteratedFDeriv_sl {N : ℕ} {q : Euc d → ℝ} {n : ℕ} (hq : ContDiff ℝ n q)
    (Y : Fin N → Euc d) (m : Fin n → (Fin N → Euc d)) :
    iteratedFDeriv ℝ n (q09b_sl N q) Y m =
      (N : ℝ)⁻¹ * ∑ i, iteratedFDeriv ℝ n q (Y i) (fun a => m a i) := by
  have e : q09b_sl N q = fun Z => (N : ℝ)⁻¹ • ∑ i : Fin N,
      (q ∘ ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i)) Z := by
    funext Z; simp [q09b_sl]
  rw [e, iteratedFDeriv_const_smul_apply' (hf := ?_), iteratedFDeriv_fun_sum_apply]
  · simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sum_apply, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hq Y le_rfl]
    rfl
  · exact fun i _ => (hq.comp (contDiff_apply ℝ (Euc d) i)).contDiffAt
  · exact (ContDiff.sum fun i _ => hq.comp (contDiff_apply ℝ (Euc d) i)).contDiffAt

theorem q09b_fderiv2_sq (y u v : Euc d) :
    fderiv ℝ (fderiv ℝ (fun x : Euc d => ‖x‖ ^ 2)) y u v = 2 * inner ℝ u v := by
  have h : HasFDerivAt (fun y : Euc d => (2 : ℕ) • (innerSL ℝ (E := Euc d)) y)
      ((2 : ℕ) • (innerSL ℝ (E := Euc d) : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)) y := by
    exact ((innerSL ℝ (E := Euc d) : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).hasFDerivAt).const_smul 2
  have e : fderiv ℝ (fun x : Euc d => ‖x‖ ^ 2) =
      fun y => (2 : ℕ) • (innerSL ℝ (E := Euc d)) y := funext fun y => fderiv_norm_sq_apply y
  rw [e, h.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul]
  push_cast
  rfl

theorem q09b_fderiv1_sq (y u : Euc d) :
    fderiv ℝ (fun x : Euc d => ‖x‖ ^ 2) y u = 2 * inner ℝ y u := by
  rw [fderiv_norm_sq_apply]
  simp

theorem q09b_contDiff_g (d N : ℕ) : ContDiff ℝ 2 (q09b_g d N) := by
  unfold q09b_g q09b_sl
  exact contDiff_const.mul (ContDiff.sum fun i _ =>
    (contDiff_norm_sq ℝ (n := 2)).comp (contDiff_apply ℝ (Euc d) i))

theorem q09b_g_nonneg (d N : ℕ) (x : EucConfig d N) : 0 ≤ q09b_g d N x := by
  unfold q09b_g q09b_sl
  positivity

theorem q09b_fderiv_g {N : ℕ} (x h : EucConfig d N) :
    fderiv ℝ (q09b_g d N) x h = (N : ℝ)⁻¹ * ∑ i, 2 * inner ℝ (x i) (h i) := by
  unfold q09b_g
  rw [q09b_fderiv_sl_apply ((contDiff_norm_sq ℝ (n := 2)).differentiable (by norm_num))]
  simp only [q09b_fderiv1_sq]

theorem q09b_fderiv2_g {N : ℕ} (x u v : EucConfig d N) :
    fderiv ℝ (fderiv ℝ (q09b_g d N)) x u v = (N : ℝ)⁻¹ * ∑ i, 2 * inner ℝ (u i) (v i) := by
  have h := iteratedFDeriv_two_apply (𝕜 := ℝ) (q09b_g d N) x ![u, v]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← h]
  unfold q09b_g
  rw [q09b_iteratedFDeriv_sl (n := 2) (contDiff_norm_sq ℝ)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp [q09b_fderiv2_sq]

/-- The additive-noise directions `σ_{(i,j)} = √(2ν) e_{i,j}`. -/
def q09b_noise (d N : ℕ) (ν : ℝ) (k : Fin N × Fin d) : EucConfig d N :=
  Real.sqrt (2 * ν) • Pi.single k.1 (EuclideanSpace.single k.2 (1 : ℝ))

theorem q09b_noise_sum {N : ℕ} (hN : 0 < N) {ν : ℝ} (hν : 0 ≤ ν) (x : EucConfig d N) :
    ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ (q09b_g d N)) x (q09b_noise d N ν k)
      (q09b_noise d N ν k) = 4 * ν * d := by
  have hc : Real.sqrt (2 * ν) ^ 2 = 2 * ν := Real.sq_sqrt (by positivity)
  have hterm : ∀ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ (q09b_g d N)) x (q09b_noise d N ν k)
      (q09b_noise d N ν k) = (N : ℝ)⁻¹ * (4 * ν) := by
    intro k
    rw [q09b_fderiv2_g]
    have hi : ∀ i : Fin N, inner ℝ (q09b_noise d N ν k i) (q09b_noise d N ν k i) =
        if i = k.1 then 2 * ν else 0 := by
      intro i
      by_cases h : i = k.1
      · subst h
        have e1 : inner ℝ (Real.sqrt (2 * ν) • EuclideanSpace.single k.2 (1 : ℝ))
            (Real.sqrt (2 * ν) • EuclideanSpace.single k.2 (1 : ℝ)) = 2 * ν := by
          rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
            EuclideanSpace.norm_single]
          rw [← hc]; simp; ring
        simpa [q09b_noise] using e1
      · simp [q09b_noise, h, Pi.single_apply]
    simp only [hi]
    have hs : ∑ i : Fin N, 2 * (if i = k.1 then 2 * ν else 0) = 4 * ν := by
      simp [mul_ite, Finset.sum_ite_eq']
      ring
    rw [hs]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

/-- The singular-pair majorant `(MB d s / N²) ∑_{i≠j} g(x_i - x_j)` (zero for `s = 0`). -/
def q09b_u (d : ℕ) (s Mn : ℝ) (N : ℕ) (x : EucConfig d N) : ℝ :=
  if s = 0 then 0 else
    Mn * s * ((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (x i - x j)

theorem q09b_u_nonneg {N : ℕ} {s Mn : ℝ} (hs0 : 0 ≤ s) (hMn : 0 ≤ Mn) (x : EucConfig d N) :
    0 ≤ q09b_u d s Mn N x := by
  unfold q09b_u
  split_ifs with hs
  · exact le_rfl
  · have hker : ∀ w : Euc d, 0 ≤ rieszKernel d s w := by
      intro w
      simp only [rieszKernel, hs, ite_false]
      exact Real.rpow_nonneg (norm_nonneg _) _
    have : 0 ≤ ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (x i - x j) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hker _
    positivity

theorem q09b_sum_offdiag_symm {N : ℕ} (v : Fin N → Euc d) (w : Fin N → Fin N → Euc d)
    (hodd : ∀ i j, w j i = -w i j) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (v i) (w i j)
      = (1 / 2 : ℝ) * ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (v i - v j) (w i j) := by
  have hB : ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (v j) (w i j)
      = -∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (v i) (w i j) := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.univ.erase j)
      (fun x y => by simp [Finset.mem_erase, ne_comm])]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hodd y x, inner_neg_right]
  simp only [inner_sub_left, Finset.sum_sub_distrib]
  rw [hB]
  ring

theorem q09b_drift_pair {N : ℕ} (D : WholeDyn d) (x : EucConfig d N) :
    fderiv ℝ (q09b_g d N) x (fun i => particleDriftW D x i) =
      2 * ((N : ℝ)⁻¹) ^ 2 * (∑ i, ∑ j ∈ Finset.univ.erase i,
        inner ℝ (x i) (Torus.matVec D.M (rieszKernelGrad d D.s (x i - x j))))
      - 2 * (N : ℝ)⁻¹ * ∑ i, inner ℝ (x i) (gradient D.V (x i)) := by
  rw [q09b_fderiv_g]
  have hi : ∀ i, inner ℝ (x i) (particleDriftW D x i) =
      (1 / (N : ℝ)) * (∑ j ∈ Finset.univ.erase i,
        inner ℝ (x i) (Torus.matVec D.M (rieszKernelGrad d D.s (x i - x j))))
      - inner ℝ (x i) (gradient D.V (x i)) := by
    intro i
    unfold particleDriftW
    rw [inner_sub_right, inner_smul_right, inner_sum]
  simp only [hi]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [one_div]
  ring

theorem q09b_inter_bound {N : ℕ} (hN : 0 < N) {s : ℝ} (hs0 : 0 ≤ s) {MB : ℝ} (hMB : 0 ≤ MB)
    (D : WholeDyn d) (hDs : D.s = s) (hM : PDE.MatBound MB D.M) (x : EucConfig d N) :
    2 * ((N : ℝ)⁻¹) ^ 2 * (∑ i, ∑ j ∈ Finset.univ.erase i,
        inner ℝ (x i) (Torus.matVec D.M (rieszKernelGrad d D.s (x i - x j))))
      ≤ MB * d + q09b_u d s (MB * d) N x := by
  have hodd : ∀ i j, Torus.matVec D.M (rieszKernelGrad d D.s (x j - x i)) =
      -Torus.matVec D.M (rieszKernelGrad d D.s (x i - x j)) := by
    intro i j
    rw [← neg_sub, q09b_rkg_neg]
    have := q09b_matVec_smul D.M (-1) (rieszKernelGrad d D.s (x i - x j))
    simpa using this
  rw [q09b_sum_offdiag_symm x (fun i j => Torus.matVec D.M (rieszKernelGrad d D.s (x i - x j)))
    hodd]
  have hpair : ∀ i j, inner ℝ (x i - x j) (Torus.matVec D.M (rieszKernelGrad d D.s (x i - x j)))
      ≤ MB * d * (if s = 0 then 1 else s * rieszKernel d s (x i - x j)) := by
    intro i j
    have h := q09b_pair_bound (s := D.s) (by rw [hDs]; exact hs0) hMB hM (x i - x j)
    refine (le_abs_self _).trans (h.trans (le_of_eq ?_))
    rw [hDs]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hMd : 0 ≤ MB * d := by positivity
  have hsum : ∑ i, ∑ j ∈ Finset.univ.erase i,
      inner ℝ (x i - x j) (Torus.matVec D.M (rieszKernelGrad d D.s (x i - x j))) ≤
      ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        MB * d * (if s = 0 then 1 else s * rieszKernel d s (x i - x j)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
  have hc : 0 ≤ 2 * ((N : ℝ)⁻¹) ^ 2 * (1 / 2) := by positivity
  by_cases hs : s = 0
  · simp only [hs, if_true, mul_one, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hu : q09b_u d s (MB * d) N x = 0 := by simp [q09b_u, hs]
    rw [hu, add_zero]
    calc 2 * ((N : ℝ)⁻¹) ^ 2 * (1 / 2 * ∑ i, ∑ j ∈ Finset.univ.erase i,
          inner ℝ (x i - x j) (Torus.matVec D.M (rieszKernelGrad d D.s (x i - x j))))
        ≤ 2 * ((N : ℝ)⁻¹) ^ 2 * (1 / 2 * ((N : ℝ) * (((N - 1 : ℕ) : ℝ) * (MB * d)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ ≤ MB * d := by
          have h1 : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
          have : (N : ℝ) * (((N - 1 : ℕ) : ℝ) * (MB * d)) ≤ (N : ℝ) * ((N : ℝ) * (MB * d)) := by
            gcongr
          calc 2 * ((N : ℝ)⁻¹) ^ 2 * (1 / 2 * ((N : ℝ) * (((N - 1 : ℕ) : ℝ) * (MB * d))))
              ≤ 2 * ((N : ℝ)⁻¹) ^ 2 * (1 / 2 * ((N : ℝ) * ((N : ℝ) * (MB * d)))) := by
                gcongr
            _ = MB * d := by field_simp
  · have hu : q09b_u d s (MB * d) N x =
        MB * d * s * ((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (x i - x j) := by
      simp [q09b_u, hs]
    have hsum2 : ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        MB * d * (if s = 0 then 1 else s * rieszKernel d s (x i - x j))
        = MB * d * s * ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (x i - x j) := by
      simp only [hs, if_false, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hsum2] at hsum
    have hu0 := q09b_u_nonneg (N := N) hs0 hMd x
    calc 2 * ((N : ℝ)⁻¹) ^ 2 * (1 / 2 * ∑ i, ∑ j ∈ Finset.univ.erase i,
          inner ℝ (x i - x j) (Torus.matVec D.M (rieszKernelGrad d D.s (x i - x j))))
        ≤ 2 * ((N : ℝ)⁻¹) ^ 2 * (1 / 2 * (MB * d * s * ∑ i, ∑ j ∈ Finset.univ.erase i,
            rieszKernel d s (x i - x j))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = q09b_u d s (MB * d) N x := by
          rw [hu]; field_simp
      _ ≤ MB * d + q09b_u d s (MB * d) N x := by linarith

theorem q09b_V_bound {N : ℕ} (hN : 0 < N) {mV : ℕ} (hmV : 2 ≤ mV) {ΛV G₀ : ℝ}
    (hG₀ : 0 ≤ G₀) (hΛV : 0 ≤ ΛV) {V : Euc d → ℝ} (hV : VHypRd mV ΛV G₀ V)
    (x : EucConfig d N) :
    -(2 * (N : ℝ)⁻¹ * ∑ i, inner ℝ (x i) (gradient V (x i))) ≤
      G₀ + (G₀ + 2 * ΛV) * q09b_g d N x := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hi : ∀ i, -(2 * inner ℝ (x i) (gradient V (x i))) ≤ G₀ + (G₀ + 2 * ΛV) * ‖x i‖ ^ 2 := by
    intro i
    have h1 : -inner ℝ (x i) (gradient V (x i)) ≤ ‖x i‖ * (G₀ + ΛV * ‖x i‖) := by
      calc -inner ℝ (x i) (gradient V (x i)) ≤ |inner ℝ (x i) (gradient V (x i))| := neg_le_abs _
        _ ≤ ‖x i‖ * ‖gradient V (x i)‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖x i‖ * (G₀ + ΛV * ‖x i‖) :=
            mul_le_mul_of_nonneg_left (q09b_gradV_bound hmV hV (x i)) (norm_nonneg _)
    have h2 : 2 * (‖x i‖ * G₀) ≤ G₀ + G₀ * ‖x i‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x i‖ - 1), mul_nonneg hG₀ (sq_nonneg (‖x i‖ - 1))]
    nlinarith
  have hsum : -(2 * ∑ i, inner ℝ (x i) (gradient V (x i))) ≤
      ∑ i : Fin N, (G₀ + (G₀ + 2 * ΛV) * ‖x i‖ ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => hi i
  have hg : q09b_g d N x = (N : ℝ)⁻¹ * ∑ i, ‖x i‖ ^ 2 := rfl
  have e : ∑ i : Fin N, (G₀ + (G₀ + 2 * ΛV) * ‖x i‖ ^ 2) =
      N * G₀ + (G₀ + 2 * ΛV) * ∑ i, ‖x i‖ ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  rw [e] at hsum
  have : -(2 * (N : ℝ)⁻¹ * ∑ i, inner ℝ (x i) (gradient V (x i))) =
      (N : ℝ)⁻¹ * (-(2 * ∑ i, inner ℝ (x i) (gradient V (x i)))) := by ring
  rw [this, hg]
  calc (N : ℝ)⁻¹ * (-(2 * ∑ i, inner ℝ (x i) (gradient V (x i))))
      ≤ (N : ℝ)⁻¹ * (N * G₀ + (G₀ + 2 * ΛV) * ∑ i, ‖x i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hNpos.le)
    _ = G₀ + (G₀ + 2 * ΛV) * ((N : ℝ)⁻¹ * ∑ i, ‖x i‖ ^ 2) := by field_simp

/-- The pointwise drift bound for the normalised second moment. -/
theorem q09b_drift_le {N : ℕ} (hN : 0 < N) {s : ℝ} (hs0 : 0 ≤ s) {MB ΛV G₀ νbar : ℝ} {mV : ℕ}
    (hmV : 2 ≤ mV) (hMB : 0 ≤ MB) (hG₀ : 0 ≤ G₀) (hΛV : 0 ≤ ΛV) (D : WholeDyn d)
    (hDs : D.s = s) (hM : PDE.MatBound MB D.M) (hV : VHypRd mV ΛV G₀ D.V) (hν0 : 0 ≤ D.invβ)
    (hν : D.invβ ≤ νbar) (x : EucConfig d N) :
    fderiv ℝ (q09b_g d N) x (fun i => particleDriftW D x i) +
        (1 / 2) * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ (q09b_g d N)) x
          (q09b_noise d N D.invβ k) (q09b_noise d N D.invβ k)
      ≤ (G₀ + 2 * ΛV) * q09b_g d N x + (MB * d + G₀ + 2 * νbar * d) + q09b_u d s (MB * d) N x := by
  rw [q09b_drift_pair, q09b_noise_sum hN hν0]
  have h1 := q09b_inter_bound hN hs0 hMB D hDs hM x
  have h2 := q09b_V_bound hN hmV hG₀ hΛV hV x
  have h3 : (1 / 2 : ℝ) * (4 * D.invβ * d) ≤ 2 * νbar * d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    nlinarith
  linarith

end HRS.Whole.Q09B
