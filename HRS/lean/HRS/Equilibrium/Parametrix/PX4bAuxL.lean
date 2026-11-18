import HRS.Equilibrium.Parametrix.PX4bAuxK

/-!
# Packet PX4b auxiliaries L: second derivatives of kernels in the chart
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma px4b_fderiv_smooth {K : Torus d → Torus d → ℝ} {m : ℕ}
    (hK : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d)) (hm : 1 ≤ m) (w : Euc d × Euc d) :
    ContDiffOn ℝ ((m - 1 : ℕ) : WithTop ℕ∞) (fun p => fderiv ℝ (lift2 K) p w) (offDiag d) :=
  (hK.fderiv_of_isOpen isOpen_offDiag (m := ((m - 1 : ℕ) : WithTop ℕ∞))
    (by exact_mod_cast (by omega : m - 1 + 1 ≤ m))).clm_apply contDiffOn_const

lemma px4b_K1_smooth {K : Torus d → Torus d → ℝ} {m : ℕ}
    (hK : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d)) (hm : 1 ≤ m) (i : Fin d) :
    ContDiffOn ℝ ((m - 1 : ℕ) : WithTop ℕ∞) (lift2 (px4b_K1 i K)) (offDiag d) :=
  (px4b_fderiv_smooth hK hm _).congr (fun p hp => px4b_lift2_dx hK hm i hp)

lemma px4b_dy_smooth {K : Torus d → Torus d → ℝ} {m : ℕ}
    (hK : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d)) (hm : 1 ≤ m) (i : Fin d) :
    ContDiffOn ℝ ((m - 1 : ℕ) : WithTop ℕ∞) (lift2 (px4b_dy i K)) (offDiag d) :=
  (px4b_fderiv_smooth hK hm _).congr (fun p hp => px4b_lift2_dy hK hm i hp)

lemma px4b_dX_smooth {K : Torus d → Torus d → ℝ} {m : ℕ}
    (hK : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d)) (hm : 1 ≤ m) (i : Fin d) :
    ContDiffOn ℝ ((m - 1 : ℕ) : WithTop ℕ∞) (lift2 (px4b_dX i K)) (offDiag d) := by
  refine (px4b_fderiv_smooth hK hm (px4b_e i, px4b_e i)).congr (fun p hp => ?_)
  show lift2 (px4b_K1 i K) p + lift2 (px4b_dy i K) p = _
  rw [px4b_lift2_dx hK hm i hp, px4b_lift2_dy hK hm i hp, ← map_add, px4b_pair_add1]

lemma px4b_toChart_dX {K : Torus d → Torus d → ℝ} {m : ℕ}
    (hK : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d)) (hm : 1 ≤ m) (i : Fin d)
    {q : Euc d × Euc d} (hq : q ∈ Uc d) :
    toChart (px4b_dX i K) q = fderiv ℝ (toChart K) q (px4b_e i, (0 : Euc d)) := by
  show toChart (px4b_K1 i K) q + toChart (px4b_dy i K) q = _
  rw [px4b_toChart_dx hK hm i hq, px4b_toChart_dy hK hm i hq, ← map_add, px4b_pair_add2]

/-- Chart expression of two successive applications of a derivative operator. -/
lemma px4b_chart_second {Op : (Torus d → Torus d → ℝ) → (Torus d → Torus d → ℝ)}
    {w : Euc d × Euc d}
    (hOp : ∀ (K : Torus d → Torus d → ℝ) (m : ℕ),
      ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d) → 1 ≤ m →
        ContDiffOn ℝ ((m - 1 : ℕ) : WithTop ℕ∞) (lift2 (Op K)) (offDiag d) ∧
          ∀ q ∈ Uc d, toChart (Op K) q = fderiv ℝ (toChart K) q w)
    {K : Torus d → Torus d → ℝ} {m : ℕ}
    (hK : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d)) (hm : 2 ≤ m)
    {q : Euc d × Euc d} (hq : q ∈ Uc d) :
    toChart (Op (Op K)) q = fderiv ℝ (fun q' => fderiv ℝ (toChart K) q' w) q w := by
  obtain ⟨h1s, h1c⟩ := hOp K m hK (by omega)
  have h1s' : ContDiffOn ℝ (((m - 1 : ℕ)) : WithTop ℕ∞) (lift2 (Op K)) (offDiag d) := h1s
  obtain ⟨-, h2c⟩ := hOp (Op K) (m - 1) h1s' (by omega)
  rw [h2c q hq]
  have hev : toChart (Op K) =ᶠ[𝓝 q] fun q' => fderiv ℝ (toChart K) q' w := by
    filter_upwards [isOpen_Uc.mem_nhds hq] with q' hq' using h1c q' hq'
  rw [hev.fderiv_eq]


/-- Chart weights of `∂_x`, `∂_y`, `∂_X`. -/
def px4b_wP (i : Fin d) : Euc d × Euc d := (((1 / 2 : ℝ) • px4b_e i), px4b_e i)
def px4b_wM (i : Fin d) : Euc d × Euc d := (((1 / 2 : ℝ) • px4b_e i), -px4b_e i)
def px4b_wX (i : Fin d) : Euc d × Euc d := (px4b_e i, (0 : Euc d))
def px4b_wZ (i : Fin d) : Euc d × Euc d := ((0 : Euc d), px4b_e i)

lemma px4b_fderiv_fderiv_apply {f : Euc d × Euc d → ℝ} {q : Euc d × Euc d}
    (hf : ContDiffAt ℝ 2 f q) (w w' : Euc d × Euc d) :
    fderiv ℝ (fun q' => fderiv ℝ f q' w) q w' = fderiv ℝ (fderiv ℝ f) q w' w := by
  have hc : DifferentiableAt ℝ (fderiv ℝ f) q :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
  rw [fderiv_clm_apply hc (differentiableAt_const w)]
  simp

theorem px4b_Z_chart {K : Torus d → Torus d → ℝ} {m : ℕ}
    (hK : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d)) (hm : 2 ≤ m) (i : Fin d)
    {q : Euc d × Euc d} (hq : q ∈ Uc d) :
    toChart (px4b_K1 i (px4b_K1 i K)) q + toChart (px4b_dy i (px4b_dy i K)) q -
        (1 / 2 : ℝ) * toChart (px4b_dX i (px4b_dX i K)) q =
      2 * fderiv ℝ (fun q' => fderiv ℝ (toChart K) q' (px4b_wZ i)) q (px4b_wZ i) := by
  have hOp1 : ∀ (K : Torus d → Torus d → ℝ) (m : ℕ),
      ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d) → 1 ≤ m →
        ContDiffOn ℝ ((m - 1 : ℕ) : WithTop ℕ∞) (lift2 (px4b_K1 i K)) (offDiag d) ∧
          ∀ q ∈ Uc d, toChart (px4b_K1 i K) q = fderiv ℝ (toChart K) q (px4b_wP i) :=
    fun K m hK hm => ⟨px4b_K1_smooth hK hm i, fun q hq => px4b_toChart_dx hK hm i hq⟩
  have hOp2 : ∀ (K : Torus d → Torus d → ℝ) (m : ℕ),
      ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d) → 1 ≤ m →
        ContDiffOn ℝ ((m - 1 : ℕ) : WithTop ℕ∞) (lift2 (px4b_dy i K)) (offDiag d) ∧
          ∀ q ∈ Uc d, toChart (px4b_dy i K) q = fderiv ℝ (toChart K) q (px4b_wM i) :=
    fun K m hK hm => ⟨px4b_dy_smooth hK hm i, fun q hq => px4b_toChart_dy hK hm i hq⟩
  have hOp3 : ∀ (K : Torus d → Torus d → ℝ) (m : ℕ),
      ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d) → 1 ≤ m →
        ContDiffOn ℝ ((m - 1 : ℕ) : WithTop ℕ∞) (lift2 (px4b_dX i K)) (offDiag d) ∧
          ∀ q ∈ Uc d, toChart (px4b_dX i K) q = fderiv ℝ (toChart K) q (px4b_wX i) :=
    fun K m hK hm => ⟨px4b_dX_smooth hK hm i, fun q hq => px4b_toChart_dX hK hm i hq⟩
  rw [px4b_chart_second hOp1 hK hm hq, px4b_chart_second hOp2 hK hm hq,
    px4b_chart_second hOp3 hK hm hq]
  have hf : ContDiffAt ℝ 2 (toChart K) q :=
    ((toChart_contDiffOn hK).contDiffAt (isOpen_Uc.mem_nhds hq)).of_le (by exact_mod_cast hm)
  rw [px4b_fderiv_fderiv_apply hf, px4b_fderiv_fderiv_apply hf, px4b_fderiv_fderiv_apply hf,
    px4b_fderiv_fderiv_apply hf]
  have e1 : px4b_wP i = (1 / 2 : ℝ) • px4b_wX i + px4b_wZ i :=
    Prod.ext (by simp [px4b_wP, px4b_wX, px4b_wZ]) (by simp [px4b_wP, px4b_wX, px4b_wZ])
  have e2 : px4b_wM i = (1 / 2 : ℝ) • px4b_wX i - px4b_wZ i :=
    Prod.ext (by simp [px4b_wM, px4b_wX, px4b_wZ]) (by simp [px4b_wM, px4b_wX, px4b_wZ])
  rw [e1, e2]
  simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring


/-- The `z`-Laplacian of a chart function through the second derivative in the pair variable. -/
theorem px4b_laplacian_chart {f : Euc d × Euc d → ℝ} {X z : Euc d}
    (hf : ContDiffAt ℝ 2 f (X, z)) :
    Laplacian.laplacian (fun z' => f (X, z')) z =
      ∑ i : Fin d, fderiv ℝ (fun q' => fderiv ℝ f q' (px4b_wZ i)) (X, z) (px4b_wZ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (fun z' => f (X, z'))
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  set g : Euc d → ℝ := fun z' => f (X, z') with hg
  have hι : ∀ z' : Euc d, HasFDerivAt (fun z'' : Euc d => ((X, z'') : Euc d × Euc d))
      (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) z' := fun z' =>
    (hasFDerivAt_const X z').prodMk (hasFDerivAt_id z')
  have hev : ∀ᶠ z' in 𝓝 z, ContDiffAt ℝ 2 f (X, z') := by
    have h1 : ∀ᶠ q' in 𝓝 (X, z), ContDiffAt ℝ 2 f q' := hf.eventually (by simp)
    exact (continuous_const.prodMk continuous_id).continuousAt.eventually h1 |>.mono fun z' h => h
  have hgd : ∀ᶠ z' in 𝓝 z, fderiv ℝ g z' (px4b_e i) = fderiv ℝ f (X, z') (px4b_wZ i) := by
    filter_upwards [hev] with z' hz'
    have := (hz'.differentiableAt (by norm_num)).hasFDerivAt.comp z' (hι z')
    rw [show g = f ∘ fun z'' : Euc d => ((X, z'') : Euc d × Euc d) from rfl, this.fderiv]
    simp [px4b_wZ]
  have hdd : DifferentiableAt ℝ (fderiv ℝ g) z := by
    have hgc : ContDiffAt ℝ 2 g z := hf.comp z (contDiffAt_const.prodMk contDiffAt_id)
    exact ((hgc.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
  have h1 : fderiv ℝ (fderiv ℝ g) z (px4b_e i) (px4b_e i) =
      fderiv ℝ (fun z' => fderiv ℝ g z' (px4b_e i)) z (px4b_e i) := by
    rw [fderiv_clm_apply hdd (differentiableAt_const _)]
    simp
  have hdq : DifferentiableAt ℝ (fun q' => fderiv ℝ f q' (px4b_wZ i)) (X, z) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt one_ne_zero
  have h2 : fderiv ℝ (fun z' => fderiv ℝ g z' (px4b_e i)) z =
      fderiv ℝ ((fun q' => fderiv ℝ f q' (px4b_wZ i)) ∘ fun z'' : Euc d => ((X, z'') : Euc d × Euc d)) z := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hgd] with z' hz' using hz'
  have h3 := hdq.hasFDerivAt.comp z (hι z)
  rw [show (EuclideanSpace.basisFun (Fin d) ℝ) i = px4b_e i by simp [EuclideanSpace.basisFun_apply]]
  rw [h1, h2, h3.fderiv]
  simp [px4b_wZ]

end HRS.Parx
end
