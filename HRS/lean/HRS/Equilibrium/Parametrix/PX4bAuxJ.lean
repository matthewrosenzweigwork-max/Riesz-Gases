import HRS.Equilibrium.Parametrix.PX4bAuxI

/-!
# Packet PX4b auxiliaries J: the `y`-derivative kernels and their chart expressions
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- `∂_{y_i} K` as a kernel. -/
def px4b_dy (i : Fin d) (K : Torus d → Torus d → ℝ) : Torus d → Torus d → ℝ :=
  swapK (px4b_K1 i (swapK K))

lemma px4b_swap_mem {p : Euc d × Euc d} (hp : p ∈ offDiag d) : swapCLM d p ∈ offDiag d := by
  show Torus.mk p.2 ≠ Torus.mk p.1
  exact Ne.symm hp

lemma px4b_swapCLM_swap (p : Euc d × Euc d) : swapCLM d (swapCLM d p) = p := rfl

lemma px4b_contDiffOn_swapK {K : Torus d → Torus d → ℝ} {m : ℕ}
    (hK : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d)) :
    ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 (swapK K)) (offDiag d) := by
  rw [lift2_swapK]
  exact hK.comp (swapCLM d).contDiff.contDiffOn (fun p hp => px4b_swap_mem hp)

lemma px4b_lift2_dy {K : Torus d → Torus d → ℝ} {m : ℕ}
    (hK : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d)) (hm : 1 ≤ m) (i : Fin d)
    {p : Euc d × Euc d} (hp : p ∈ offDiag d) :
    lift2 (px4b_dy i K) p = fderiv ℝ (lift2 K) p ((0 : Euc d), EuclideanSpace.single i (1 : ℝ)) := by
  have hsw : swapCLM d p ∈ offDiag d := px4b_swap_mem hp
  have h1 : lift2 (px4b_dy i K) p = lift2 (px4b_K1 i (swapK K)) (swapCLM d p) := rfl
  have h2 := lift2_partial (px4b_contDiffOn_swapK hK) hm i hsw
  rw [h1]
  show lift2 (fun x y => Torus.partialDeriv i (fun z => swapK K z y) x) (swapCLM d p) = _
  rw [h2]
  have hd : DifferentiableAt ℝ (lift2 K) p :=
    (hK.differentiableOn (by exact_mod_cast (by omega : m ≠ 0))).differentiableAt
      (isOpen_offDiag.mem_nhds hp)
  have hc : HasFDerivAt (lift2 (swapK K)) ((fderiv ℝ (lift2 K) p).comp (swapCLM d)) (swapCLM d p) := by
    rw [lift2_swapK]
    have := hd.hasFDerivAt.comp (swapCLM d p) (swapCLM d).hasFDerivAt
    simpa [px4b_swapCLM_swap] using this
  rw [hc.fderiv]
  rfl

lemma px4b_toChart_dy {K : Torus d → Torus d → ℝ} {m : ℕ}
    (hK : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d)) (hm : 1 ≤ m) (i : Fin d)
    {q : Euc d × Euc d} (hq : q ∈ Uc d) :
    toChart (px4b_dy i K) q =
      fderiv ℝ (toChart K) q (((1 / 2 : ℝ) • EuclideanSpace.single i (1 : ℝ)),
        -EuclideanSpace.single i (1 : ℝ)) := by
  have hTq : chartT d q ∈ offDiag d := hq
  have hd : DifferentiableAt ℝ (lift2 K) (chartT d q) :=
    (hK.differentiableOn (by exact_mod_cast (by omega : m ≠ 0))).differentiableAt
      (isOpen_offDiag.mem_nhds hTq)
  have h1 : toChart (px4b_dy i K) q = lift2 (px4b_dy i K) (chartT d q) := by
    rw [toChart_eq]; rfl
  rw [h1, px4b_lift2_dy hK hm i hTq]
  have h2 : HasFDerivAt (toChart K) ((fderiv ℝ (lift2 K) (chartT d q)).comp (chartT d)) q := by
    rw [toChart_eq]
    exact hd.hasFDerivAt.comp q (chartT d).hasFDerivAt
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  rw [chartT_apply]
  refine Prod.ext ?_ ?_
  · show (0 : Euc d) = (1 / 2 : ℝ) • EuclideanSpace.single i (1 : ℝ) +
      (1 / 2 : ℝ) • (-EuclideanSpace.single i (1 : ℝ))
    module
  · show EuclideanSpace.single i (1 : ℝ) = (1 / 2 : ℝ) • EuclideanSpace.single i (1 : ℝ) -
      (1 / 2 : ℝ) • (-EuclideanSpace.single i (1 : ℝ))
    module

theorem px4b_dy_conormal {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {K : Torus d → Torus d → ℝ}
    (hm : 1 ≤ m) (hK : ConormalL σ b m B K) (i : Fin d) :
    ConormalL (σ + 1) (fun c => max (b c) (b (c + 1))) (m - 1) (2 * B) (px4b_dy i K) :=
  conormalL_swap (conormal_partial_fst_aux (conormalL_swap hK) hm i)


lemma px4b_lift2_dx {K : Torus d → Torus d → ℝ} {m : ℕ}
    (hK : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d)) (hm : 1 ≤ m) (i : Fin d)
    {p : Euc d × Euc d} (hp : p ∈ offDiag d) :
    lift2 (px4b_K1 i K) p = fderiv ℝ (lift2 K) p (EuclideanSpace.single i (1 : ℝ), (0 : Euc d)) :=
  lift2_partial hK hm i hp

lemma px4b_toChart_dx {K : Torus d → Torus d → ℝ} {m : ℕ}
    (hK : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 K) (offDiag d)) (hm : 1 ≤ m) (i : Fin d)
    {q : Euc d × Euc d} (hq : q ∈ Uc d) :
    toChart (px4b_K1 i K) q = fderiv ℝ (toChart K) q (((1 / 2 : ℝ) • EuclideanSpace.single i (1 : ℝ)),
        EuclideanSpace.single i (1 : ℝ)) :=
  toChart_partial hK hm i hq


lemma px4b_pair_add1 (e : Euc d) : ((e, (0 : Euc d)) : Euc d × Euc d) + ((0 : Euc d), e) = (e, e) :=
  Prod.ext (by simp) (by simp)

lemma px4b_pair_add2 (e : Euc d) :
    ((((1 / 2 : ℝ) • e), e) : Euc d × Euc d) + (((1 / 2 : ℝ) • e), -e) = (e, 0) :=
  Prod.ext (by show (1 / 2 : ℝ) • e + (1 / 2 : ℝ) • e = e; module) (by simp)

/-- `∂_{X_i} K = ∂_{x_i} K + ∂_{y_i} K` (derivative along the diagonal direction). -/
def px4b_dX (i : Fin d) (K : Torus d → Torus d → ℝ) : Torus d → Torus d → ℝ :=
  fun x y => px4b_K1 i K x y + px4b_dy i K x y

theorem tb_dirD_X {G : Euc d × Euc d → ℝ} {q : Euc d × Euc d} {a c : ℕ} {W : ℝ}
    (hG : ContDiffAt ℝ ((a + c + 1 : ℕ) : WithTop ℕ∞) G q) (e : Euc d) (he : ‖e‖ = 1)
    (h1 : TB G q (a + 1) c W) : TB (dirD (e, (0 : Euc d)) G) q a c W := by
  intro u v
  rw [iteratedFDeriv_dirD hG]
  have T1 : |iteratedFDeriv ℝ (a + c + 1) G q (Fin.snoc (pat u v) (e, (0 : Euc d)))| ≤
      W * (∏ i, ‖u i‖) * ∏ j, ‖v j‖ := by
    rw [← iteratedFDeriv_cons_eq_snoc hG]
    have := h1 (Fin.cons e u) v
    rw [pat_cons_left, iteratedFDeriv_cast, prod_norm_cons, he, one_mul] at this
    exact this
  exact T1

theorem px4b_dX_conormal {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {K : Torus d → Torus d → ℝ}
    (hm : 1 ≤ m) (hK : ConormalL σ b m B K) (i : Fin d) :
    ConormalL σ b (m - 1) B (px4b_dX i K) where
  smooth := by
    set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
    have hfd : ContDiffOn ℝ ((m - 1 : ℕ) : WithTop ℕ∞)
        (fun p => fderiv ℝ (lift2 K) p (e, e)) (offDiag d) :=
      (hK.smooth.fderiv_of_isOpen isOpen_offDiag (m := ((m - 1 : ℕ) : WithTop ℕ∞))
        (by exact_mod_cast (by omega : m - 1 + 1 ≤ m))).clm_apply contDiffOn_const
    refine hfd.congr (fun p hp => ?_)
    show lift2 (px4b_K1 i K) p + lift2 (px4b_dy i K) p = _
    rw [px4b_lift2_dx hK.smooth hm i hp, px4b_lift2_dy hK.smooth hm i hp, ← map_add,
      px4b_pair_add1]
  near := by
    intro a c hac X z hz hzr
    have hq : (X, z) ∈ Uc d := mem_Uc hz hzr
    set r := ‖z‖ with hr
    set L := 1 + |Real.log r| with hL
    have hr0 : 0 < r := norm_pos_iff.mpr hz
    set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
    have hne : ‖e‖ = 1 := by simp [he]
    have hs : ContDiffOn ℝ (((m - 1 : ℕ)) : WithTop ℕ∞) (lift2 (px4b_dX i K)) (offDiag d) := by
      have hfd : ContDiffOn ℝ ((m - 1 : ℕ) : WithTop ℕ∞)
          (fun p => fderiv ℝ (lift2 K) p (e, e)) (offDiag d) :=
        (hK.smooth.fderiv_of_isOpen isOpen_offDiag (m := ((m - 1 : ℕ) : WithTop ℕ∞))
          (by exact_mod_cast (by omega : m - 1 + 1 ≤ m))).clm_apply contDiffOn_const
      refine hfd.congr (fun p hp => ?_)
      show lift2 (px4b_K1 i K) p + lift2 (px4b_dy i K) p = _
      rw [px4b_lift2_dx hK.smooth hm i hp, px4b_lift2_dy hK.smooth hm i hp, ← map_add,
        px4b_pair_add1]
    have hG'd : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) (toChart (px4b_dX i K)) (Uc d) :=
      (toChart_contDiffOn hs).of_le (by exact_mod_cast hac)
    have hGd : ∀ k ≤ m, ContDiffOn ℝ (k : WithTop ℕ∞) (toChart K) (Uc d) := fun k hk =>
      (toChart_contDiffOn hK.smooth).of_le (by exact_mod_cast hk)
    have hGat : ContDiffAt ℝ ((a + c + 1 : ℕ) : WithTop ℕ∞) (toChart K) (X, z) :=
      (hGd (a + c + 1) (by omega)).contDiffAt (isOpen_Uc.mem_nhds hq)
    have hev : toChart (px4b_dX i K) =ᶠ[𝓝 (X, z)] dirD (e, (0 : Euc d)) (toChart K) := by
      filter_upwards [isOpen_Uc.mem_nhds hq] with q' hq'
      show toChart (px4b_K1 i K) q' + toChart (px4b_dy i K) q' = _
      rw [px4b_toChart_dx hK.smooth hm i hq', px4b_toChart_dy hK.smooth hm i hq', ← map_add,
        px4b_pair_add2]
      rfl
    set W₁ : ℝ := B * (1 + r ^ (-(σ + (c : ℝ))) * L ^ (b c)) with hW₁
    have hB : 0 ≤ B := by
      have h00 := hK.near 0 0 (Nat.zero_le _) X z hz hzr
      have h0 : 0 ≤ ‖mixedDeriv 0 0 (toChart K) X z‖ := ContinuousMultilinearMap.opNorm_nonneg _
      have hw : 0 < 1 + r ^ (-(σ + ((0 : ℕ) : ℝ))) * L ^ (b 0) := by positivity
      by_contra hneg
      rw [not_le] at hneg
      have := mul_neg_of_neg_of_pos hneg hw
      linarith
    have hW₁0 : 0 ≤ W₁ := by simp only [hW₁]; positivity
    have T1 : TB (toChart K) (X, z) (a + 1) c W₁ :=
      tb_of_norm_le isOpen_Uc (hGd (a + 1 + c) (by omega)) hq
        (hK.near (a + 1) c (by omega) X z hz hzr)
    have T := tb_congr hev (tb_dirD_X hGat e hne T1)
    exact norm_le_of_tb isOpen_Uc hG'd hq hW₁0 T
  far := by
    intro k hk p hp hr
    have hB : 0 ≤ B := (norm_nonneg _).trans (hK.far 0 (Nat.zero_le _) p hp hr)
    have hat : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (lift2 K) p :=
      (hK.smooth.contDiffAt (isOpen_offDiag.mem_nhds hp)).of_le (by exact_mod_cast (by omega : k + 1 ≤ m))
    set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
    have hev : lift2 (px4b_dX i K) =ᶠ[𝓝 p] dirD (e, e) (lift2 K) := by
      filter_upwards [isOpen_offDiag.mem_nhds hp] with p' hp'
      show lift2 (px4b_K1 i K) p' + lift2 (px4b_dy i K) p' = _
      rw [px4b_lift2_dx hK.smooth hm i hp', px4b_lift2_dy hK.smooth hm i hp', ← map_add,
        px4b_pair_add1]
      rfl
    rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
    refine (norm_iteratedFDeriv_dirD_le hat _).trans ?_
    have hn : ‖(e, e)‖ = 1 := by simp [Prod.norm_def, he]
    rw [hn, mul_one]
    exact hK.far (k + 1) (by omega) p hp hr

end HRS.Parx
end
