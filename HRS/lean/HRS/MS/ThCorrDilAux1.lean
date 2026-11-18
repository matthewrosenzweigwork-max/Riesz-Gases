import HRS.MS.PoisFinal

/-!
# TC-Q (part 1): analytic facts on the dilation `y ↦ f (c • y)`

Infrastructure for the dilation lemma `tcq_affine_poisson_higher` (`HRS/MS/ThCorrDilAux2.lean`).
Namespace `HRS.MS.TcQ`, helper prefix `tcq_`.

* `tcq_norm_iter_dil`: `‖D^i (a • f (c • ·)) x‖ ≤ |a| |c|^i ‖D^i f (c • x)‖`;
* `tcq_laplacian_dil`: `Δ (f (c • ·)) x = c² (Δ f) (c • x)` for `C²` `f`;
* `tcq_gradient_dil`: `∇ (f (c • ·)) x = c • ∇f (c • x)` for differentiable `f`;
* `tcq_memCb_dil`, `tcq_hasCb_dil`: `C_b^k` scalar functions and `C_b^m` vector fields stay in the class under
  `a • f (lam • ·)` with `|a| ≤ 1`, `0 ≤ lam ≤ 1`, with `cbNorm` not increasing, respectively the bound `Mb` kept.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
open HRS HRS.Whole

noncomputable section

namespace HRS.MS.TcQ

variable {d : ℕ}

theorem tcq_norm_iter_dil {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {n : ℕ} (hf : ContDiff ℝ n f) {i : ℕ}
    (hi : i ≤ n) (a c : ℝ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y => a • f (c • y)) x‖ ≤ |a| * |c| ^ i * ‖iteratedFDeriv ℝ i f (c • x)‖ := by
  set g : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E with hg
  have hgx : ∀ y, g y = c • y := fun y => by simp [hg]
  have hcomp : ContDiff ℝ n (fun y => f (c • y)) := by
    have : (fun y => f (c • y)) = f ∘ g := by ext y; simp [hgx]
    rw [this]; exact hf.comp g.contDiff
  have h1 : iteratedFDeriv ℝ i (fun y => a • f (c • y)) x
      = a • iteratedFDeriv ℝ i (fun y => f (c • y)) x :=
    iteratedFDeriv_const_smul_apply (hcomp.of_le (by exact_mod_cast hi)).contDiffAt
  have h2 : iteratedFDeriv ℝ i (fun y => f (c • y)) x
      = (iteratedFDeriv ℝ i f (c • x)).compContinuousLinearMap fun _ => g := by
    have : (fun y => f (c • y)) = f ∘ g := by ext y; simp [hgx]
    rw [this, g.iteratedFDeriv_comp_right hf x (by exact_mod_cast hi), hgx]
  have hgn : ‖g‖ ≤ |c| := by
    have h0 := norm_smul_le c (ContinuousLinearMap.id ℝ E)
    have h1 : ‖ContinuousLinearMap.id ℝ E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    calc ‖g‖ ≤ ‖c‖ * ‖ContinuousLinearMap.id ℝ E‖ := h0
      _ ≤ ‖c‖ * 1 := by gcongr
      _ = |c| := by simp
  have h3 := (iteratedFDeriv ℝ i f (c • x)).norm_compContinuousLinearMap_le fun _ : Fin i => g
  have h4 : ∏ _j : Fin i, ‖g‖ ≤ |c| ^ i := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg _) hgn _
  rw [h1, h2, norm_smul, Real.norm_eq_abs]
  calc |a| * ‖(iteratedFDeriv ℝ i f (c • x)).compContinuousLinearMap fun _ => g‖
      ≤ |a| * (‖iteratedFDeriv ℝ i f (c • x)‖ * ∏ _j : Fin i, ‖g‖) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ ≤ |a| * (‖iteratedFDeriv ℝ i f (c • x)‖ * |c| ^ i) := by gcongr
    _ = |a| * |c| ^ i * ‖iteratedFDeriv ℝ i f (c • x)‖ := by ring

/-- second derivative of a dilation, evaluated on a pair of vectors. -/
theorem tcq_iter2_dil {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x v : Euc d) :
    iteratedFDeriv ℝ 2 (fun y => f (c • y)) x ![v, v] = c ^ 2 * iteratedFDeriv ℝ 2 f (c • x) ![v, v] := by
  set g : Euc d →L[ℝ] Euc d := c • ContinuousLinearMap.id ℝ (Euc d) with hg
  have hgx : ∀ y, g y = c • y := fun y => by simp [hg]
  have : (fun y => f (c • y)) = f ∘ g := by ext y; simp [hgx]
  rw [this, g.iteratedFDeriv_comp_right hf x le_rfl]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hgx]
  have := (iteratedFDeriv ℝ 2 f (c • x)).map_smul_univ (fun _ => c) ![v, v]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  rw [this]

theorem tcq_laplacian_dil {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x : Euc d) :
    Laplacian.laplacian (fun y => f (c • y)) x = c ^ 2 * Laplacian.laplacian f (c • x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [tcq_iter2_dil hf, Finset.mul_sum]

theorem tcq_gradient_dil {f : Euc d → ℝ} (c : ℝ) (x : Euc d) (hf : DifferentiableAt ℝ f (c • x)) :
    gradient (fun y => f (c • y)) x = c • gradient f (c • x) := by
  have h1 : HasFDerivAt (fun y : Euc d => f (c • y))
      ((fderiv ℝ f (c • x)).comp (c • ContinuousLinearMap.id ℝ (Euc d))) x := by
    have hc : HasFDerivAt (fun y : Euc d => c • y) (c • ContinuousLinearMap.id ℝ (Euc d)) x :=
      (hasFDerivAt_id x).const_smul c
    exact HasFDerivAt.comp x (by simpa using hf.hasFDerivAt) hc
  unfold gradient
  rw [h1.fderiv]
  have : (fderiv ℝ f (c • x)).comp (c • ContinuousLinearMap.id ℝ (Euc d)) = c • fderiv ℝ f (c • x) := by
    ext v; simp
  rw [this, map_smul]

theorem tcq_pow_le_one {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) (j : ℕ) : l ^ j ≤ 1 :=
  pow_le_one₀ h0 h1

theorem tcq_memCb_dil {k : ℕ} {r : Euc d → ℝ} (hr : MemCb k r) {a lam : ℝ} (ha : |a| ≤ 1)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    MemCb k (fun y => a * r (lam • y)) ∧ cbNorm k (fun y => a * r (lam • y)) ≤ cbNorm k r := by
  have hb : ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j (fun y => a * r (lam • y)) y‖
      ≤ ⨆ z, ‖iteratedFDeriv ℝ j r z‖ := by
    intro j hj y
    have := tcq_norm_iter_dil hr.1 (n := k) hj a lam y
    simp only [smul_eq_mul] at this
    have hl : |lam| ^ j ≤ 1 := by rw [abs_of_nonneg h0]; exact tcq_pow_le_one h0 h1 j
    have hle : ‖iteratedFDeriv ℝ j r (lam • y)‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j r z‖ :=
      le_ciSup (hr.2 j hj) (lam • y)
    have hn := norm_nonneg (iteratedFDeriv ℝ j r (lam • y))
    calc _ ≤ |a| * |lam| ^ j * ‖iteratedFDeriv ℝ j r (lam • y)‖ := this
      _ ≤ 1 * 1 * ‖iteratedFDeriv ℝ j r (lam • y)‖ := by gcongr
      _ ≤ _ := by simpa using hle
  refine ⟨⟨contDiff_const.mul (hr.1.comp (contDiff_const_smul lam)), fun j hj =>
    ⟨⨆ z, ‖iteratedFDeriv ℝ j r z‖, ?_⟩⟩, ?_⟩
  · rintro _ ⟨y, rfl⟩; exact hb j hj y
  · unfold cbNorm
    refine Finset.sum_le_sum fun j hj => ?_
    exact ciSup_le fun y => hb j (by simpa [Nat.lt_succ_iff] using hj) y

theorem tcq_hasCb_dil {m : ℕ} {Mb : ℝ} {B : Euc d → Euc d} (hB : HasCbBound m Mb B) {lam : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : HasCbBound m Mb (fun y => lam • B (lam • y)) := by
  have hM : 0 ≤ Mb := (norm_nonneg _).trans (hB.2 0 (Nat.zero_le _) 0)
  refine ⟨(hB.1.comp (contDiff_const_smul lam)).const_smul lam, fun j hj y => ?_⟩
  have := tcq_norm_iter_dil hB.1 (n := m) hj lam lam y
  have hl : |lam| ^ j ≤ 1 := by rw [abs_of_nonneg h0]; exact tcq_pow_le_one h0 h1 j
  have hl' : |lam| ≤ 1 := by rwa [abs_of_nonneg h0]
  have hle := hB.2 j hj (lam • y)
  have hn := norm_nonneg (iteratedFDeriv ℝ j B (lam • y))
  calc _ ≤ |lam| * |lam| ^ j * ‖iteratedFDeriv ℝ j B (lam • y)‖ := this
    _ ≤ 1 * 1 * Mb := by gcongr
    _ = Mb := by ring

end HRS.MS.TcQ

end
