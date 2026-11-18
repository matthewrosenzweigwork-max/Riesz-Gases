import HRS.MS.WhoAux10

/-!
# S54 part 12: the conjugated generator (clause (b) of the frozen statement)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Matrix

namespace HRS.MS.Who

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc

variable {d : ℕ}

/-- an `IsLinearFlow` is the matrix exponential flow -/
theorem who_flow_eq (Q : Matrix (Fin d) (Fin d) ℝ) {Φ : ℝ → Euc d → Euc d} (hΦ : IsLinearFlow Q Φ)
    (x : Euc d) (τ : ℝ) : Φ τ x = ouExp Q τ x := by
  set ψ : ℝ → Euc d := fun τ => ouExp Q (-τ) (Φ τ x) with hψ
  have hE : ∀ τ : ℝ, HasDerivAt (fun u : ℝ => ouExp Q (-u)) (NormedSpace.exp (τ • lcQ Q) * lcQ Q) τ := by
    intro τ
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) (lcQ Q) τ
    have e : (fun u : ℝ => ouExp Q (-u)) = fun u => NormedSpace.exp (u • lcQ Q) := by
      funext u; simp [ouExp]
    rw [e]; exact this
  have hder : ∀ τ, HasDerivAt ψ 0 τ := by
    intro τ
    have h2 := (hΦ.2 x τ)
    have h3 := (hE τ).clm_apply h2
    refine h3.congr_deriv ?_
    have e1 : ouExp Q (-τ) = NormedSpace.exp (τ • lcQ Q) := by simp [ouExp]
    simp only [e1, ContinuousLinearMap.mul_apply, lcQ_apply, map_neg]
    abel
  have hc := is_const_of_deriv_eq_zero (fun τ => (hder τ).differentiableAt) (fun τ => (hder τ).deriv) τ 0
  have h0 : ψ 0 = x := by simp [hψ, ouExp_zero, hΦ.1]
  have : Φ τ x = ouExp Q τ (ψ τ) := by
    simp only [hψ]
    rw [← ContinuousLinearMap.mul_apply, ul2_exp_mul_neg, ContinuousLinearMap.one_apply]
  rw [this, hc, h0]


theorem who_iter_comp_le {r : ℕ} {g : Euc d → ℝ} (hg : ContDiff ℝ r g) (L : Euc d →L[ℝ] Euc d) {j : ℕ}
    (hj : j ≤ r) (y : Euc d) :
    ‖iteratedFDeriv ℝ j (fun x => g (L x)) y‖ ≤ ‖L‖ ^ j * ‖iteratedFDeriv ℝ j g (L y)‖ := by
  have h := ul3C_iter_comp hg L 0 hj y
  simp only [add_zero] at h
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h3 : ∏ _l : Fin j, ‖L‖ = ‖L‖ ^ j := by simp
  rw [h3, mul_comm]

/-- composition with a linear map in the weighted norm of order `r` -/
theorem who_Nsq_comp {P : ℝ} (hP : 0 ≤ P) (L : Euc d →L[ℝ] Euc d)
    (hL : LinearMap.det (L : Euc d →ₗ[ℝ] Euc d) ≠ 0) {r : ℕ} {g : Euc d → ℝ} (hg : ContDiff ℝ r g) :
    Nsq r P (fun x => g (L x)) ≤ ENNReal.ofReal ((max 1 ‖L‖) ^ (2 * r) * cLin P L) * Nsq r P g := by
  unfold Nsq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjr : j ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hGm : Measurable fun y => ‖iteratedFDeriv ℝ j g y‖ :=
    (hg.continuous_iteratedFDeriv (by exact_mod_cast hjr)).norm.measurable
  calc wSq P (fun x => ‖iteratedFDeriv ℝ j (fun x => g (L x)) x‖)
      ≤ wSq P (fun x => ‖L‖ ^ j * ‖iteratedFDeriv ℝ j g (L x)‖) :=
        who_wSq_mono fun x => pow_le_pow_left₀ (norm_nonneg _) (who_iter_comp_le hg L hjr x) 2
    _ = ENNReal.ofReal ((‖L‖ ^ j) ^ 2) * wSq P (fun x => ‖iteratedFDeriv ℝ j g (L x)‖) := who_wSq_smul P _ _
    _ ≤ ENNReal.ofReal ((‖L‖ ^ j) ^ 2) * (ENNReal.ofReal (cLin P L) * wSq P (fun y => ‖iteratedFDeriv ℝ j g y‖)) := by
        refine mul_le_mul' le_rfl ?_
        have := who_wSq_comp_linear hP L hL hGm
        unfold cLin
        exact this
    _ ≤ ENNReal.ofReal ((max 1 ‖L‖) ^ (2 * r) * cLin P L) * wSq P (fun y => ‖iteratedFDeriv ℝ j g y‖) := by
        have hc : 0 ≤ cLin P L := by unfold cLin; positivity
        rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _)]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        refine mul_le_mul_of_nonneg_right ?_ hc
        rw [← pow_mul]
        calc ‖L‖ ^ (j * 2) ≤ (max 1 ‖L‖) ^ (j * 2) := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
          _ ≤ (max 1 ‖L‖) ^ (2 * r) := pow_le_pow_right₀ (le_max_left _ _) (by omega)


theorem who_dir_norm {l : ℕ} {G : Euc d → ℝ} (hG : ContDiff ℝ ((l + 1 : ℕ) : WithTop ℕ∞) G) (v : Euc d) (y : Euc d) :
    ‖iteratedFDeriv ℝ l (fun z => fderiv ℝ G z v) y‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (l + 1) G y‖ := by
  have hd1 : ContDiff ℝ (l : WithTop ℕ∞) (fderiv ℝ G) := hG.fderiv_right (by exact_mod_cast le_refl (l + 1))
  refine (norm_iteratedFDeriv_clm_apply_const (N := (l : WithTop ℕ∞)) (c := v) (n := l)
    hd1.contDiffAt (by exact_mod_cast le_refl l)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]

theorem who_lap_eq {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) (y : Euc d) :
    Laplacian.laplacian h y = ∑ k : Fin d, fderiv ℝ (fun z => fderiv ℝ h z (EuclideanSpace.single k 1)) y
      (EuclideanSpace.single k 1) := by
  have hL : Laplacian.laplacian h y = ∑ i : Fin d,
      iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := by
    have := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := h)
      (EuclideanSpace.basisFun (Fin d) ℝ)) y
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [EuclideanSpace.basisFun_apply]
  rw [hL]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ h) y := ((hh.fderiv_right (by norm_num)).differentiable one_ne_zero) y
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp


theorem who_lap_iter {i : ℕ} {h : Euc d → ℝ} (hh : ContDiff ℝ ((i + 2 : ℕ) : WithTop ℕ∞) h) :
    ContDiff ℝ i (Laplacian.laplacian h) ∧ ∀ y, ‖iteratedFDeriv ℝ i (Laplacian.laplacian h) y‖ ≤
      d * ‖iteratedFDeriv ℝ (i + 2) h y‖ := by
  set G : Fin d → Euc d → ℝ := fun k z => fderiv ℝ h z (EuclideanSpace.single k 1) with hG
  have hGc : ∀ k, ContDiff ℝ ((i + 1 : ℕ) : WithTop ℕ∞) (G k) := fun k =>
    (hh.fderiv_right (by exact_mod_cast le_refl (i + 2))).clm_apply contDiff_const
  have hT : ∀ k, ContDiff ℝ (i : WithTop ℕ∞) (fun y => fderiv ℝ (G k) y (EuclideanSpace.single k 1)) := fun k =>
    ((hGc k).fderiv_right (by exact_mod_cast le_refl (i + 1))).clm_apply contDiff_const
  have hfun : Laplacian.laplacian h = ∑ k : Fin d, fun y => fderiv ℝ (G k) y (EuclideanSpace.single k 1) := by
    funext y
    rw [who_lap_eq (hh.of_le (by exact_mod_cast Nat.le_add_left 2 i)) y]
    simp [Finset.sum_apply, hG]
  rw [hfun]
  have hcd : ContDiff ℝ (i : WithTop ℕ∞) (∑ k : Fin d, fun y => fderiv ℝ (G k) y (EuclideanSpace.single k 1)) := by
    have := ContDiff.sum (s := Finset.univ) fun k _ => hT k
    simpa only [Finset.sum_fn] using this
  refine ⟨hcd, fun y => ?_⟩
  rw [iteratedFDeriv_sum_apply (fun k _ => (hT k).contDiffAt)]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k : Fin d, ‖iteratedFDeriv ℝ i (fun y => fderiv ℝ (G k) y (EuclideanSpace.single k 1)) y‖
      ≤ ∑ _k : Fin d, ‖iteratedFDeriv ℝ (i + 2) h y‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine (who_dir_norm (hGc k) _ y).trans ?_
        have h2 := who_dir_norm (l := i + 1) hh (EuclideanSpace.single k 1) y
        simp only [EuclideanSpace.norm_single, norm_one, one_mul] at h2 ⊢
        exact h2
    _ = _ := by simp


/-- the generator `ν Δ + ulPert` applied to a function with bounded derivatives, in the weighted norm -/
theorem who_F (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (M : Matrix (Fin d) (Fin d) ℝ)
    (ψ : SchwartzMap (Euc d) ℝ) {c : Euc d → Euc d} (hc : IsSmoothBounded c) {P : ℝ}
    (hP : (d : ℝ) / 2 < P) (ν : ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : Euc d → ℝ}, CbCls (r + 3) h →
      ContDiff ℝ r (fun y => ν * Laplacian.laplacian h y + ulPert s M ψ c h y) ∧
      Nsq r P (fun y => ν * Laplacian.laplacian h y + ulPert s M ψ c h y) ≤ ENNReal.ofReal C * Nsq (r + 2) P h := by
  have hsd : s < (d : ℝ) := by linarith
  obtain ⟨CG, hCG0, hG⟩ := who_G_main hd hs0 hs1 M ψ hc hP (r + 1)
  obtain ⟨Cp, hCp0, hpert⟩ := who_pert_sup hs0 hsd M ψ hc r
  refine ⟨((r : ℝ) + 1) * (2 * ((|ν| * d) ^ 2 + 2 * (CG + d ^ 2 * CG))), by positivity, fun {h} hh => ?_⟩
  obtain ⟨hhc, B, hB⟩ := hh
  have hh2 : ContDiff ℝ ((r + 2 : ℕ) : WithTop ℕ∞) h := hhc.of_le (by exact_mod_cast Nat.le_succ _)
  obtain ⟨hlc, hlb⟩ := who_lap_iter hh2
  obtain ⟨hpc, hpb⟩ := hpert hhc hB
  have hcb : CbCls (r + 3) h := ⟨hhc, B, hB⟩
  obtain ⟨hGk, hG0, hwGk, hwG0⟩ := hG (φ := h) (by simpa using hcb)
  have hcb3 : CbCls 3 h := who_cb_mono (by omega) hcb
  have hsplit : ulPert s M ψ c h = fun y => G0 s M ψ c h y +
      ∑ k, fderiv ℝ (Gk s M ψ c k h) y (EuclideanSpace.single k 1) := by
    funext y
    rw [who_decomp hd hs0 hsd M ψ hc hcb3 y]; ring
  refine ⟨(contDiff_const.mul hlc).add hpc, ?_⟩
  have hGk1 : ∀ k, ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (Gk s M ψ c k h) := fun k =>
    (hGk k).1.of_le (by exact_mod_cast Nat.le_succ (r + 1))
  have hG0r : ContDiff ℝ (r : WithTop ℕ∞) (G0 s M ψ c h) :=
    hG0.1.of_le (by exact_mod_cast Nat.le_succ r)
  have hT : ∀ k : Fin d, ContDiff ℝ (r : WithTop ℕ∞)
      (fun y => fderiv ℝ (Gk s M ψ c k h) y (EuclideanSpace.single k 1)) := fun k =>
    ((hGk1 k).fderiv_right (by exact_mod_cast le_refl (r + 1))).clm_apply contDiff_const
  have hptD : ∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i (ulPert s M ψ c h) y‖ ≤
      ‖iteratedFDeriv ℝ i (G0 s M ψ c h) y‖ + ∑ k : Fin d, ‖iteratedFDeriv ℝ (i + 1) (Gk s M ψ c k h) y‖ := by
    intro i hi y
    rw [hsplit]
    have hs2 : (fun y => G0 s M ψ c h y + ∑ k, fderiv ℝ (Gk s M ψ c k h) y (EuclideanSpace.single k 1)) =
        G0 s M ψ c h + ∑ k : Fin d, fun y => fderiv ℝ (Gk s M ψ c k h) y (EuclideanSpace.single k 1) := by
      funext y; simp [Finset.sum_apply]
    have hir : (i : WithTop ℕ∞) ≤ r := by exact_mod_cast hi
    have hsd2 : ContDiffAt ℝ i (∑ k : Fin d, fun y => fderiv ℝ (Gk s M ψ c k h) y (EuclideanSpace.single k 1)) y := by
      have := ContDiffAt.sum (s := Finset.univ) fun k _ => ((hT k).of_le hir).contDiffAt (x := y)
      simpa only [Finset.sum_fn] using this
    rw [hs2, iteratedFDeriv_add_apply ((hG0r.of_le hir).contDiffAt) hsd2,
      iteratedFDeriv_sum_apply (fun k _ => ((hT k).of_le hir).contDiffAt)]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)))
    have h1 := who_dir_norm (l := i) (hGk1 k |>.of_le (by exact_mod_cast Nat.succ_le_succ hi)) (EuclideanSpace.single k 1) y
    simpa [PiLp.norm_single] using h1
  have hptF : ∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i (fun y => ν * Laplacian.laplacian h y + ulPert s M ψ c h y) y‖ ≤
      |ν| * (d * ‖iteratedFDeriv ℝ (i + 2) h y‖) + (‖iteratedFDeriv ℝ i (G0 s M ψ c h) y‖ +
        ∑ k : Fin d, ‖iteratedFDeriv ℝ (i + 1) (Gk s M ψ c k h) y‖) := by
    intro i hi y
    have hir : (i : WithTop ℕ∞) ≤ r := by exact_mod_cast hi
    obtain ⟨hlci, hlbi⟩ := who_lap_iter (i := i) (hhc.of_le (by exact_mod_cast (by omega : i + 2 ≤ r + 3)))
    have e : (fun y => ν * Laplacian.laplacian h y + ulPert s M ψ c h y) =
        (fun y => ν * Laplacian.laplacian h y) + ulPert s M ψ c h := rfl
    rw [e, iteratedFDeriv_add_apply ((contDiff_const.mul hlci).contDiffAt) ((hpc.of_le hir).contDiffAt),
      who_iter_const_mul hlci ν y]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hptD i hi y))
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hlbi y) (abs_nonneg _)
  have hmeasN : ∀ (n : ℕ) (f : Euc d → ℝ), ContDiff ℝ n f → ∀ i ≤ n, Measurable fun y => ‖iteratedFDeriv ℝ i f y‖ :=
    fun n f hf i hi => (hf.continuous_iteratedFDeriv (by exact_mod_cast hi)).norm.measurable
  have hmain : ∀ i ≤ r, wSq P (fun y => ‖iteratedFDeriv ℝ i
      (fun y => ν * Laplacian.laplacian h y + ulPert s M ψ c h y) y‖) ≤
      ENNReal.ofReal (2 * ((|ν| * d) ^ 2 + 2 * (CG + d ^ 2 * CG))) * Nsq (r + 2) P h := by
    intro i hi
    have m1 := hmeasN (r + 3) h hhc (i + 2) (by omega)
    have m2 := hmeasN r (G0 s M ψ c h) hG0r i hi
    have m3 : ∀ k, Measurable fun y => ‖iteratedFDeriv ℝ (i + 1) (Gk s M ψ c k h) y‖ := fun k =>
      hmeasN (r + 1) _ (hGk1 k) (i + 1) (by omega)
    have hN : Nsq (r + 1) P h ≤ Nsq (r + 2) P h := who_Nsq_mono (by omega) P h
    have b1 : wSq P (fun y => ‖iteratedFDeriv ℝ (i + 2) h y‖) ≤ Nsq (r + 2) P h := who_wSq_le_Nsq (by omega) P h
    have b2 : wSq P (fun y => ‖iteratedFDeriv ℝ i (G0 s M ψ c h) y‖) ≤ ENNReal.ofReal CG * Nsq (r + 2) P h :=
      (hwG0 (by omega)).trans (mul_le_mul' le_rfl hN)
    have b3 : ∀ k, wSq P (fun y => ‖iteratedFDeriv ℝ (i + 1) (Gk s M ψ c k h) y‖) ≤
        ENNReal.ofReal CG * Nsq (r + 2) P h := fun k => (hwGk k (by omega)).trans (mul_le_mul' le_rfl hN)
    calc wSq P (fun y => ‖iteratedFDeriv ℝ i (fun y => ν * Laplacian.laplacian h y + ulPert s M ψ c h y) y‖)
        ≤ wSq P (fun y => |ν| * (d * ‖iteratedFDeriv ℝ (i + 2) h y‖) + ((‖iteratedFDeriv ℝ i (G0 s M ψ c h) y‖ +
            ∑ k : Fin d, ‖iteratedFDeriv ℝ (i + 1) (Gk s M ψ c k h) y‖))) :=
          who_wSq_mono fun y => pow_le_pow_left₀ (norm_nonneg _) (hptF i hi y) 2
      _ ≤ 2 * (wSq P (fun y => |ν| * (d * ‖iteratedFDeriv ℝ (i + 2) h y‖)) +
            wSq P (fun y => ‖iteratedFDeriv ℝ i (G0 s M ψ c h) y‖ +
              ∑ k : Fin d, ‖iteratedFDeriv ℝ (i + 1) (Gk s M ψ c k h) y‖)) :=
          who_wSq_add_le (measurable_const.mul (measurable_const.mul m1))
      _ ≤ 2 * (wSq P (fun y => |ν| * (d * ‖iteratedFDeriv ℝ (i + 2) h y‖)) +
            2 * (wSq P (fun y => ‖iteratedFDeriv ℝ i (G0 s M ψ c h) y‖) +
              wSq P (fun y => ∑ k : Fin d, ‖iteratedFDeriv ℝ (i + 1) (Gk s M ψ c k h) y‖))) :=
          mul_le_mul' le_rfl (add_le_add le_rfl (who_wSq_add_le m2))
      _ ≤ 2 * (ENNReal.ofReal ((|ν| * d) ^ 2) * Nsq (r + 2) P h +
            2 * (ENNReal.ofReal CG * Nsq (r + 2) P h +
              (d : ℝ≥0∞) * ((d : ℝ≥0∞) * (ENNReal.ofReal CG * Nsq (r + 2) P h)))) := by
          refine mul_le_mul' le_rfl (add_le_add ?_ (mul_le_mul' le_rfl (add_le_add b2 ?_)))
          · have : wSq P (fun y => |ν| * (d * ‖iteratedFDeriv ℝ (i + 2) h y‖)) =
                ENNReal.ofReal ((|ν| * d) ^ 2) * wSq P (fun y => ‖iteratedFDeriv ℝ (i + 2) h y‖) := by
              rw [← who_wSq_smul]; congr 1; funext y; ring
            rw [this]; exact mul_le_mul' le_rfl b1
          · refine (who_wSq_sum_le (Finset.univ : Finset (Fin d)) (fun k => m3 k)).trans ?_
            rw [Finset.card_univ, Fintype.card_fin]
            refine mul_le_mul' le_rfl ?_
            calc ∑ k : Fin d, wSq P (fun y => ‖iteratedFDeriv ℝ (i + 1) (Gk s M ψ c k h) y‖)
                ≤ ∑ _k : Fin d, ENNReal.ofReal CG * Nsq (r + 2) P h := Finset.sum_le_sum fun k _ => b3 k
              _ = _ := by simp
      _ = ENNReal.ofReal (2 * ((|ν| * d) ^ 2 + 2 * (CG + d ^ 2 * CG))) * Nsq (r + 2) P h := by
          have e1 : ENNReal.ofReal (2 * ((|ν| * d) ^ 2 + 2 * (CG + d ^ 2 * CG))) =
              2 * (ENNReal.ofReal ((|ν| * d) ^ 2) + 2 * (ENNReal.ofReal CG + (d : ℝ≥0∞) ^ 2 * ENNReal.ofReal CG)) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add hCG0 (by positivity),
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
            simp
          rw [e1]; ring
  unfold Nsq
  calc ∑ i ∈ Finset.range (r + 1), wSq P (fun y => ‖iteratedFDeriv ℝ i
        (fun y => ν * Laplacian.laplacian h y + ulPert s M ψ c h y) y‖)
      ≤ ∑ _i ∈ Finset.range (r + 1), ENNReal.ofReal (2 * ((|ν| * d) ^ 2 + 2 * (CG + d ^ 2 * CG))) *
          (∑ j ∈ Finset.range (r + 2 + 1), wSq P (fun y => ‖iteratedFDeriv ℝ j h y‖)) :=
        Finset.sum_le_sum fun i hi => hmain i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    _ = ENNReal.ofReal (((r : ℝ) + 1) * (2 * ((|ν| * d) ^ 2 + 2 * (CG + d ^ 2 * CG)))) *
          ∑ j ∈ Finset.range (r + 2 + 1), wSq P (fun y => ‖iteratedFDeriv ℝ j h y‖) := by
        have hr1 : ENNReal.ofReal ((r : ℝ) + 1) = ((r + 1 : ℕ) : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_natCast]; push_cast; rfl
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (p := (r : ℝ) + 1) (by positivity), hr1]
        ring


theorem who_exp_neg (Q : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) : ouExp (-Q) τ = ouExp Q (-τ) := by
  unfold ouExp
  have : lcQ (-Q) = -lcQ Q := by
    unfold lcQ; rw [map_neg, map_neg]
  rw [this, smul_neg, ← neg_smul, neg_neg]

/-- the generator conjugated by the flow -/
theorem who_B (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (M : Matrix (Fin d) (Fin d) ℝ)
    (ψ : SchwartzMap (Euc d) ℝ) {c : Euc d → Euc d} (hc : IsSmoothBounded c) {P : ℝ}
    (hP : (d : ℝ) / 2 < P) (Q : Matrix (Fin d) (Fin d) ℝ) (ν T : ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Φ : ℝ → Euc d → Euc d}, IsLinearFlow Q Φ → ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ {g : Euc d → ℝ}, ContDiff ℝ ∞ g → HasCompactSupport g →
      ContDiff ℝ r (fun x => generatorW (⟨s, M, ν, fun _ y => c y, fun _ => ⇑ψ⟩ : WholeCoeff d) 0
          (fun y => g (Φ (-t) y)) (Φ t x)) ∧
      Nsq r P (fun x => generatorW (⟨s, M, ν, fun _ y => c y, fun _ => ⇑ψ⟩ : WholeCoeff d) 0
          (fun y => g (Φ (-t) y)) (Φ t x)) ≤ ENNReal.ofReal C * Nsq (r + 2) P g := by
  have hP0 : 0 ≤ P := by linarith [show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity]
  obtain ⟨CF, hCF0, hF⟩ := who_F hd hs0 hs1 M ψ hc hP ν r
  obtain ⟨K1, hK11, hK1⟩ := ul3_exp_unif Q T
  obtain ⟨K2, hK21, hK2⟩ := ul3_exp_unif (-Q) T
  set K : ℝ := max K1 K2 with hK
  have hK1' : 1 ≤ K := le_trans hK11 (le_max_left _ _)
  have hK0 : 0 < K := by linarith
  set Cc : ℝ := (1 + K) ^ (2 * P) * K with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  refine ⟨(K ^ (2 * r) * Cc) * CF * (K ^ (2 * (r + 2)) * Cc), by positivity, ?_⟩
  intro Φ hΦ t ht g hg hgc
  have hBn : ‖ouExp Q t‖ ≤ K := (hK1 t ht).1.trans (le_max_left _ _)
  have hBd : K⁻¹ ≤ |LinearMap.det ((ouExp Q t : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d)| :=
    le_trans (inv_anti₀ (by linarith) (le_max_left K1 K2)) (hK1 t ht).2.2
  have hAn : ‖ouExp Q (-t)‖ ≤ K := by
    have := (hK2 t ht).1; rw [who_exp_neg] at this; exact this.trans (le_max_right _ _)
  have hAd : K⁻¹ ≤ |LinearMap.det ((ouExp Q (-t) : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d)| := by
    have := (hK2 t ht).2.2; rw [who_exp_neg] at this
    exact le_trans (inv_anti₀ (by linarith) (le_max_right K1 K2)) this
  set A := ouExp Q (-t) with hAdef
  set B := ouExp Q t with hBdef
  have hΦA : (fun y => g (Φ (-t) y)) = fun y => g (A y) := funext fun y => by rw [who_flow_eq Q hΦ y (-t)]
  have hΦB : ∀ x, Φ t x = B x := fun x => who_flow_eq Q hΦ x t
  obtain ⟨Bg, hBg⟩ := ul3C_bdd_upto hg hgc (r + 3)
  have hgc' : ContDiff ℝ ((r + 3 : ℕ) : WithTop ℕ∞) g := contDiff_infty.1 hg (r + 3)
  have hhc : ContDiff ℝ ((r + 3 : ℕ) : WithTop ℕ∞) (fun y => g (A y)) := hgc'.comp A.contDiff
  have hcb : CbCls (r + 3) (fun y => g (A y)) :=
    ⟨hhc, K ^ (r + 3) * Bg, fun i hi y => (who_iter_comp_le hgc' A hi y).trans (by
      have hBg0 : 0 ≤ Bg := (norm_nonneg _).trans (hBg 0 (Nat.zero_le _) 0)
      calc ‖A‖ ^ i * ‖iteratedFDeriv ℝ i g (A y)‖ ≤ K ^ i * Bg :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hAn i) (hBg i hi _) (norm_nonneg _) (by positivity)
        _ ≤ K ^ (r + 3) * Bg := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1' hi) hBg0)⟩
  obtain ⟨hFc, hFb⟩ := hF hcb
  have hE : (fun x => generatorW (⟨s, M, ν, fun _ y => c y, fun _ => ⇑ψ⟩ : WholeCoeff d) 0
      (fun y => g (Φ (-t) y)) (Φ t x)) = fun x =>
      (fun y => ν * Laplacian.laplacian (fun y => g (A y)) y + ulPert s M ψ c (fun y => g (A y)) y) (B x) := by
    funext x
    rw [hΦA, hΦB]
    unfold generatorW ulPert ulNL
    ring
  rw [hE]
  refine ⟨hFc.comp B.contDiff, ?_⟩
  have hBdet := who_det_ne hK1' hBd
  have hAdet := who_det_ne hK1' hAd
  have h1 := who_Nsq_comp hP0 B hBdet hFc
  have h2 := who_Nsq_comp hP0 A hAdet (r := r + 2) (g := g) (contDiff_infty.1 hg (r + 2))
  have cB : (max 1 ‖B‖) ^ (2 * r) * cLin P B ≤ K ^ (2 * r) * Cc := by
    have hmax : max 1 ‖B‖ ≤ K := max_le hK1' hBn
    exact mul_le_mul (pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hmax _) (who_cLin_le hP0 hK1' hBn hBd)
      (by unfold cLin; positivity) (by positivity)
  have cA : (max 1 ‖A‖) ^ (2 * (r + 2)) * cLin P A ≤ K ^ (2 * (r + 2)) * Cc := by
    have hmax : max 1 ‖A‖ ≤ K := max_le hK1' hAn
    exact mul_le_mul (pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hmax _) (who_cLin_le hP0 hK1' hAn hAd)
      (by unfold cLin; positivity) (by positivity)
  have hNh : Nsq (r + 2) P (fun y => g (A y)) ≤ ENNReal.ofReal (K ^ (2 * (r + 2)) * Cc) * Nsq (r + 2) P g :=
    h2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal cA) le_rfl)
  calc Nsq r P (fun x => (fun y => ν * Laplacian.laplacian (fun y => g (A y)) y + ulPert s M ψ c (fun y => g (A y)) y) (B x))
      ≤ ENNReal.ofReal ((max 1 ‖B‖) ^ (2 * r) * cLin P B) * Nsq r P (fun y => ν * Laplacian.laplacian (fun y => g (A y)) y +
          ulPert s M ψ c (fun y => g (A y)) y) := h1
    _ ≤ ENNReal.ofReal (K ^ (2 * r) * Cc) * (ENNReal.ofReal CF * Nsq (r + 2) P (fun y => g (A y))) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal cB) hFb
    _ ≤ ENNReal.ofReal (K ^ (2 * r) * Cc) * (ENNReal.ofReal CF *
          (ENNReal.ofReal (K ^ (2 * (r + 2)) * Cc) * Nsq (r + 2) P g)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hNh)
    _ = ENNReal.ofReal ((K ^ (2 * r) * Cc) * CF * (K ^ (2 * (r + 2)) * Cc)) * Nsq (r + 2) P g := by
        have e : ENNReal.ofReal ((K ^ (2 * r) * Cc) * CF * (K ^ (2 * (r + 2)) * Cc)) =
            ENNReal.ofReal (K ^ (2 * r) * Cc) * (ENNReal.ofReal CF * ENNReal.ofReal (K ^ (2 * (r + 2)) * Cc)) := by
          rw [ENNReal.ofReal_mul (p := (K ^ (2 * r) * Cc) * CF) (by positivity),
            ENNReal.ofReal_mul (p := K ^ (2 * r) * Cc) (by positivity)]
          ring
        rw [e]; ring

end HRS.MS.Who
