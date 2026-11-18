import HRS.MS.MovAdjAux13

/-!
# S6.7 (packet P3, part 3): the bound `‖J f_r‖_{C^{j+2}} ≤ K ‖ψ[f_r]‖_{Σ^M}`

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

`s67_J_bound`: for `M > d/2 + j + 5` there is `K` (depending on `d, s, q, β, j, M` only) such that for every `u ∈ C_b²` with
`ψ[u] = √ρ(u - ∫uρ) ∈ Σ^M`: `u ∈ C^{j+4}`, `J u ∈ C^{j+2}` and `‖D^i J u‖_∞ ≤ K ‖ψ[u]‖_{Σ^M}` for `i ≤ j+2`.
Proof: `w_k = √ρ ∂_k u = ∂_kψ + (βq/2) x_kψ - ½ B_kψ` has derivative bounds up to order `j+3` (`s67_psi_bounds`), then
`J u = ∑_k (movForce(√ρ w_k))_k` and `mov_operators_force_gen` with `j+1`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.Mov63 HRS.MS.MovForce HRS.MH.DualityRd HRS.MS.MovLin

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

/-- `RgW` of the components of a vector field with bounded `C_b^K` norm. -/
theorem s67_rgW_of_cbVec {K : ℕ} {F : Euc d → Euc d} (hF : ContDiff ℝ (K : WithTop ℕ∞) F) {Λ : ℝ}
    (h : cbNormVecE K F ≤ ENNReal.ofReal Λ) (i : Fin d) :
    HRS.MP.RdGen.RgW (fun _ : Euc d => (1 : ℝ)) K (max Λ 0) (fun x => F x i) := by
  have hproj : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le v i)
  refine ⟨contDiff_euclidean.1 hF i, fun n hn x => ?_⟩
  have hn' : (n : WithTop ℕ∞) ≤ K := by exact_mod_cast hn
  have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left (f := F) (x := x)
    (N := (K : WithTop ℕ∞)) hF.contDiffAt hn'
  calc ‖iteratedFDeriv ℝ n (fun y => F y i) x‖
      = ‖iteratedFDeriv ℝ n ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) ∘ F) x‖ := rfl
    _ ≤ ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ n F x‖ := this
    _ ≤ 1 * max Λ 0 := mul_le_mul hproj (s67_cbVec_bound h hn x) (norm_nonneg _) zero_le_one
    _ = max Λ 0 * 1 := by ring

/-- Components of a vector field with `HasCbBound`. -/
theorem s67_rgW_of_cbBound {K : ℕ} {B : Euc d → Euc d} {Mb : ℝ} (hB : HasCbBound K Mb B) (i : Fin d) :
    HRS.MP.RdGen.RgW (fun _ : Euc d => (1 : ℝ)) K (max Mb 0) (fun x => B x i) := by
  have hproj : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le v i)
  refine ⟨contDiff_euclidean.1 hB.1 i, fun n hn x => ?_⟩
  have hn' : (n : WithTop ℕ∞) ≤ K := by exact_mod_cast hn
  have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left (f := B) (x := x)
    (N := (K : WithTop ℕ∞)) hB.1.contDiffAt hn'
  calc ‖iteratedFDeriv ℝ n (fun y => B y i) x‖
      = ‖iteratedFDeriv ℝ n ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) ∘ B) x‖ := rfl
    _ ≤ ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ n B x‖ := this
    _ ≤ 1 * max Mb 0 := mul_le_mul hproj ((hB.2 n hn x).trans (le_max_left _ _)) (norm_nonneg _) zero_le_one
    _ = max Mb 0 * 1 := by ring

/-- `RgW` of a function with bounds on all derivatives, in the `≤ B` form. -/
theorem s67_rgW_of_bound {K : ℕ} {f : Euc d → ℝ} {B : ℝ} (hf : ContDiff ℝ (K : WithTop ℕ∞) f)
    (hb : ∀ k ≤ K, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ B) :
    HRS.MP.RdGen.RgW (fun _ : Euc d => (1 : ℝ)) K B f :=
  ⟨hf, fun n hn x => by simpa using hb n hn x⟩

/-- Lowering the order of an `RgW` bound. -/
theorem s67_rgW_le {K K' : ℕ} {c : ℝ} {f : Euc d → ℝ}
    (h : HRS.MP.RdGen.RgW (fun _ : Euc d => (1 : ℝ)) K c f) (hK : K' ≤ K) :
    HRS.MP.RdGen.RgW (fun _ : Euc d => (1 : ℝ)) K' c f :=
  ⟨h.1.of_le (by exact_mod_cast hK), fun n hn x => h.2 n (hn.trans hK) x⟩

set_option maxHeartbeats 1600000 in
/-- **The bound for `J u`.** -/
theorem s67_J_bound (H : Mov2dTh d s β q ρ) (j M : ℕ) (hM : (d : ℝ) / 2 + j + 5 < M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : Euc d → ℝ, MemCb 2 u → MemOsc (M : ℝ) (s67psi ρ u) →
      ContDiff ℝ ((j + 4 : ℕ) : WithTop ℕ∞) u ∧ ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) (s67J d s ρ u) ∧
      ∀ i ≤ j + 2, ∀ x, ‖iteratedFDeriv ℝ i (s67J d s ρ u) x‖ ≤ K * oscNorm (M : ℝ) (s67psi ρ u) := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hρ := mnb_rhoData H
  obtain ⟨Kψ, hKψ0, hKψ⟩ := s67_psi_bounds (d := d) j M hM
  obtain ⟨B, hBeq, hR, hcbB⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  have hq' : 0 < β * q := mul_pos H.hβ H.hq
  obtain ⟨hψs, hgrad, c, hc, hψb⟩ := HRS.MS.Mov0.mv0_sqrt_gauss hq' hR
  obtain ⟨hdlog, M0, hM0⟩ := HRS.MS.Mov0.mv0_dlog_bounds hq'.le hR
  have hM00 : 0 ≤ M0 := by
    have := hM0 0
    simp only [norm_zero, mul_zero, zero_add] at this
    exact (norm_nonneg _).trans this
  have hfs : ContDiff ℝ ∞ (fun x => gradient (fun y => Real.log (ρ y)) x) := by
    have : (fun x => gradient (fun y => Real.log (ρ y)) x) = fun x => (-(β * q)) • x + B x :=
      funext hgrad
    rw [this]
    exact (contDiff_id.const_smul (-(β * q))).add (HRS.MS.Mov0.mov0_B_smooth hR)
  obtain ⟨C0, hC00, hC0⟩ := mov_operators_force_gen hd1 H.hs0 H.hsd hc hq'.le hM00 hψs hψb hfs hM0 hdlog (j + 1)
  obtain ⟨MB, hMB⟩ := hcbB (j + 4)
  have hMBr : ∀ k : Fin d, HRS.MP.RdGen.RgW (fun _ : Euc d => (1 : ℝ)) (j + 3) (max MB 0) (fun x => B x k) :=
    fun k => s67_rgW_le (s67_rgW_of_cbBound hMB k) (by omega)
  have hbq : 0 ≤ β * q / 2 := by linarith [hq'.le]
  -- the constant
  set L : ℝ := Kψ + (β * q / 2) * Kψ + (1 / 2) * (2 ^ (j + 3) * max MB 0 * Kψ) with hL
  have hL0 : 0 ≤ L := by
    have h3 : 0 ≤ (2 : ℝ) ^ (j + 3) * max MB 0 * Kψ :=
      mul_nonneg (mul_nonneg (by positivity) (le_max_right _ _)) hKψ0
    rw [hL]
    exact add_nonneg (add_nonneg hKψ0 (mul_nonneg hbq hKψ0)) (mul_nonneg (by norm_num) h3)
  refine ⟨d * (C0 * L), by positivity, fun u hu hψ => ?_⟩
  obtain ⟨Bu, hBu0, hBu, hBd, hB2⟩ := s67_memCb_bounds hu
  have hu2 : ContDiff ℝ 2 u := hu.1
  set ψ := s67psi ρ u with hψdef
  set N := oscNorm (M : ℝ) ψ with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  -- qualitative facts for `ψ`
  have hsq : Continuous fun x => Real.sqrt (ρ x) := hρ.smooth.continuous.sqrt
  have hψc : Continuous ψ := by
    have hu0 : Continuous u := hu2.continuous
    have : Continuous fun x => Real.sqrt (ρ x) * (u x - ∫ y, u y * ρ y) := hsq.mul (hu0.sub continuous_const)
    exact this
  have hxL : ∀ i : Fin d, MemLp (fun x => x i * ψ x) 2 (volume : Measure (Euc d)) := by
    intro i
    set cc : ℝ := ∫ y, u y * ρ y with hcc
    refine MemLp.of_le_mul (c := Bu + |cc|) (s67_memLp_G H)
      (((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.mul hψc).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    have hsx : 0 ≤ Real.sqrt (ρ x) := Real.sqrt_nonneg _
    have h1 : |x i| ≤ 1 + ‖x‖ := by
      have := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at this
      linarith
    have h2 : |ψ x| ≤ (Bu + |cc|) * Real.sqrt (ρ x) := by
      show |Real.sqrt (ρ x) * (u x - cc)| ≤ _
      rw [abs_mul, abs_of_nonneg hsx, mul_comm]
      exact mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (add_le_add (hBu x) le_rfl)) hsx
    have e1 : ‖(1 + ‖x‖) * Real.sqrt (ρ x)‖ = (1 + ‖x‖) * Real.sqrt (ρ x) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [e1, Real.norm_eq_abs, abs_mul]
    calc |x i| * |ψ x| ≤ (1 + ‖x‖) * ((Bu + |cc|) * Real.sqrt (ρ x)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = (Bu + |cc|) * ((1 + ‖x‖) * Real.sqrt (ρ x)) := by ring
  obtain ⟨hψC, hψb', hxψ⟩ := hKψ ψ hψc hψ hxL
  -- regularity of `u`
  have hu_eq : u = fun x => (∫ y, u y * ρ y) + ψ x / Real.sqrt (ρ x) := by
    funext x
    have hs : Real.sqrt (ρ x) ≠ 0 := (Real.sqrt_pos.2 (hρ.pos x)).ne'
    show u x = _ + Real.sqrt (ρ x) * (u x - ∫ y, u y * ρ y) / Real.sqrt (ρ x)
    field_simp
    ring
  have hsqC : ContDiff ℝ ((j + 4 : ℕ) : WithTop ℕ∞) (fun x => Real.sqrt (ρ x)) :=
    contDiff_infty.1 hρ.sqrt_smooth (j + 4)
  have hu_C : ContDiff ℝ ((j + 4 : ℕ) : WithTop ℕ∞) u := by
    rw [hu_eq]
    exact contDiff_const.add (hψC.div hsqC (fun x => (Real.sqrt_pos.2 (hρ.pos x)).ne'))
  refine ⟨hu_C, ?_⟩
  -- the functions `w_k`
  have hρd : Differentiable ℝ ρ := hρ.smooth.differentiable (by simp)
  have hgs : ∀ x, gradient (fun y => Real.sqrt (ρ y)) x =
      ((1 / 2) * Real.sqrt (ρ x)) • gradient (fun y => Real.log (ρ y)) x :=
    fun x => mov2a_grad_sqrt hρd hρ.pos x
  set cc : ℝ := ∫ y, u y * ρ y with hcc
  have hψd : Differentiable ℝ ψ := (hψC.differentiable (by norm_num))
  have hdψ : ∀ x (k : Fin d), fderiv ℝ ψ x (EuclideanSpace.single k 1) =
      (1 / 2 * Real.sqrt (ρ x)) * (-(β * q) * x k + B x k) * (u x - cc) +
        Real.sqrt (ρ x) * fderiv ℝ u x (EuclideanSpace.single k 1) := by
    intro x k
    have hsd : DifferentiableAt ℝ (fun y => Real.sqrt (ρ y)) x := hρ.sqrt_smooth.differentiable (by simp) x
    have hud : DifferentiableAt ℝ u x := hu2.differentiable (by norm_num) x
    have h2 : fderiv ℝ (fun y => Real.sqrt (ρ y) * (u y - cc)) x =
        Real.sqrt (ρ x) • fderiv ℝ u x + (u x - cc) • fderiv ℝ (fun y => Real.sqrt (ρ y)) x := by
      rw [fderiv_fun_mul hsd (hud.sub_const cc), fderiv_sub_const]
    show fderiv ℝ (fun y => Real.sqrt (ρ y) * (u y - cc)) x _ = _
    rw [h2]
    simp only [add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have h3 : fderiv ℝ (fun y => Real.sqrt (ρ y)) x (EuclideanSpace.single k 1) =
        (1 / 2 * Real.sqrt (ρ x)) * (-(β * q) * x k + B x k) := by
      rw [← mnc_gradient_apply, hgs x, hgrad x]
      simp
      ring
    rw [h3]; ring
  set wf : Fin d → Euc d → ℝ := fun k x => fderiv ℝ ψ x (EuclideanSpace.single k 1) +
    (β * q / 2) * (x k * ψ x) + (-(1 / 2)) * (B x k * ψ x) with hwf
  have hwk : ∀ k x, wf k x = Real.sqrt (ρ x) * fderiv ℝ u x (EuclideanSpace.single k 1) := by
    intro k x
    simp only [hwf]
    rw [hdψ x k]
    show _ = _
    have : ψ x = Real.sqrt (ρ x) * (u x - cc) := rfl
    rw [this]; ring
  have hwR : ∀ k : Fin d, HRS.MP.RdGen.RgW (fun _ : Euc d => (1 : ℝ)) (j + 3) (L * N) (wf k) := by
    intro k
    have p1 : HRS.MP.RdGen.RgW (fun _ : Euc d => (1 : ℝ)) (j + 3) (Kψ * N) (fun x => gradient ψ x k) :=
      HRS.MP.RdGen.rg_grad_comp (k := j + 3) (φ := ψ) hψC (fun n hn x => hψb' n hn x) k
    have p1' : HRS.MP.RdGen.RgW (fun _ : Euc d => (1 : ℝ)) (j + 3) (Kψ * N)
        (fun x => fderiv ℝ ψ x (EuclideanSpace.single k 1)) := by
      have : (fun x => gradient ψ x k) = fun x => fderiv ℝ ψ x (EuclideanSpace.single k 1) :=
        funext fun x => mnc_gradient_apply ψ x k
      rw [this] at p1; exact p1
    have p2 := s67_rgW_of_bound (hxψ k).1 (hxψ k).2
    have p0 : HRS.MP.RdGen.RgW (fun _ : Euc d => (1 : ℝ)) (j + 3) (Kψ * N) ψ :=
      s67_rgW_of_bound (hψC.of_le (by exact_mod_cast Nat.le_succ _)) (fun n hn x => hψb' n (by omega) x)
    have p3 := HRS.MP.RdGen.RgW.mul (w := fun _ : Euc d => (1 : ℝ)) (fun _ => zero_le_one) (le_max_right _ _)
      (mul_nonneg hKψ0 hN0) (hMBr k) p0
    have hsum := (p1'.add (p2.const_mul (β * q / 2))).add (p3.const_mul (-(1 / 2 : ℝ)))
    refine HRS.MP.RdGen.RgW.mono (fun _ => zero_le_one) hsum ?_
    refine le_of_eq ?_
    rw [abs_of_nonneg hbq, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hL]
    ring
  -- the force bounds for `√ρ w_k`
  have hFk : ∀ k : Fin d, ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) (movb2_F d s ρ (wf k)) ∧
      cbNormVecE (j + 2) (movb2_F d s ρ (wf k)) ≤ ENNReal.ofReal (C0 * (L * N)) := by
    intro k
    obtain ⟨h1, -, h3⟩ := hC0 (wf k) (L * N) (mul_nonneg hL0 hN0) (hwR k).1
      (fun i hi x => by simpa using (hwR k).2 i (by omega) x)
    exact ⟨h1, le_trans le_self_add h3⟩
  have hcomp : ∀ k i : Fin d, HRS.MP.RdGen.RgW (fun _ : Euc d => (1 : ℝ)) (j + 2) (max (C0 * (L * N)) 0)
      (fun x => movb2_F d s ρ (wf k) x i) := fun k i => s67_rgW_of_cbVec (hFk k).1 (hFk k).2 i
  have hsum := HRS.MP.RdGen.RgW.sum (w := fun _ : Euc d => (1 : ℝ)) (k := j + 2) Finset.univ
    (c := fun _ : Fin d => max (C0 * (L * N)) 0) (u := fun k x => movb2_F d s ρ (wf k) x k)
    (fun k _ => hcomp k k)
  have hJeq : s67J d s ρ u = fun x => ∑ k : Fin d, movb2_F d s ρ (wf k) x k := by
    funext x
    unfold s67J
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : (fun y => ρ y * gradient u y k) = fun y => Real.sqrt (ρ y) * wf k y := by
      funext y
      rw [hwk k y, mnc_gradient_apply, ← mul_assoc, Real.mul_self_sqrt (hρ.pos y).le]
    rw [e]
    rfl
  rw [hJeq]
  refine ⟨hsum.1, fun i hi x => ?_⟩
  have h := hsum.2 i hi x
  refine h.trans ?_
  have hC0N : 0 ≤ C0 * (L * N) := mul_nonneg hC00 (mul_nonneg hL0 hN0)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, max_eq_left hC0N]
  refine le_of_eq ?_
  ring

end HRS.MS.MovAdj
