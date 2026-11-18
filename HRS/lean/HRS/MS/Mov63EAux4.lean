import HRS.MS.Mov63EAux3

/-!
# S6.3, packet N6 (part 4): joint continuity of the flux and the explicit divergence `div Y_u`

Namespace `HRS.MS.Mov63`, prefix `mne_`.  See `Mov63EAux1`.

* `mne_joint_lin`: a family `Ψ(u,x)` that is linear in `u` (`Ψ u - Ψ u' = Ψ (u-u')`), bounded by `C‖u‖` and continuous in `x` is jointly continuous along any
  `v` continuous in `Σ^m`.  `mne_joint`: `h_{v_s}(x)`, `∇h`, `Δh`, `F_{v_s}(x)`, `div F_{v_s}(x)` are jointly continuous on `S × ℝ^d`.
* `mne_e_formulaR`, `mne_e_formula`: `div Y_u = ν Δρ_u + ρ_u (q d + div F[ρ_u]) + ⟨∇ρ_u, qx + F[ρ_u]⟩` (and split over `ρ + h_u`);
  `mne_e_joint`: `(s,x) ↦ div Y_{v_s}(x)` is jointly continuous.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section JointLin

lemma mne_joint_lin {E G X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [TopologicalSpace X] {Ψ : E → X → G} (C : ℝ) (hsub : ∀ u u' x, Ψ u x - Ψ u' x = Ψ (u - u') x)
    (hb : ∀ u x, ‖Ψ u x‖ ≤ C * ‖u‖) (hc : ∀ u, Continuous (Ψ u)) {S : Set ℝ} {v : ℝ → E}
    (hv : ContinuousOn v S) : ContinuousOn (fun p : ℝ × X => Ψ (v p.1) p.2) (S ×ˢ univ) := by
  intro p0 hp0
  obtain ⟨s0, x0⟩ := p0
  have hs0 : s0 ∈ S := hp0.1
  have h1 : Tendsto (fun p : ℝ × X => Ψ (v p.1 - v s0) p.2) (𝓝[S ×ˢ univ] (s0, x0)) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun p : ℝ × X => C * ‖v p.1 - v s0‖) (Eventually.of_forall fun p => hb _ _) ?_
    have hv' : ContinuousWithinAt (fun p : ℝ × X => v p.1) (S ×ˢ univ) (s0, x0) :=
      (hv s0 hs0).comp continuousWithinAt_fst (fun p (hp : p ∈ S ×ˢ univ) => hp.1)
    have := (hv'.sub (continuousWithinAt_const (b := v s0))).norm.const_mul C
    simpa [ContinuousWithinAt] using this
  have h2 : ContinuousWithinAt (fun p : ℝ × X => Ψ (v s0) p.2) (S ×ˢ univ) (s0, x0) :=
    ((hc (v s0)).comp continuous_snd).continuousWithinAt
  have e : (fun p : ℝ × X => Ψ (v p.1) p.2) = fun p => Ψ (v p.1 - v s0) p.2 + Ψ (v s0) p.2 := by
    funext p
    rw [← hsub]; abel
  rw [ContinuousWithinAt, e]
  simpa using h1.add h2

end JointLin

section Inst

variable {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m)

lemma mne_hu_sub (u u' : OscSpace d (m : ℝ)) :
    mnc_hu ρ (mne_hn hm) (u - u') = fun y => mnc_hu ρ (mne_hn hm) u y - mnc_hu ρ (mne_hn hm) u' y := by
  have : u - u' = u + (-1 : ℝ) • u' := by rw [neg_one_smul]; rfl
  rw [this, mnc_hu_add, mnc_hu_smul]
  funext y
  ring

lemma mne_hu_cd (H : Mov2dTh d s β q ρ) (u : OscSpace d (m : ℝ)) : ContDiff ℝ 3 (mnc_hu ρ (mne_hn hm) u) := by
  obtain ⟨c, K0, hc, hK0, h⟩ := mnc_h_gauss H (mne_hn hm)
  exact_mod_cast (h u).1

lemma mne_hu_iter (H : Mov2dTh d s β q ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u : OscSpace d (m : ℝ)) (n : ℕ), n ≤ 3 → ∀ x,
      ‖iteratedFDeriv ℝ n (mnc_hu ρ (mne_hn hm) u) x‖ ≤ K * ‖u‖ := by
  obtain ⟨c, K0, hc, hK0, h⟩ := mnc_h_gauss H (mne_hn hm)
  refine ⟨K0, hK0, fun u n hn x => ?_⟩
  refine ((h u).2 n hn x).trans ?_
  have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])
  nlinarith [mul_nonneg hK0 (norm_nonneg u)]

lemma mne_lap_cont {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (Laplacian.laplacian f) := by
  have h2 : Continuous (iteratedFDeriv ℝ 2 f) := hf.continuous_iteratedFDeriv (m := 2) (by norm_num)
  have e : Laplacian.laplacian f = fun y => ∑ i : Fin d, iteratedFDeriv ℝ 2 f y
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := funext fun y => mnb_lap_formula f y
  rw [e]
  refine continuous_finsetSum _ fun i _ => ?_
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
    ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]).continuous.comp h2

lemma mne_lap_bound (f : Euc d → ℝ) (x : Euc d) :
    |Laplacian.laplacian f x| ≤ d * ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [mnb_lap_formula]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i : Fin d, |iteratedFDeriv ℝ 2 f x ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]|
      ≤ ∑ i : Fin d, ‖iteratedFDeriv ℝ 2 f x‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Real.norm_eq_abs]
        refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
        simp [Fin.prod_univ_two]
    _ = d * ‖iteratedFDeriv ℝ 2 f x‖ := by simp

lemma mne_movDiv_cont {Y : Euc d → Euc d} (hY : ContDiff ℝ 1 Y) : Continuous (movDiv Y) := by
  unfold movDiv
  refine continuous_finsetSum _ fun i _ => ?_
  have h1 : Continuous (fderiv ℝ Y) := hY.continuous_fderiv one_ne_zero
  exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp (h1.clm_apply continuous_const)

lemma mne_movDiv_bound (Y : Euc d → Euc d) (x : Euc d) : |movDiv Y x| ≤ d * ‖fderiv ℝ Y x‖ := by
  unfold movDiv
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i : Fin d, |fderiv ℝ Y x (EuclideanSpace.single i 1) i| ≤ ∑ i : Fin d, ‖fderiv ℝ Y x‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Real.norm_eq_abs]
        refine (PiLp.norm_apply_le _ i).trans ?_
        refine ((fderiv ℝ Y x).le_opNorm _).trans ?_
        simp
    _ = d * ‖fderiv ℝ Y x‖ := by simp

lemma mne_movDiv_sub {A B : Euc d → Euc d} {x : Euc d} (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    movDiv (fun y => A y - B y) x = movDiv A x - movDiv B x := by
  unfold movDiv
  have h : fderiv ℝ (fun y => A y - B y) x = fderiv ℝ A x - fderiv ℝ B x :=
    (hA.hasFDerivAt.sub hB.hasFDerivAt).fderiv
  rw [h, ← Finset.sum_sub_distrib]
  rfl


lemma mne_Fo_sub (H : Mov2dTh d s β q ρ) (u u' : OscSpace d (m : ℝ)) (x : Euc d) :
    mneFo d s ρ hm (u - u') x = mneFo d s ρ hm u x - mneFo d s ρ hm u' x := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  obtain ⟨K1, hK1, hW⟩ := mnc_hu_rgW H (mne_hn hm)
  have e : u - u' = u + (-1 : ℝ) • u' := by rw [neg_one_smul]; rfl
  have hsm : mnc_hu ρ (mne_hn hm) ((-1 : ℝ) • u') = fun y => (-1) * mnc_hu ρ (mne_hn hm) u' y :=
    mnc_hu_smul ρ (mne_hn hm) (-1) u'
  have h1 := mnc_force_add hd1 H.hs0 H.hsd (mul_nonneg hK1 (norm_nonneg u)) (mul_nonneg hK1 (norm_nonneg ((-1 : ℝ) • u')))
    (hW u) (hW ((-1 : ℝ) • u')) x
  have h2 := mnc_force_smul hd1 H.hs0 H.hsd (mul_nonneg hK1 (norm_nonneg u')) (hW u') (-1) x
  show movForce d s (mnc_hu ρ (mne_hn hm) (u - u')) x = movForce d s (mnc_hu ρ (mne_hn hm) u) x -
    movForce d s (mnc_hu ρ (mne_hn hm) u') x
  rw [e, mnc_hu_add, h1, hsm, h2]
  simp [sub_eq_add_neg]

lemma mne_grad_sub (H : Mov2dTh d s β q ρ) (u u' : OscSpace d (m : ℝ)) (x : Euc d) :
    gradient (mnc_hu ρ (mne_hn hm) (u - u')) x =
      gradient (mnc_hu ρ (mne_hn hm) u) x - gradient (mnc_hu ρ (mne_hn hm) u') x := by
  have h1 := (mne_hu_cd hm H u).differentiable (by norm_num) x
  have h2 := (mne_hu_cd hm H u').differentiable (by norm_num) x
  rw [mne_hu_sub hm u u']
  unfold gradient
  rw [show fderiv ℝ (fun y => mnc_hu ρ (mne_hn hm) u y - mnc_hu ρ (mne_hn hm) u' y) x =
      fderiv ℝ (mnc_hu ρ (mne_hn hm) u) x - fderiv ℝ (mnc_hu ρ (mne_hn hm) u') x from (h1.hasFDerivAt.sub h2.hasFDerivAt).fderiv]
  exact map_sub _ _ _

lemma mne_lap_sub (H : Mov2dTh d s β q ρ) (u u' : OscSpace d (m : ℝ)) (x : Euc d) :
    Laplacian.laplacian (mnc_hu ρ (mne_hn hm) (u - u')) x =
      Laplacian.laplacian (mnc_hu ρ (mne_hn hm) u) x - Laplacian.laplacian (mnc_hu ρ (mne_hn hm) u') x := by
  have h1 := ((mne_hu_cd hm H u).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).contDiffAt (x := x)
  have h2 := ((mne_hu_cd hm H u').of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).contDiffAt (x := x)
  rw [mne_hu_sub hm u u']
  exact ContDiffAt.laplacian_sub h1 h2

/-- Joint continuity in `(s,x)` of the five basic quantities of `ρ_{v_s}`. -/
theorem mne_joint (H : Mov2dTh d s β q ρ) {S : Set ℝ} {v : ℝ → OscSpace d (m : ℝ)} (hv : ContinuousOn v S) :
    ContinuousOn (fun p : ℝ × Euc d => mnc_hu ρ (mne_hn hm) (v p.1) p.2) (S ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × Euc d => gradient (mnc_hu ρ (mne_hn hm) (v p.1)) p.2) (S ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × Euc d => Laplacian.laplacian (mnc_hu ρ (mne_hn hm) (v p.1)) p.2) (S ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × Euc d => mneFo d s ρ hm (v p.1) p.2) (S ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × Euc d => movDiv (mneFo d s ρ hm (v p.1)) p.2) (S ×ˢ univ) := by
  obtain ⟨K, hK0, hK⟩ := mne_hu_iter hm H
  obtain ⟨C, hC0, hC⟩ := mne_force_facts (s := s) (β := β) (q := q) (ρ := ρ) hm H
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine mne_joint_lin (Ψ := fun u x => mnc_hu ρ (mne_hn hm) u x) K ?_ ?_ ?_ hv
    · intro u u' x; rw [mne_hu_sub hm u u']
    · intro u x
      have := hK u 0 (by norm_num) x
      rwa [norm_iteratedFDeriv_zero] at this
    · intro u; exact (mne_hu_cd hm H u).continuous
  · refine mne_joint_lin (Ψ := fun u x => gradient (mnc_hu ρ (mne_hn hm) u) x) K ?_ ?_ ?_ hv
    · intro u u' x; rw [mne_grad_sub hm H u u']
    · intro u x
      have := hK u 1 (by norm_num) x
      rw [norm_iteratedFDeriv_one] at this
      rw [mnc_norm_gradient]; exact this
    · intro u
      exact (mne_grad_cd (n := 2) (f := mnc_hu ρ (mne_hn hm) u) (by exact_mod_cast mne_hu_cd hm H u)).continuous
  · refine mne_joint_lin (Ψ := fun u x => Laplacian.laplacian (mnc_hu ρ (mne_hn hm) u) x) (d * K) ?_ ?_ ?_ hv
    · intro u u' x; rw [mne_lap_sub hm H u u']
    · intro u x
      have h2 := hK u 2 (by norm_num) x
      rw [Real.norm_eq_abs]
      refine (mne_lap_bound _ x).trans ?_
      nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    · intro u; exact mne_lap_cont ((mne_hu_cd hm H u).of_le (by norm_num))
  · refine mne_joint_lin (Ψ := fun u x => mneFo d s ρ hm u x) C ?_ ?_ ?_ hv
    · intro u u' x; rw [mne_Fo_sub hm H u u']
    · intro u x; exact (hC u).2.1 x
    · intro u; exact (hC u).1.continuous
  · refine mne_joint_lin (Ψ := fun u x => movDiv (mneFo d s ρ hm u) x) (d * C) ?_ ?_ ?_ hv
    · intro u u' x
      have e : mneFo d s ρ hm (u - u') = fun y => mneFo d s ρ hm u y - mneFo d s ρ hm u' y :=
        funext (mne_Fo_sub hm H u u')
      show movDiv (mneFo d s ρ hm u) x - movDiv (mneFo d s ρ hm u') x = movDiv (mneFo d s ρ hm (u - u')) x
      rw [e, mne_movDiv_sub (((hC u).1.differentiable (by norm_num)) x) (((hC u').1.differentiable (by norm_num)) x)]
    · intro u x
      rw [Real.norm_eq_abs]
      refine (mne_movDiv_bound _ x).trans ?_
      have := (hC u).2.2 x
      nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    · intro u; exact mne_movDiv_cont (hC u).1


/-- The explicit form of the flux divergence `e_u = div Y_u`. -/
theorem mne_e_formulaR (H : Mov2dTh d s β q ρ) (u : OscSpace d (m : ℝ)) (x : Euc d) :
    movDiv (mneY d s q β ρ hm u) x =
      β⁻¹ * Laplacian.laplacian (mneRho ρ hm u) x +
        (mneRho ρ hm u x * (q * d + (movDiv (movForce d s ρ) x + movDiv (mneFo d s ρ hm u) x)) +
          inner ℝ (gradient (mneRho ρ hm u) x)
            (q • x + (movForce d s ρ x + mneFo d s ρ hm u x))) := by
  obtain ⟨C, hC0, hC⟩ := mne_force_facts (s := s) (β := β) (q := q) (ρ := ρ) hm H
  have hRcd := mne_rho_cd hm H u
  have hρ3 : ContDiff ℝ 3 ρ := (mnc_rho_smooth H).of_le (by simp)
  have hh3 := mne_hu_cd hm H u
  set R := mneRho ρ hm u with hRdef
  have hRd : DifferentiableAt ℝ R x := (hRcd.differentiable (by norm_num)) x
  have hgR2 : ContDiff ℝ 1 (gradient R) := by
    have := mne_grad_cd (n := 2) (f := R) (by exact_mod_cast hRcd)
    exact this.of_le (by norm_num)
  have hgRd : DifferentiableAt ℝ (gradient R) x := (hgR2.differentiable (by norm_num)) x
  have hF1 : ContDiff ℝ 1 (movForce d s R) := mne_Fr_cd hm H u
  have hFd : DifferentiableAt ℝ (movForce d s R) x := (hF1.differentiable (by norm_num)) x
  have hF0 := mne_F0_cd hm H
  have hFu := (hC u).1
  have hforce : movForce d s R = fun y => movForce d s ρ y + mneFo d s ρ hm u y := funext (mne_force_split hm H u)
  -- (i) the diffusion part
  have hconst : ∀ (c : ℝ) (F : Euc d → Euc d), DifferentiableAt ℝ F x →
      movDiv (fun y => c • F y) x = c * movDiv F x := by
    intro c F hF
    have := mv1_movDiv_smul (c := fun _ => c) (F := F) (x := x) (differentiableAt_const _) hF
    have h0 : fderiv ℝ (fun _ : Euc d => c) x = 0 := (hasFDerivAt_const c x).fderiv
    rw [this, h0]
    simp
  have h1 : movDiv (fun y => β⁻¹ • gradient R y) x = β⁻¹ * Laplacian.laplacian R x := by
    rw [hconst β⁻¹ (gradient R) hgRd]
    congr 1
    exact HRS.MS.S98.s98_movDiv_gradient (hRcd.of_le (by norm_num)) x
  -- (ii) the transport part
  have hid : DifferentiableAt ℝ (fun y : Euc d => q • y) x :=
    (differentiableAt_id.const_smul q : DifferentiableAt ℝ (fun y : Euc d => q • y) x)
  have hq1 : movDiv (fun y : Euc d => q • y) x = q * d := by
    rw [hconst q (fun y : Euc d => y) differentiableAt_id, mov2a_movDiv_id]
  have hGd : DifferentiableAt ℝ (fun y : Euc d => q • y + movForce d s R y) x := hid.add hFd
  have h2 : movDiv (fun y => R y • (q • y + movForce d s R y)) x =
      R x * (q * d + (movDiv (movForce d s ρ) x + movDiv (mneFo d s ρ hm u) x)) +
        inner ℝ (gradient R x) (q • x + (movForce d s ρ x + mneFo d s ρ hm u x)) := by
    rw [mv1_movDiv_smul hRd hGd, mov2a_sum_fderiv_mul]
    have hadd : movDiv (fun y => q • y + movForce d s R y) x = q * d + movDiv (movForce d s R) x := by
      rw [mov2a_movDiv_add (A := fun y : Euc d => q • y) (B := movForce d s R) hid hFd, hq1]
    rw [hadd, hforce]
    have hd0 : DifferentiableAt ℝ (movForce d s ρ) x := (hF0.differentiable (by norm_num)) x
    have hdu : DifferentiableAt ℝ (mneFo d s ρ hm u) x := (hFu.differentiable (by norm_num)) x
    rw [mov2a_movDiv_add (A := movForce d s ρ) (B := mneFo d s ρ hm u) hd0 hdu]
  -- the sum
  have hsum : movDiv (mneY d s q β ρ hm u) x = β⁻¹ * Laplacian.laplacian R x +
      (R x * (q * d + (movDiv (movForce d s ρ) x + movDiv (mneFo d s ρ hm u) x)) +
        inner ℝ (gradient R x) (q • x + (movForce d s ρ x + mneFo d s ρ hm u x))) := by
    show movDiv (fun y => β⁻¹ • gradient R y + R y • (q • y + movForce d s R y)) x = _
    rw [mov2a_movDiv_add (A := fun y => β⁻¹ • gradient R y) (B := fun y => R y • (q • y + movForce d s R y))
      (hgRd.const_smul β⁻¹ : DifferentiableAt ℝ (fun y => β⁻¹ • gradient R y) x) (hRd.smul hGd), h1, h2]
  exact hsum

/-- The explicit form of the flux divergence `e_u = div Y_u`, split into `ρ` and `h_u`. -/
theorem mne_e_formula (H : Mov2dTh d s β q ρ) (u : OscSpace d (m : ℝ)) (x : Euc d) :
    movDiv (mneY d s q β ρ hm u) x =
      β⁻¹ * (Laplacian.laplacian ρ x + Laplacian.laplacian (mnc_hu ρ (mne_hn hm) u) x) +
        ((ρ x + mnc_hu ρ (mne_hn hm) u x) * (q * d + (movDiv (movForce d s ρ) x + movDiv (mneFo d s ρ hm u) x)) +
          inner ℝ (gradient ρ x + gradient (mnc_hu ρ (mne_hn hm) u) x)
            (q • x + (movForce d s ρ x + mneFo d s ρ hm u x))) := by
  have hρ3 : ContDiff ℝ 3 ρ := (mnc_rho_smooth H).of_le (by simp)
  have hh3 := mne_hu_cd hm H u
  rw [mne_e_formulaR hm H u x]
  have hlap : Laplacian.laplacian (mneRho ρ hm u) x =
      Laplacian.laplacian ρ x + Laplacian.laplacian (mnc_hu ρ (mne_hn hm) u) x :=
    ContDiffAt.laplacian_add (hρ3.of_le (by norm_num)).contDiffAt (hh3.of_le (by norm_num)).contDiffAt
  have hgrad : gradient (mneRho ρ hm u) x = gradient ρ x + gradient (mnc_hu ρ (mne_hn hm) u) x := by
    unfold gradient
    have hd1 : DifferentiableAt ℝ ρ x := (hρ3.differentiable (by norm_num)) x
    have hd2 : DifferentiableAt ℝ (mnc_hu ρ (mne_hn hm) u) x := (hh3.differentiable (by norm_num)) x
    have : fderiv ℝ (mneRho ρ hm u) x = fderiv ℝ ρ x + fderiv ℝ (mnc_hu ρ (mne_hn hm) u) x :=
      (hd1.hasFDerivAt.add hd2.hasFDerivAt).fderiv
    rw [this, map_add]
  rw [hlap, hgrad]

/-- Joint continuity of `(s,x) ↦ e_{v_s}(x) = div Y_{v_s}(x)`. -/
theorem mne_e_joint (H : Mov2dTh d s β q ρ) {S : Set ℝ} {v : ℝ → OscSpace d (m : ℝ)} (hv : ContinuousOn v S) :
    ContinuousOn (fun p : ℝ × Euc d => movDiv (mneY d s q β ρ hm (v p.1)) p.2) (S ×ˢ univ) := by
  obtain ⟨j1, j2, j3, j4, j5⟩ := mne_joint hm H hv
  have hρ2 : ContDiff ℝ 2 ρ := (mnc_rho_smooth H).of_le (by simp)
  have c1 : Continuous fun p : ℝ × Euc d => ρ p.2 := (mnc_rho_smooth H).continuous.comp continuous_snd
  have c2 : Continuous fun p : ℝ × Euc d => Laplacian.laplacian ρ p.2 := (mne_lap_cont hρ2).comp continuous_snd
  have c3 : Continuous fun p : ℝ × Euc d => gradient ρ p.2 :=
    (mnc_grad_contDiff (mnc_rho_smooth H)).comp continuous_snd
  have c4 : Continuous fun p : ℝ × Euc d => movForce d s ρ p.2 := (mne_F0_cd hm H).continuous.comp continuous_snd
  have c5 : Continuous fun p : ℝ × Euc d => movDiv (movForce d s ρ) p.2 :=
    (mne_movDiv_cont (mne_F0_cd hm H)).comp continuous_snd
  have cx : Continuous fun p : ℝ × Euc d => (q • p.2 : Euc d) := (continuous_snd.const_smul q)
  refine ContinuousOn.congr ?_ (fun p _ => mne_e_formula hm H (v p.1) p.2)
  exact (continuousOn_const.mul (c2.continuousOn.add j3)).add
    (((c1.continuousOn.add j1).mul (continuousOn_const.add (c5.continuousOn.add j5))).add
      ((c3.continuousOn.add j2).inner (cx.continuousOn.add (c4.continuousOn.add j4))))

end Inst

end HRS.MS.Mov63

end
