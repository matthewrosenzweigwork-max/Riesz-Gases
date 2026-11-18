import HRS.MS.MfeConfAux7

/-!
# S.B.1, packet F1 (part 3): the pointwise form `A(h)` of the mean-field operator and the weak/strong identity

For a density slice `h` and a potential `V ∈ C³`,
`A(h) = β⁻¹ ∑_k ∂_k∂_k h + ∑_k ∂_k(h (∂_k V + F_k))`, `F = ∇g * h`
(`= β⁻¹Δh + Div(h u_V)` with `u_V = β⁻¹∇log h + ∇g*h + ∇V`).  `sb1_weak_eq_pde`: for `M = -1` and
a smooth compactly supported test function `ψ`, the generator pairing of the weak form
`HRS.MH.DualityRd.mfGen D ψ h` equals `∫ ψ A(h)` (two integrations by parts and `self_pairing_rd_proof`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

open HRS.MP.RdGen HRS.MH.DualityRd

variable {d : ℕ}

/-- the `k`-th basis vector -/
abbrev sb1e (k : Fin d) : Euc d := EuclideanSpace.single k (1 : ℝ)

/-- The `k`-th component of the flux `h (∇V + ∇g * h)`. -/
def sb1Flux (D : Whole.WholeDyn d) (h : Euc d → ℝ) (k : Fin d) (y : Euc d) : ℝ :=
  h y * (fderiv ℝ D.V y (sb1e k) + sb1F d D.s h k y)

/-- `A(h) = β⁻¹ ∑_k ∂_k∂_k h + ∑_k ∂_k (h (∂_kV + F_k))`. -/
def sb1A (D : Whole.WholeDyn d) (h : Euc d → ℝ) (x : Euc d) : ℝ :=
  D.invβ * ∑ k, fderiv ℝ (fun y => fderiv ℝ h y (sb1e k)) x (sb1e k) +
    ∑ k, fderiv ℝ (sb1Flux D h k) x (sb1e k)

/-! ### Integration by parts against a compactly supported function -/

theorem sb1_ibp {ψ g : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g)
    (k : Fin d) :
    ∫ x, ψ x * fderiv ℝ g x (sb1e k) = -∫ x, fderiv ℝ ψ x (sb1e k) * g x := by
  have hψ' : Continuous fun x => fderiv ℝ ψ x (sb1e k) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hg' : Continuous fun x => fderiv ℝ g x (sb1e k) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsupp : HasCompactSupport fun x => fderiv ℝ ψ x (sb1e k) :=
    (hψc.fderiv_apply (𝕜 := ℝ) (sb1e k))
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun x _ => hψ.differentiable (by norm_num) x) (fun x _ => hg.differentiable (by norm_num) x)
  · exact (hψ'.mul hg.continuous).integrable_of_hasCompactSupport (hsupp.mul_right)
  · exact (hψ.continuous.mul hg').integrable_of_hasCompactSupport (hψc.mul_right)
  · exact (hψ.continuous.mul hg.continuous).integrable_of_hasCompactSupport (hψc.mul_right)

/-- `∫ h ∂_k a = -∫ ∂_k h a` when `a` has compact support. -/
theorem sb1_ibp' {h a : Euc d → ℝ} (hh : ContDiff ℝ 1 h) (ha : ContDiff ℝ 1 a) (hac : HasCompactSupport a)
    (k : Fin d) :
    ∫ x, h x * fderiv ℝ a x (sb1e k) = -∫ x, fderiv ℝ h x (sb1e k) * a x := by
  have hh' : Continuous fun x => fderiv ℝ h x (sb1e k) :=
    (hh.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have ha' : Continuous fun x => fderiv ℝ a x (sb1e k) :=
    (ha.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsupp : HasCompactSupport fun x => fderiv ℝ a x (sb1e k) :=
    (hac.fderiv_apply (𝕜 := ℝ) (sb1e k))
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun x _ => hh.differentiable (by norm_num) x) (fun x _ => ha.differentiable (by norm_num) x)
  · exact (hh'.mul ha.continuous).integrable_of_hasCompactSupport (hac.mul_left)
  · exact (hh.continuous.mul ha').integrable_of_hasCompactSupport hsupp.mul_left
  · exact (hh.continuous.mul ha.continuous).integrable_of_hasCompactSupport (hac.mul_left)


/-! ### The potential -/

/-- `V ∈ C³` with `‖D²V‖ ≤ B` (the hypotheses of the frozen S.B.1 statements: `ContDiff ℝ 3 V`, bounded second derivative). -/
structure Sb1Pot (V : Euc d → ℝ) (B : ℝ) : Prop where
  c3 : ContDiff ℝ 3 V
  bd : ∀ x, ‖iteratedFDeriv ℝ 2 V x‖ ≤ B

theorem Sb1Pot.B_nonneg {V : Euc d → ℝ} {B : ℝ} (P : Sb1Pot V B) : 0 ≤ B :=
  (norm_nonneg _).trans (P.bd 0)

theorem sb1_gradV_bound {V : Euc d → ℝ} {B : ℝ} (P : Sb1Pot V B) (x : Euc d) :
    ‖fderiv ℝ V x‖ ≤ ‖fderiv ℝ V 0‖ + B * ‖x‖ := by
  have hd : Differentiable ℝ (fderiv ℝ V) :=
    (P.c3.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ V) (s := Set.univ) (C := B)
    (fun z _ => hd z) (fun z _ => by rw [sb1_norm_fderiv_fderiv]; exact P.bd z) convex_univ
    (Set.mem_univ 0) (Set.mem_univ x)
  rw [sub_zero] at h
  have := norm_le_insert' (fderiv ℝ V x) (fderiv ℝ V 0)
  linarith

theorem sb1_apply_single_le (L : Euc d →L[ℝ] ℝ) (k : Fin d) : |L (sb1e k)| ≤ ‖L‖ := by
  have := L.le_opNorm (sb1e k)
  simpa [sb1e] using this

theorem sb1_dV_k_contDiff {V : Euc d → ℝ} {B : ℝ} (P : Sb1Pot V B) (k : Fin d) :
    ContDiff ℝ 2 (fun y => fderiv ℝ V y (sb1e k)) :=
  (P.c3.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const

theorem sb1_ddk_le (f : Euc d → ℝ) {x : Euc d} (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (k : Fin d) :
    |fderiv ℝ (fun y => fderiv ℝ f y (sb1e k)) x (sb1e k)| ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  have e : fderiv ℝ (fun y => fderiv ℝ f y (sb1e k)) x = (fderiv ℝ (fderiv ℝ f) x).flip (sb1e k) := by
    rw [fderiv_clm_apply hf (differentiableAt_const _)]
    simp
  rw [e]
  simp only [ContinuousLinearMap.flip_apply]
  calc |fderiv ℝ (fderiv ℝ f) x (sb1e k) (sb1e k)| ≤ ‖fderiv ℝ (fderiv ℝ f) x (sb1e k)‖ :=
        sb1_apply_single_le (fderiv ℝ (fderiv ℝ f) x (sb1e k)) k
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ := by
        have := (fderiv ℝ (fderiv ℝ f) x).le_opNorm (sb1e k)
        simpa [sb1e] using this

theorem sb1_ddV_k_le {V : Euc d → ℝ} {B : ℝ} (P : Sb1Pot V B) (k : Fin d) (x : Euc d) :
    |fderiv ℝ (fun y => fderiv ℝ V y (sb1e k)) x (sb1e k)| ≤ B := by
  have hd : DifferentiableAt ℝ (fderiv ℝ V) x :=
    ((P.c3.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)) x
  refine (sb1_ddk_le V hd k).trans ?_
  rw [sb1_norm_fderiv_fderiv]; exact P.bd x

/-! ### Regularity and bounds of the flux -/

theorem sb1_flux_contDiff (D : Whole.WholeDyn d) {B : ℝ} (P : Sb1Pot D.V B) (hd : 1 ≤ d)
    (hs0 : 0 ≤ D.s) (hsd : D.s < d) {C : ℝ} {h : Euc d → ℝ} (S : Sb1Slice d C h) (k : Fin d) :
    ContDiff ℝ 1 (sb1Flux D h k) := by
  unfold sb1Flux
  have h3 : ContDiff ℝ 1 h := (sb1_slice_facts S).1.of_le (by norm_num)
  have hV : ContDiff ℝ 1 (fun y => fderiv ℝ D.V y (sb1e k)) := (sb1_dV_k_contDiff P k).of_le (by norm_num)
  exact h3.mul (hV.add (sb1F_contDiff hd hs0 hsd S k).1)

theorem sb1_flux_deriv (D : Whole.WholeDyn d) {B : ℝ} (P : Sb1Pot D.V B) (hd : 1 ≤ d)
    (hs0 : 0 ≤ D.s) (hsd : D.s < d) {C : ℝ} {h : Euc d → ℝ} (S : Sb1Slice d C h) (k : Fin d)
    (x : Euc d) :
    fderiv ℝ (sb1Flux D h k) x (sb1e k) =
      fderiv ℝ h x (sb1e k) * (fderiv ℝ D.V x (sb1e k) + sb1F d D.s h k x) +
        h x * (fderiv ℝ (fun y => fderiv ℝ D.V y (sb1e k)) x (sb1e k) +
          fderiv ℝ (sb1F d D.s h k) x (sb1e k)) := by
  have h3 : DifferentiableAt ℝ h x := ((sb1_slice_facts S).1.differentiable (by norm_num)) x
  have hV : DifferentiableAt ℝ (fun y => fderiv ℝ D.V y (sb1e k)) x :=
    ((sb1_dV_k_contDiff P k).differentiable (by norm_num)) x
  have hF : DifferentiableAt ℝ (sb1F d D.s h k) x :=
    (((sb1F_contDiff hd hs0 hsd S k).1).differentiable (by norm_num)) x
  have hVF : DifferentiableAt ℝ (fun y => fderiv ℝ D.V y (sb1e k) + sb1F d D.s h k y) x := hV.add hF
  unfold sb1Flux
  rw [fderiv_fun_mul h3 hVF, fderiv_fun_add hV hF]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring


theorem sb1BF_nonneg {s : ℝ} (hs0 : 0 ≤ s) {C : ℝ} (hC : 0 ≤ C) : 0 ≤ sb1BF d s C := by
  unfold sb1BF
  exact mul_nonneg (rg_sigma_nonneg hs0) (add_nonneg (mul_nonneg hC (rg_near_nonneg s))
    (mul_nonneg (mul_nonneg (by positivity) hC) rg_W_nonneg))

/-- The uniform bound of `A(h)`. -/
def sb1KA (d : ℕ) (νb C B G0 BF : ℝ) : ℝ :=
  |νb| * (d * C) + d * (C * (G0 + BF + B) + C * (B + BF))

theorem sb1A_bound (D : Whole.WholeDyn d) {B : ℝ} (P : Sb1Pot D.V B) (hd : 1 ≤ d)
    (hs0 : 0 ≤ D.s) (hsd : D.s < d) {C : ℝ} {h : Euc d → ℝ} (S : Sb1Slice d C h) (x : Euc d) :
    |sb1A D h x| ≤ sb1KA d D.invβ C B ‖fderiv ℝ D.V 0‖ (sb1BF d D.s C) := by
  obtain ⟨hc3, h0, h1, h1', h2', h0'⟩ := sb1_slice_facts S
  have hC := S.C_nonneg
  have hB := P.B_nonneg
  have hBF := sb1BF_nonneg (d := d) hs0 hC
  set G0 := ‖fderiv ℝ D.V 0‖ with hG0
  set BF := sb1BF d D.s C with hBFdef
  have hG0nn : 0 ≤ G0 := norm_nonneg _
  have hh2 : DifferentiableAt ℝ (fderiv ℝ h) x :=
    ((hc3.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)) x
  -- the Laplacian-type term
  have hlap : |∑ k, fderiv ℝ (fun y => fderiv ℝ h y (sb1e k)) x (sb1e k)| ≤ d * C := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |fderiv ℝ (fun y => fderiv ℝ h y (sb1e k)) x (sb1e k)| ≤ ∑ _k : Fin d, C :=
          Finset.sum_le_sum fun k _ => (sb1_ddk_le h hh2 k).trans (h2' x)
      _ = d * C := by simp
  -- the flux terms
  have hflux : ∀ k : Fin d, |fderiv ℝ (sb1Flux D h k) x (sb1e k)| ≤
      C * (G0 + BF + B) + C * (B + BF) := by
    intro k
    rw [sb1_flux_deriv D P hd hs0 hsd S k x]
    have e1 : |fderiv ℝ h x (sb1e k)| ≤ C * (1 + ‖x‖)⁻¹ := by
      refine (sb1_apply_single_le _ k).trans ((h1 x).trans ?_)
      have : (1 + ‖x‖) ^ (-((d : ℝ) + 1)) ≤ (1 + ‖x‖)⁻¹ := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x])
          (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
      exact mul_le_mul_of_nonneg_left this hC
    have e2 : |fderiv ℝ D.V x (sb1e k) + sb1F d D.s h k x| ≤ G0 + BF + B * ‖x‖ := by
      refine (abs_add_le _ _).trans ?_
      have a1 : |fderiv ℝ D.V x (sb1e k)| ≤ G0 + B * ‖x‖ :=
        (sb1_apply_single_le _ k).trans (sb1_gradV_bound P x)
      have a2 : |sb1F d D.s h k x| ≤ BF := by
        have := (sb1F_contDiff hd hs0 hsd S k).2 0 (Nat.zero_le _) x
        rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      linarith
    have e3 : |fderiv ℝ (sb1F d D.s h k) x (sb1e k)| ≤ BF := by
      have := (sb1F_contDiff hd hs0 hsd S k).2 1 le_rfl x
      rw [norm_iteratedFDeriv_one] at this
      exact (sb1_apply_single_le _ k).trans this
    have e4 := sb1_ddV_k_le P k x
    have e5 : |h x| ≤ C := by rw [← Real.norm_eq_abs]; exact h0' x
    have hx : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
    have key : C * (1 + ‖x‖)⁻¹ * (G0 + BF + B * ‖x‖) ≤ C * (G0 + BF + B) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hC
      rw [inv_mul_le_iff₀ hx]
      nlinarith [norm_nonneg x]
    calc |fderiv ℝ h x (sb1e k) * (fderiv ℝ D.V x (sb1e k) + sb1F d D.s h k x) +
          h x * (fderiv ℝ (fun y => fderiv ℝ D.V y (sb1e k)) x (sb1e k) +
            fderiv ℝ (sb1F d D.s h k) x (sb1e k))|
        ≤ |fderiv ℝ h x (sb1e k)| * |fderiv ℝ D.V x (sb1e k) + sb1F d D.s h k x| +
          |h x| * (|fderiv ℝ (fun y => fderiv ℝ D.V y (sb1e k)) x (sb1e k)| +
            |fderiv ℝ (sb1F d D.s h k) x (sb1e k)|) := by
          refine (abs_add_le _ _).trans (add_le_add (le_of_eq (abs_mul _ _)) ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
      _ ≤ C * (1 + ‖x‖)⁻¹ * (G0 + BF + B * ‖x‖) + C * (B + BF) := by
          refine add_le_add (mul_le_mul e1 e2 (abs_nonneg _) (by positivity)) ?_
          exact mul_le_mul e5 (add_le_add e4 e3) (by positivity) hC
      _ ≤ _ := by linarith
  unfold sb1A sb1KA
  calc |D.invβ * ∑ k, fderiv ℝ (fun y => fderiv ℝ h y (sb1e k)) x (sb1e k) +
        ∑ k, fderiv ℝ (sb1Flux D h k) x (sb1e k)|
      ≤ |D.invβ| * |∑ k, fderiv ℝ (fun y => fderiv ℝ h y (sb1e k)) x (sb1e k)| +
        |∑ k, fderiv ℝ (sb1Flux D h k) x (sb1e k)| := by
        refine (abs_add_le _ _).trans (add_le_add (le_of_eq (abs_mul _ _)) le_rfl)
    _ ≤ |D.invβ| * (d * C) + d * (C * (G0 + BF + B) + C * (B + BF)) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hlap (abs_nonneg _)) ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ k, |fderiv ℝ (sb1Flux D h k) x (sb1e k)|
            ≤ ∑ _k : Fin d, (C * (G0 + BF + B) + C * (B + BF)) :=
              Finset.sum_le_sum fun k _ => hflux k
          _ = d * (C * (G0 + BF + B) + C * (B + BF)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]


/-! ### The weak / strong identity -/

theorem sb1_matVec_neg_one (v : Euc d) : Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) v = -v := by
  simp [Torus.matVec]

theorem sb1_grad_apply (f : Euc d → ℝ) (x : Euc d) (k : Fin d) :
    gradient f x k = fderiv ℝ f x (sb1e k) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Euc d) (x := sb1e k) (y := fderiv ℝ f x)
  unfold gradient
  rw [← h]
  simp only [sb1e, EuclideanSpace.inner_single_right] at h ⊢
  simpa using h

theorem sb1_inner_eq_sum (a b : Euc d) : inner ℝ a b = ∑ k, a k * b k := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem sb1_laplacian_eq {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (x : Euc d) :
    Laplacian.laplacian ψ x = ∑ k, fderiv ℝ (fun y => fderiv ℝ ψ y (sb1e k)) x (sb1e k) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis ψ (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const _)]
  simp [sb1e]


/-- **Weak = strong**: for `M = -1`, a density slice `h` and a `C²` compactly supported test function `ψ`,
`mfGen D ψ h = ∫ ψ A(h)` (two integrations by parts and the self-pairing identity). -/
theorem sb1_weak_eq_pde (D : Whole.WholeDyn d) {B : ℝ} (P : Sb1Pot D.V B) (hd : 1 ≤ d)
    (hs0 : 0 ≤ D.s) (hsd : D.s < d) (hM : D.M = -1) {C : ℝ} {h : Euc d → ℝ} (S : Sb1Slice d C h)
    (R : RegSliceRd h) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    mfGen D ψ h = ∫ x, ψ x * sb1A D h x := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hψb : MemCb 2 ψ := db1_memCb_of_compact hψ hψc
  obtain ⟨hh3, -, -, -, -, -⟩ := sb1_slice_facts S
  have hh1 : ContDiff ℝ 1 h := hh3.of_le (by norm_num)
  set a : Fin d → Euc d → ℝ := fun k y => fderiv ℝ ψ y (sb1e k) with ha
  have ha1 : ∀ k, ContDiff ℝ 1 (a k) := fun k =>
    (hψ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hac : ∀ k, HasCompactSupport (a k) := fun k => hψc.fderiv_apply (𝕜 := ℝ) (sb1e k)
  have hg : ∀ k, ContDiff ℝ 1 (fun y => fderiv ℝ h y (sb1e k)) := fun k =>
    ((hh3.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).of_le (by norm_num)
  have hfl : ∀ k, ContDiff ℝ 1 (sb1Flux D h k) := fun k => sb1_flux_contDiff D P hd hs0 hsd S k
  -- integrations by parts
  have step1 : ∀ k, ∫ x, ψ x * fderiv ℝ (fun y => fderiv ℝ h y (sb1e k)) x (sb1e k) =
      ∫ x, h x * fderiv ℝ (a k) x (sb1e k) := by
    intro k
    have e1 := sb1_ibp hψ1 hψc (hg k) k
    have e2 := sb1_ibp (ha1 k) (hac k) hh1 k
    rw [e1]
    have e3 : ∫ x, a k x * fderiv ℝ h x (sb1e k) = -∫ x, fderiv ℝ (a k) x (sb1e k) * h x := e2
    calc -∫ x, fderiv ℝ ψ x (sb1e k) * fderiv ℝ h x (sb1e k)
        = -(-∫ x, fderiv ℝ (a k) x (sb1e k) * h x) := by rw [← e3]
      _ = ∫ x, h x * fderiv ℝ (a k) x (sb1e k) := by
          rw [neg_neg]; exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have step2 : ∀ k, ∫ x, ψ x * fderiv ℝ (sb1Flux D h k) x (sb1e k) = -∫ x, a k x * sb1Flux D h k x :=
    fun k => sb1_ibp hψ1 hψc (hfl k) k
  -- integrability
  have hint1 : ∀ k, Integrable fun x => ψ x * fderiv ℝ (fun y => fderiv ℝ h y (sb1e k)) x (sb1e k) :=
    fun k => (hψ1.continuous.mul ((hg k).continuous_fderiv (by norm_num) |>.clm_apply continuous_const)
      ).integrable_of_hasCompactSupport hψc.mul_right
  have hint2 : ∀ k, Integrable fun x => ψ x * fderiv ℝ (sb1Flux D h k) x (sb1e k) :=
    fun k => (hψ1.continuous.mul ((hfl k).continuous_fderiv (by norm_num) |>.clm_apply continuous_const)
      ).integrable_of_hasCompactSupport hψc.mul_right
  have hint3 : ∀ k, Integrable fun x => h x * fderiv ℝ (a k) x (sb1e k) :=
    fun k => (hh1.continuous.mul ((ha1 k).continuous_fderiv (by norm_num) |>.clm_apply continuous_const)
      ).integrable_of_hasCompactSupport (((hac k).fderiv_apply (𝕜 := ℝ) (sb1e k)).mul_left)
  have hint4 : ∀ k, Integrable fun x => a k x * sb1Flux D h k x :=
    fun k => ((ha1 k).continuous.mul (hfl k).continuous).integrable_of_hasCompactSupport (hac k).mul_right
  -- the right-hand side
  have hRHS : ∫ x, ψ x * sb1A D h x =
      D.invβ * (∑ k, ∫ x, h x * fderiv ℝ (a k) x (sb1e k)) - (∑ k, ∫ x, a k x * sb1Flux D h k x) := by
    have e : (fun x => ψ x * sb1A D h x) = fun x => ∑ k, (D.invβ * (ψ x *
        fderiv ℝ (fun y => fderiv ℝ h y (sb1e k)) x (sb1e k)) +
        ψ x * fderiv ℝ (sb1Flux D h k) x (sb1e k)) := by
      funext x
      unfold sb1A
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hI : ∀ k ∈ (Finset.univ : Finset (Fin d)), Integrable (fun x => D.invβ * (ψ x *
        fderiv ℝ (fun y => fderiv ℝ h y (sb1e k)) x (sb1e k)) +
        ψ x * fderiv ℝ (sb1Flux D h k) x (sb1e k)) := fun k _ => ((hint1 k).const_mul _).add (hint2 k)
    have step : ∀ k : Fin d, ∫ x, (D.invβ * (ψ x * fderiv ℝ (fun y => fderiv ℝ h y (sb1e k)) x (sb1e k)) +
        ψ x * fderiv ℝ (sb1Flux D h k) x (sb1e k)) =
        D.invβ * (∫ x, h x * fderiv ℝ (a k) x (sb1e k)) - (∫ x, a k x * sb1Flux D h k x) := by
      intro k
      rw [integral_add ((hint1 k).const_mul _) (hint2 k), integral_const_mul, step1, step2]
      ring
    rw [e, integral_finsetSum _ hI, Finset.sum_congr rfl fun k _ => step k, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
  -- the left-hand side
  have hdV : ∀ k, Continuous fun x => fderiv ℝ D.V x (sb1e k) := fun k =>
    (sb1_dV_k_contDiff P k).continuous
  have hF1 : ∀ k, ContDiff ℝ 1 (sb1F d D.s h k) := fun k => (sb1F_contDiff hd hs0 hsd S k).1
  have iT2 : ∀ k, Integrable fun x => fderiv ℝ D.V x (sb1e k) * (h x * a k x) := fun k =>
    ((hdV k).mul (hh1.continuous.mul (ha1 k).continuous)).integrable_of_hasCompactSupport
      ((hac k).mul_left.mul_left)
  have iT3 : ∀ k, Integrable fun x => a k x * (h x * sb1F d D.s h k x) := fun k =>
    ((ha1 k).continuous.mul (hh1.continuous.mul (hF1 k).continuous)).integrable_of_hasCompactSupport
      ((hac k).mul_right)
  have hLHS : mfGen D ψ h = D.invβ * (∑ k, ∫ x, h x * fderiv ℝ (a k) x (sb1e k)) -
      (∑ k, ∫ x, a k x * sb1Flux D h k x) := by
    have hself := (self_pairing_rd_proof D hd hs0 hsd R hψb).1
    have hpair := Whole.Q09A.pair_withDensityReal S.dens
      (fun x => D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x))
    unfold mfGen
    rw [hpair, hself]
    have ef : (fun x => h x * (D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x)))
        = fun x => ∑ k, (D.invβ * (h x * fderiv ℝ (a k) x (sb1e k)) -
            fderiv ℝ D.V x (sb1e k) * (h x * a k x)) := by
      funext x
      rw [sb1_laplacian_eq hψ, sb1_inner_eq_sum, mul_sub, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sb1_grad_apply, sb1_grad_apply]
      simp only [ha]
      ring
    have eg : (fun x => h x * inner ℝ (gradient ψ x)
        (Torus.matVec D.M (Whole.convGradConvW (Whole.rieszKernelGrad d D.s) h x)))
        = fun x => -∑ k, a k x * (h x * sb1F d D.s h k x) := by
      funext x
      rw [hM, sb1_matVec_neg_one, inner_neg_right, sb1_inner_eq_sum, mul_neg, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sb1_grad_apply]
      simp only [ha, sb1F]
      ring
    have if_ : Integrable fun x => ∑ k, (D.invβ * (h x * fderiv ℝ (a k) x (sb1e k)) -
            fderiv ℝ D.V x (sb1e k) * (h x * a k x)) :=
      integrable_finsetSum _ fun k _ => ((hint3 k).const_mul _).sub (iT2 k)
    have ig_ : Integrable fun x => -∑ k, a k x * (h x * sb1F d D.s h k x) :=
      (integrable_finsetSum _ fun k _ => iT3 k).neg
    have hI3 : ∀ k ∈ (Finset.univ : Finset (Fin d)), Integrable (fun x => D.invβ * (h x *
        fderiv ℝ (a k) x (sb1e k)) - fderiv ℝ D.V x (sb1e k) * (h x * a k x)) :=
      fun k _ => ((hint3 k).const_mul _).sub (iT2 k)
    have hI4 : ∀ k ∈ (Finset.univ : Finset (Fin d)), Integrable (fun x => a k x * (h x * sb1F d D.s h k x)) :=
      fun k _ => iT3 k
    rw [ef, eg, integral_neg, integral_finsetSum _ hI3, integral_finsetSum _ hI4]
    have step : ∀ k : Fin d, ∫ x, (D.invβ * (h x * fderiv ℝ (a k) x (sb1e k)) -
        fderiv ℝ D.V x (sb1e k) * (h x * a k x)) = D.invβ * (∫ x, h x * fderiv ℝ (a k) x (sb1e k)) -
        (∫ x, fderiv ℝ D.V x (sb1e k) * (h x * a k x)) := fun k => by
      rw [integral_sub ((hint3 k).const_mul _) (iT2 k), integral_const_mul]
    have step' : ∀ k : Fin d, ∫ x, a k x * sb1Flux D h k x =
        (∫ x, fderiv ℝ D.V x (sb1e k) * (h x * a k x)) + ∫ x, a k x * (h x * sb1F d D.s h k x) := fun k => by
      rw [← integral_add (iT2 k) (iT3 k)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [sb1Flux]
      ring
    rw [Finset.sum_congr rfl fun k _ => step k, Finset.sum_congr rfl fun k _ => step' k,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hLHS, hRHS]

end HRS.MS.MfeConf
