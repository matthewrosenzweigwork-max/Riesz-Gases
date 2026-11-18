import HRS.MS.MovLinAux8

/-!
# MOV-2d, part 3: the ground state, generator at `0`, the Schwartz core, `L²_0`, uniqueness

Namespace `HRS.MS.MovLin`, helpers `mov2d_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff
open Laplacian

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

section Thermal

variable {s : ℝ} {β q : ℝ} {ρ : Euc d → ℝ}

/-! ## A. The ground state `√ρ` is Schwartz, and `∫ (S φ) √ρ = 0` -/

lemma mov2d_rho_data (H : Mov2dTh d s β q ρ) :
    ContDiff ℝ ∞ ρ ∧ (∀ x, 0 < ρ x) := by
  obtain ⟨B, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  exact ⟨hR.smooth, hR.pos⟩

/-- `√ρ` is a Schwartz function. -/
lemma mov2d_sqrt_schwartz (H : Mov2dTh d s β q ρ) : ∃ ψ : 𝓢R, (⇑ψ : Euc d → ℝ) = fun x => Real.sqrt (ρ x) := by
  obtain ⟨h1, -, c, hc, hk⟩ := HRS.MS.Mov0.mv0_sqrt_gauss_thermal H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  exact movc1_G_schwartz ⟨h1, c, hc, hk⟩

lemma mov2d_grad_coord (f : Euc d → ℝ) (x : Euc d) (i : Fin d) :
    gradient f x i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
  have := HRS.MS.PoisKolm.kl_inner_gradient f x (EuclideanSpace.single i 1)
  simp only [EuclideanSpace.inner_single_left] at this
  simpa using this

lemma mov2d_fderiv_coord {F : Euc d → Euc d} {y : Euc d} (hF : DifferentiableAt ℝ F y) (i : Fin d)
    (e : Euc d) :
    fderiv ℝ (fun z => F z i) y e = fderiv ℝ F y e i := by
  have h1 : HasFDerivAt (fun z => F z i) ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp (fderiv ℝ F y)) y :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp y hF.hasFDerivAt
  rw [h1.fderiv]
  rfl

/-- `P^† √ρ = 0`. -/
lemma mov2d_Padj_sqrt (H : Mov2dTh d s β q ρ) :
    movPadj d s ρ (fun x => Real.sqrt (ρ x)) = fun _ => 0 := by
  obtain ⟨hsm, hpos⟩ := mov2d_rho_data H
  have hdiff : Differentiable ℝ ρ := hsm.differentiable (by simp)
  funext x
  unfold movPadj
  have hk : (fun z => Real.sqrt (ρ z) * Real.sqrt (ρ z)) = ρ := by
    funext z; exact Real.mul_self_sqrt (hpos z).le
  rw [hk]
  have hop : movPadjOp d ρ ρ = fun _ => 0 := by
    funext y
    unfold movPadjOp
    have e1 : ∀ i : Fin d, (fun z => gradient (fun u => Real.log (ρ u)) z i * ρ z) =
        fun z => gradient ρ z i := by
      intro i; funext z
      rw [mov2d_grad_coord, mov2d_grad_coord]
      have := (hdiff z).hasFDerivAt.log (hpos z).ne'
      rw [this.fderiv]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      field_simp [(hpos z).ne']
    simp_rw [e1]
    have hgd : DifferentiableAt ℝ (fun z => gradient ρ z) y := mov2a_gradient_diff hsm y
    have e2 : ∑ i : Fin d, fderiv ℝ (fun z => gradient ρ z i) y (EuclideanSpace.single i 1) =
        movDiv (fun z => gradient ρ z) y := by
      unfold movDiv
      exact Finset.sum_congr rfl fun i _ => mov2d_fderiv_coord hgd i _
    rw [e2, mov2a_movDiv_gradient hsm]
    simp
  rw [hop]
  simp [HRS.Whole.convFun]

/-- **The ground state is a null vector of the adjoint**: `∫ (S φ) √ρ = 0` for Schwartz `φ`. -/
theorem mov2d_S_orth (H : Mov2dTh d s β q ρ) (φ : 𝓢R) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) :
    ∫ x, movS d s β ρ φ x * Real.sqrt (ρ x) = 0 := by
  obtain ⟨hsm, hpos⟩ := mov2d_rho_data H
  have hS : ∀ x, movS d s β ρ φ x = β⁻¹ * (-Laplacian.laplacian (φ : Euc d → ℝ) x + mov2a_V ρ x * φ x)
      + movP d s ρ φ x := fun x => mov_S_ground_state H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ φ x
  have hΔ : ∀ x, Laplacian.laplacian (fun y => Real.sqrt (ρ y)) x = Real.sqrt (ρ x) * mov2a_V ρ x :=
    mov2a_laplacian_sqrt hsm hpos
  obtain ⟨χ, hχ⟩ := mov_P_schwartz H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ φ
  -- the three pieces
  have hP : ∫ x, movP d s ρ φ x * Real.sqrt (ρ x) = 0 := by
    have := mov_P_adj_pairing H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ φ ψ0
    rw [hψ0] at this
    simp only at this
    rw [this]
    have h0 := mov2d_Padj_sqrt H
    have : ∀ x, φ x * movPadj d s ρ (fun x => Real.sqrt (ρ x)) x = 0 := fun x => by rw [h0]; simp
    simp_rw [this]
    simp
  have e1 : ∀ x, (Δ φ : 𝓢R) x = Laplacian.laplacian (φ : Euc d → ℝ) x := fun x => SchwartzMap.laplacian_apply φ x
  have e2 : ∀ x, (Δ ψ0 : 𝓢R) x = Real.sqrt (ρ x) * mov2a_V ρ x := fun x => by
    rw [SchwartzMap.laplacian_apply, hψ0]; exact hΔ x
  have hLap : ∫ x, Laplacian.laplacian (φ : Euc d → ℝ) x * Real.sqrt (ρ x) =
      ∫ x, φ x * (Real.sqrt (ρ x) * mov2a_V ρ x) := by
    have h := SchwartzMap.integral_smul_laplacian_right_eq_left (μ := (volume : Measure (Euc d))) ψ0 φ
    simp only [smul_eq_mul, e1, e2, hψ0] at h
    calc ∫ x, Laplacian.laplacian (φ : Euc d → ℝ) x * Real.sqrt (ρ x)
        = ∫ x, Real.sqrt (ρ x) * Laplacian.laplacian (φ : Euc d → ℝ) x := by simp_rw [mul_comm]
      _ = ∫ x, (Real.sqrt (ρ x) * mov2a_V ρ x) * φ x := h
      _ = _ := by simp_rw [mul_comm]
  have I1 : Integrable (fun x => Laplacian.laplacian (φ : Euc d → ℝ) x * Real.sqrt (ρ x)) := by
    have := mov2d_integrable_schwartz_mul (Δ φ : 𝓢R) ψ0
    simpa only [e1, hψ0] using this
  have I2 : Integrable (fun x => φ x * (Real.sqrt (ρ x) * mov2a_V ρ x)) := by
    have := mov2d_integrable_schwartz_mul φ (Δ ψ0 : 𝓢R)
    simpa only [e2] using this
  have I3 : Integrable (fun x => movP d s ρ φ x * Real.sqrt (ρ x)) := by
    have := mov2d_integrable_schwartz_mul χ ψ0
    simpa only [hψ0, show (⇑χ : Euc d → ℝ) = movP d s ρ φ from hχ] using this
  have hexp : ∀ x, movS d s β ρ φ x * Real.sqrt (ρ x) =
      β⁻¹ * (-(Laplacian.laplacian (φ : Euc d → ℝ) x * Real.sqrt (ρ x)) +
        φ x * (Real.sqrt (ρ x) * mov2a_V ρ x)) + movP d s ρ φ x * Real.sqrt (ρ x) := fun x => by
    rw [hS x]; ring
  have hn1 : Integrable (fun x => -(Laplacian.laplacian (φ : Euc d → ℝ) x * Real.sqrt (ρ x))) := I1.neg
  have hI12 : Integrable (fun x => -(Laplacian.laplacian (φ : Euc d → ℝ) x * Real.sqrt (ρ x)) +
      φ x * (Real.sqrt (ρ x) * mov2a_V ρ x)) := I1.neg.add I2
  simp_rw [hexp]
  rw [integral_add (hI12.const_mul β⁻¹) I3, integral_const_mul, integral_add hn1 I2,
    integral_neg, hLap, hP]
  ring

end Thermal

/-! ## B. `S_0` on Schwartz functions: Schwartz-ness and the coefficient identity -/

section S0gen

variable {β q : ℝ}

lemma mov2d_S0_schwartz (φ : 𝓢R) : ∃ χ : 𝓢R, (⇑χ : Euc d → ℝ) = mov_S0 d β q φ := by
  refine ⟨β⁻¹ • (-(Δ φ) + ((β * q / 2) ^ 2) • ∑ j : Fin d, mova1_X j (mova1_X j φ)) -
    (β⁻¹ * (β * q) * (d / 2)) • φ, ?_⟩
  funext x
  have e1 : (Δ φ : 𝓢R) x = Laplacian.laplacian (φ : Euc d → ℝ) x := SchwartzMap.laplacian_apply φ x
  have e2 : (∑ j : Fin d, mova1_X j (mova1_X j φ) : 𝓢R) x = ‖x‖ ^ 2 * φ x := by
    simp only [SchwartzMap.sum_apply, mova1_X_apply]
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [mov_S0, sub_apply, smul_apply, add_apply, neg_apply, e1, e2, smul_eq_mul]
  ring

/-- The dilation `y ↦ c • y` as a continuous linear equivalence. -/
def mov2d_dilEquiv (d : ℕ) (c : ℝ) (hc : c ≠ 0) : Euc d ≃L[ℝ] Euc d :=
  ContinuousLinearEquiv.equivOfInverse (c • ContinuousLinearMap.id ℝ (Euc d))
    (c⁻¹ • ContinuousLinearMap.id ℝ (Euc d)) (fun x => by simp [smul_smul, inv_mul_cancel₀ hc, mul_inv_cancel₀ hc])
    (fun x => by simp [smul_smul, inv_mul_cancel₀ hc, mul_inv_cancel₀ hc])

lemma mov2d_dilEquiv_apply (c : ℝ) (hc : c ≠ 0) (y : Euc d) : mov2d_dilEquiv d c hc y = c • y := by
  simp [mov2d_dilEquiv]

/-- The dilated Schwartz function `y ↦ φ(c y)`. -/
def mov2d_dilS (c : ℝ) (hc : c ≠ 0) (φ : 𝓢R) : 𝓢R :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (mov2d_dilEquiv d c hc) φ

lemma mov2d_dilS_apply (c : ℝ) (hc : c ≠ 0) (φ : 𝓢R) (y : Euc d) : mov2d_dilS c hc φ y = φ (c • y) := by
  simp [mov2d_dilS, mov2d_dilEquiv_apply]

/-- **Conjugation of `S_0` by the dilation**: with `u(y) = φ(y/ℓ)`, `(S_0 φ)(y/ℓ) = (q/2)(𝓗 u - (d+1) u)`. -/
lemma mov2d_S0_dil (hβ : 0 < β) (hq : 0 < q) (φ : 𝓢R) (y : Euc d) :
    mov_S0 d β q φ ((mov_dil β q)⁻¹ • y) =
      (q / 2) * (oscillatorOp (fun z => φ ((mov_dil β q)⁻¹ • z)) y - (d + 1) * φ ((mov_dil β q)⁻¹ • y)) := by
  set l := mov_dil β q with hl
  have hlp : 0 < l := mov_dil_pos hβ hq
  have hl2 : l ^ 2 = β * q / 2 := mov_dil_sq hβ hq
  have hc : ContDiff ℝ 2 (φ : Euc d → ℝ) := (φ.smooth 2)
  have hlap := mov2b_laplacian_comp_smul hc l⁻¹ y
  unfold mov_S0 oscillatorOp
  have hn : ‖(l⁻¹ • y)‖ ^ 2 = (l ^ 2)⁻¹ * ‖y‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hlp]; field_simp
  rw [hlap, hn]
  have hm : β * q / 2 = l ^ 2 := hl2.symm
  have hbq : β * q = 2 * l ^ 2 := by linarith
  have hq' : q / 2 = l ^ 2 / β := by field_simp; linarith
  have hl0 : l ≠ 0 := hlp.ne'
  rw [hm, hbq, hq']
  field_simp
  ring

lemma mov2d_dcoeff_sub (hβ : 0 < β) (hq : 0 < q) {f g : Euc d → ℝ}
    (hf : MemLp f 2 (volume : Measure (Euc d))) (hg : MemLp g 2 (volume : Measure (Euc d)))
    (α : MultiIndex d) :
    mov2b_dcoeff (mov_dil β q) (fun z => f z - g z) α =
      mov2b_dcoeff (mov_dil β q) f α - mov2b_dcoeff (mov_dil β q) g α := by
  have hl := mov_dil_pos hβ hq
  rw [mov2b_dcoeff_eq hl, mov2b_dcoeff_eq hl, mov2b_dcoeff_eq hl]
  have := mova2_coeff_sub (mov2b_memLp_inv hl hf) (mov2b_memLp_inv hl hg) α
  rw [this]; ring

lemma mov2d_schwartz_memLp (φ : 𝓢R) : MemLp (fun z => φ z) 2 (volume : Measure (Euc d)) := φ.memLp 2

/-- The dilated Hermite coefficients of `S_0 φ`: multiplication by `q |α|`. -/
lemma mov2d_dcoeff_S0 (hβ : 0 < β) (hq : 0 < q) (φ χ : 𝓢R) (hχ : (⇑χ : Euc d → ℝ) = mov_S0 d β q φ)
    (α : MultiIndex d) :
    mov2b_dcoeff (mov_dil β q) (fun z => χ z) α =
      q * (α.degree : ℝ) * mov2b_dcoeff (mov_dil β q) (fun z => φ z) α := by
  have hlp := mov_dil_pos hβ hq
  set l := mov_dil β q with hl
  rw [mov2b_dcoeff_eq hlp, mov2b_dcoeff_eq hlp]
  have hl0 : (l⁻¹ : ℝ) ≠ 0 := inv_ne_zero hlp.ne'
  set u : 𝓢R := mov2d_dilS l⁻¹ hl0 φ with hudef
  have hu : ∀ y, u y = φ (l⁻¹ • y) := mov2d_dilS_apply _ _ _
  set v : 𝓢R := mov2d_dilS l⁻¹ hl0 χ with hvdef
  have hv : ∀ y, v y = χ (l⁻¹ • y) := mov2d_dilS_apply _ _ _
  have hF : ∀ y, v y = (q / 2) * (oscillatorOp (⇑u) y - (d + 1) * u y) := by
    intro y
    rw [hv, show χ (l⁻¹ • y) = mov_S0 d β q φ (l⁻¹ • y) from congrFun hχ _,
      mov2d_S0_dil hβ hq φ y]
    have : (fun z => φ (l⁻¹ • z)) = ⇑u := funext fun z => (hu z).symm
    rw [this, hu]
  obtain ⟨hh, hhp⟩ := hermiteFunD_poly α
  have Iu : Integrable (fun y => u y * hermiteFunD α y) := int_schwartz_mul u _ hh hhp
  have Iv : Integrable (fun y => v y * hermiteFunD α y) := int_schwartz_mul v _ hh hhp
  have hq0 : q ≠ 0 := hq.ne'
  have IH : Integrable (fun y => oscillatorOp (⇑u) y * hermiteFunD α y) := by
    have e : ∀ y, oscillatorOp (⇑u) y * hermiteFunD α y =
        (2 / q) * (v y * hermiteFunD α y) + (d + 1) * (u y * hermiteFunD α y) := by
      intro y
      have := hF y
      field_simp at this ⊢
      linear_combination (-1 : ℝ) * hermiteFunD α y * this
    simp_rw [e]
    exact (Iv.const_mul _).add (Iu.const_mul _)
  have hsym := sym_oscillatorOp_hermite α u
  have hcoef : hermiteCoeff (fun y => χ (l⁻¹ • y)) α = q * (α.degree : ℝ) * hermiteCoeff (fun y => φ (l⁻¹ • y)) α := by
    unfold hermiteCoeff
    have e1 : (fun y => χ (l⁻¹ • y) * hermiteFunD α y) = fun y => v y * hermiteFunD α y := by
      funext y; rw [hv]
    have e2 : (fun y => φ (l⁻¹ • y) * hermiteFunD α y) = fun y => u y * hermiteFunD α y := by
      funext y; rw [hu]
    rw [e1, e2]
    have e3 : ∀ y, v y * hermiteFunD α y = (q / 2) * (oscillatorOp (⇑u) y * hermiteFunD α y) -
        (q / 2) * (d + 1) * (u y * hermiteFunD α y) := fun y => by rw [hF y]; ring
    simp_rw [e3]
    rw [integral_sub (IH.const_mul _) (Iu.const_mul _), integral_const_mul, integral_const_mul]
    have hsym' : ∫ y, oscillatorOp (⇑u) y * hermiteFunD α y = oscEigenvalue d α * ∫ y, u y * hermiteFunD α y := hsym
    rw [hsym']
    unfold oscEigenvalue
    ring
  rw [hcoef]
  ring

/-- **The generator of `e^{-tS_0}` on Schwartz functions, in `L²`**: `(e^{-hS_0} φ - φ)/h + S_0 φ → 0` in `L²`
as `h ↓ 0`. -/
theorem mov2d_S0_gen (hβ : 0 < β) (hq : 0 < q) (φ χ : 𝓢R) (hχ : (⇑χ : Euc d → ℝ) = mov_S0 d β q φ) :
    Tendsto (fun h : ℝ => oscNorm 0 (fun x => h⁻¹ * (mov_expS0 β q h (fun z => φ z) x - φ x) + χ x))
      (𝓝[>] 0) (𝓝 0) := by
  have hlp := mov_dil_pos hβ hq
  set l := mov_dil β q with hl
  have hφ2 := mov2d_schwartz_memLp φ
  have hχ2 := mov2d_schwartz_memLp χ
  obtain ⟨C1, hC1, hdil⟩ := mov2b_dil_both (d := d) 0 hlp
  set c : ℝ := Real.sqrt (l ^ d) * (l ^ d)⁻¹ with hc
  have hcpos : 0 < c := by positivity
  have hcoef : ∀ f : Euc d → ℝ, ∀ α, mov2b_dcoeff l f α = c * hermiteCoeff (fun y => f (l⁻¹ • y)) α :=
    fun f α => mov2b_dcoeff_eq hlp f α
  set cφ : MultiIndex d → ℝ := fun α => mov2b_dcoeff l (fun z => φ z) α with hcφ
  set k : MultiIndex d → ℝ := fun α => (α.degree : ℝ) with hk
  -- the function u_h
  set uh : ℝ → Euc d → ℝ := fun h x => h⁻¹ * (mov_expS0 β q h (fun z => φ z) x - φ x) + χ x with huh
  have hu2 : ∀ h : ℝ, MemLp (uh h) 2 (volume : Measure (Euc d)) := fun h => by
    have hA := mov_expS0_memLp hβ hq h (fun z => φ z)
    exact ((hA.sub hφ2).const_mul h⁻¹).add hχ2
  -- dilated coefficients of u_h
  have hdc : ∀ h : ℝ, 0 < h → ∀ α, mov2b_dcoeff l (uh h) α =
      (h⁻¹ * (Real.exp (-(h * q * k α)) - 1) + q * k α) * cφ α := by
    intro h hh α
    have hA := mov_expS0_memLp hβ hq h (fun z => φ z)
    have e1 : mov2b_dcoeff l (uh h) α = mov2b_dcoeff l (fun x => h⁻¹ * (mov_expS0 β q h (fun z => φ z) x - φ x)) α +
        mov2b_dcoeff l (fun z => χ z) α :=
      mov2d_dcoeff_add hβ hq ((hA.sub hφ2).const_mul h⁻¹) hχ2 α
    rw [e1, mov2d_dcoeff_smul hβ hq, mov2d_dcoeff_sub hβ hq hA hφ2,
      mov_expS0_dcoeff hβ hq hh.le hφ2 α, mov2d_dcoeff_S0 hβ hq φ χ hχ α]
    simp only [hcφ, hk]
    ring
  -- Parseval: bound the norm by the dilated coefficients
  set Sh : ℝ → ℝ := fun h => ∑' α, (mov2b_dcoeff l (uh h) α) ^ 2 with hSh
  have hnorm : ∀ h : ℝ, oscNorm 0 (uh h) ≤ C1 / c * Real.sqrt (Sh h) := by
    intro h
    set f : Euc d → ℝ := fun y => uh h (l⁻¹ • y) with hf
    have hfL : MemLp f 2 (volume : Measure (Euc d)) := mov2b_memLp_inv hlp (hu2 h)
    have hfO : MemOsc 0 f := ⟨hfL, by
      have := mov2b_coeff_sq_summable hfL
      simpa using this⟩
    obtain ⟨⟨_, h2⟩, _⟩ := hdil f hfO
    have e : (fun x => f (l • x)) = uh h := by
      funext x; simp only [hf, smul_smul, inv_mul_cancel₀ hlp.ne', one_smul]
    rw [e] at h2
    refine h2.trans ?_
    have e2 : oscNorm 0 f = 1 / c * Real.sqrt (Sh h) := by
      unfold oscNorm
      simp only [Real.rpow_zero, one_mul]
      have e3 : ∀ α, hermiteCoeff f α ^ 2 = (1 / c) ^ 2 * (mov2b_dcoeff l (uh h) α) ^ 2 := by
        intro α
        rw [hcoef (uh h) α, mul_pow, ← mul_assoc, ← mul_pow, one_div, inv_mul_cancel₀ hcpos.ne',
          one_pow, one_mul]
      simp_rw [e3]
      rw [tsum_mul_left, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [e2]
    have : C1 * (1 / c * Real.sqrt (Sh h)) = C1 / c * Real.sqrt (Sh h) := by ring
    rw [this]
  -- dominated convergence for `Sh`
  have hsumχ : Summable fun α : MultiIndex d => (mov2b_dcoeff l (fun z => χ z) α) ^ 2 := by
    have := mov2b_coeff_sq_summable (mov2b_memLp_inv hlp hχ2)
    refine (this.mul_left (c ^ 2)).congr fun α => ?_
    rw [hcoef (fun z => χ z) α]
    ring
  have hlim : Tendsto Sh (𝓝[>] 0) (𝓝 0) := by
    have hdom := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
      (f := fun (h : ℝ) (α : MultiIndex d) =>
        ((h⁻¹ * (Real.exp (-(h * q * k α)) - 1) + q * k α) * cφ α) ^ 2)
      (g := fun _ => (0 : ℝ)) (bound := fun α => 4 * (mov2b_dcoeff l (fun z => χ z) α) ^ 2)
      (hsumχ.mul_left 4)
      (fun α => by
        have hd0 : HasDerivAt (fun h : ℝ => Real.exp (-(h * q * k α))) (-(q * k α)) 0 := by
          have h0 : HasDerivAt (fun h : ℝ => h * q * k α) (q * k α) 0 := by
            simpa using ((hasDerivAt_id (0 : ℝ)).mul_const q).mul_const (k α)
          have h1 : HasDerivAt (fun h : ℝ => -(h * q * k α)) (-(q * k α)) 0 := h0.neg
          simpa using h1.exp
        have hs := hd0.tendsto_slope_zero_right
        have hs' : Tendsto (fun h : ℝ => h⁻¹ * (Real.exp (-(h * q * k α)) - 1) + q * k α) (𝓝[>] 0) (𝓝 0) := by
          have := hs.add_const (q * k α)
          simpa [smul_eq_mul] using this
        have := (hs'.mul_const (cφ α)).pow 2
        simpa using this)
      (by
        filter_upwards [self_mem_nhdsWithin] with h hh α
        have hh' : 0 < h := hh
        rw [Real.norm_of_nonneg (sq_nonneg _), mov2d_dcoeff_S0 hβ hq φ χ hχ α]
        have hk0 : 0 ≤ k α := Nat.cast_nonneg _
        have hx : 0 ≤ h * q * k α := by positivity
        have hE1 : Real.exp (-(h * q * k α)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
        have hE2 : 1 - h * q * k α ≤ Real.exp (-(h * q * k α)) := by
          have := Real.add_one_le_exp (-(h * q * k α)); linarith
        have hX1 : -(q * k α) ≤ h⁻¹ * (Real.exp (-(h * q * k α)) - 1) := by
          have := mul_le_mul_of_nonneg_left (show -(h * q * k α) ≤ Real.exp (-(h * q * k α)) - 1 by linarith)
            (inv_nonneg.2 hh'.le)
          have e : h⁻¹ * (-(h * q * k α)) = -(q * k α) := by field_simp
          linarith
        have hX2 : h⁻¹ * (Real.exp (-(h * q * k α)) - 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hh'.le) (by linarith)
        have hqk : 0 ≤ q * k α := by positivity
        have hXb : (h⁻¹ * (Real.exp (-(h * q * k α)) - 1) + q * k α) ^ 2 ≤ (2 * (q * k α)) ^ 2 := by
          apply pow_le_pow_left₀ <;> nlinarith
        calc ((h⁻¹ * (Real.exp (-(h * q * k α)) - 1) + q * k α) * cφ α) ^ 2
            = (h⁻¹ * (Real.exp (-(h * q * k α)) - 1) + q * k α) ^ 2 * (cφ α) ^ 2 := by ring
          _ ≤ (2 * (q * k α)) ^ 2 * (cφ α) ^ 2 := mul_le_mul_of_nonneg_right hXb (sq_nonneg _)
          _ = 4 * (q * (α.degree : ℝ) * cφ α) ^ 2 := by simp only [hk]; ring)
    have hdom' : Tendsto (fun h : ℝ => ∑' α : MultiIndex d,
        ((h⁻¹ * (Real.exp (-(h * q * k α)) - 1) + q * k α) * cφ α) ^ 2) (𝓝[>] 0) (𝓝 0) := by
      simpa using hdom
    refine hdom'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact tsum_congr fun α => by rw [hdc h hh α]
  -- conclude
  have hsq : Tendsto (fun h => C1 / c * Real.sqrt (Sh h)) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp hlim).const_mul (C1 / c)
    simpa using this
  refine squeeze_zero (fun h => by unfold oscNorm; exact Real.sqrt_nonneg _) hnorm hsq

end S0gen



/-! ## C. The extension lemma on a class of functions, and `R` on Schwartz functions -/

/-- Variant of `mov2d_op_apply_of_bdd` with a hereditary class `Pr` of admissible functions. -/
lemma mov2d_op_apply_of_class {ρ σ : ℝ} {A : (Euc d → ℝ) → Euc d → ℝ} {C : ℝ} (h : Mov2dData ρ σ A C)
    {Pr : (Euc d → ℝ) → Prop} (hPh : ∀ c : MultiIndex d →₀ ℝ, Pr (mov2d_hs d c))
    (hPs : ∀ f g, Pr f → Pr g → Pr (fun z => f z - g z)) (hPo : ∀ f, Pr f → MemOsc ρ f)
    {K : ℝ} (hb : ∀ f : Euc d → ℝ, Pr f → MemOsc σ (A f) ∧ oscNorm σ (A f) ≤ K * oscNorm ρ f)
    (hl : ∀ f g : Euc d → ℝ, Pr f → Pr g →
      ∀ α, hermiteCoeff (A (fun z => f z - g z)) α = hermiteCoeff (A f) α - hermiteCoeff (A g) α)
    {f : Euc d → ℝ} (hf : Pr f) :
    mov2d_op ρ σ A (OscSpace.ofFun ρ f) = OscSpace.ofFun σ (A f) := by
  have hfo := hPo f hf
  have hgc : ∀ n, mo_pSum f n =
      mov2d_hs d (∑ α ∈ mova2_S d n, Finsupp.single α (hermiteCoeff f α)) := fun n => by
    rw [mov2d_hs_sum]; rfl
  have hgP : ∀ n, Pr (mo_pSum f n) := fun n => by rw [hgc n]; exact hPh _
  have hgm : ∀ n, MemOsc ρ (mo_pSum f n) := fun n => mo_hsum_memOsc ρ _ _
  have h1 : Tendsto (fun n => OscSpace.ofFun ρ (mo_pSum f n)) atTop (𝓝 (OscSpace.ofFun ρ f)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have e : ∀ n, ‖OscSpace.ofFun ρ (mo_pSum f n) - OscSpace.ofFun ρ f‖ =
        oscNorm ρ (fun x => f x - mo_pSum f n x) := by
      intro n
      rw [norm_sub_rev, ← mov2d_ofFun_sub hfo (hgm n),
        OscSpace.norm_ofFun _ (mov2d_memOsc_sub hfo (hgm n))]
    simp_rw [e]
    exact mo_hsum_tail ρ hfo
  have h2 : Tendsto (fun n => mov2d_op ρ σ A (OscSpace.ofFun ρ (mo_pSum f n))) atTop
      (𝓝 (mov2d_op ρ σ A (OscSpace.ofFun ρ f))) := ((mov2d_op ρ σ A).continuous.tendsto _).comp h1
  have h3 : Tendsto (fun n => mov2d_op ρ σ A (OscSpace.ofFun ρ (mo_pSum f n))) atTop
      (𝓝 (OscSpace.ofFun σ (A f))) := by
    have e : ∀ n, mov2d_op ρ σ A (OscSpace.ofFun ρ (mo_pSum f n)) =
        OscSpace.ofFun σ (A (mo_pSum f n)) := fun n => by
      rw [hgc n]; exact mov2d_op_hs h _
    simp_rw [e]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hAg : ∀ n, MemOsc σ (A (mo_pSum f n)) := fun n => by rw [hgc n]; exact (h.1 _).1
    have hAf : MemOsc σ (A f) := (hb f hf).1
    have e2 : ∀ n, ‖OscSpace.ofFun σ (A (mo_pSum f n)) - OscSpace.ofFun σ (A f)‖ ≤
        K * oscNorm ρ (fun x => f x - mo_pSum f n x) := by
      intro n
      rw [norm_sub_rev, ← mov2d_ofFun_sub hAf (hAg n)]
      have hbn := hb _ (hPs f (mo_pSum f n) hf (hgP n))
      have : OscSpace.ofFun σ (fun z => A f z - A (mo_pSum f n) z) =
          OscSpace.ofFun σ (A (fun z => f z - mo_pSum f n z)) :=
        mov2d_ofFun_ext (mov2d_memOsc_sub hAf (hAg n)) hbn.1 (fun α => by
          rw [mova2_coeff_sub hAf.1 (hAg n).1, hl f (mo_pSum f n) hf (hgP n) α])
      rw [this, OscSpace.norm_ofFun _ hbn.1]
      exact hbn.2
    refine squeeze_zero (fun n => norm_nonneg _) e2 ?_
    simpa using (mo_hsum_tail ρ hfo).const_mul K
  exact tendsto_nhds_unique h2 h3

section ThermalR

variable {s : ℝ} {β q : ℝ} {ρ : Euc d → ℝ}

/-- The bound for `A_R` on arbitrary Schwartz functions. -/
lemma mov2d_AR_bdd (H : Mov2dTh d s β q ρ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : 𝓢R, MemOsc (r - movA d s) (mov2d_AR d s β q ρ φ) ∧
      oscNorm (r - movA d s) (mov2d_AR d s β q ρ φ) ≤ C * oscNorm r φ := by
  obtain ⟨K, hK0, hK⟩ := mov2d_V1_mult H r
  obtain ⟨CP, hCP0, hCP⟩ := mov_P_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ r
  have ha0 := (mov2d_a_bounds d H.hd H.hsd).1
  refine ⟨K + CP, by positivity, fun φ => ?_⟩
  have hf := memOsc_schwartz r φ
  obtain ⟨h1, h2⟩ := hK _ hf
  obtain ⟨h1', h2'⟩ := mo_mono (sub_le_self r ha0) h1
  have hP := hCP φ
  have hn : 0 ≤ oscNorm r (φ : Euc d → ℝ) := Real.sqrt_nonneg _
  obtain ⟨h5, h6⟩ := HRS.MS.MovC1.movc1_osc_add (r - movA d s) h1' hP.1
  refine ⟨h5, h6.trans ?_⟩
  nlinarith [h2, h2', hP.2]

/-- `A_R` is linear on Schwartz functions. -/
lemma mov2d_AR_sub (H : Mov2dTh d s β q ρ) (φ ψ : 𝓢R) :
    mov2d_AR d s β q ρ (fun z => φ z - ψ z) = fun z => mov2d_AR d s β q ρ φ z - mov2d_AR d s β q ρ ψ z := by
  have := mov2d_P_lin' H ⟨φ, rfl⟩ ⟨ψ, rfl⟩ 1 (-1)
  funext z
  have e1 : (fun z => φ z - ψ z) = fun z => 1 * φ z + (-1) * ψ z := by funext z; ring
  unfold mov2d_AR
  rw [e1, this]
  simp only [one_mul, neg_mul]
  ring

/-- `R_r (ofFun r φ) = ofFun (r - a) (A_R φ)` for Schwartz `φ` (not only finite Hermite sums). -/
lemma mov2d_R_ofFun_schwartz (H : Mov2dTh d s β q ρ) (r : ℝ) (φ : 𝓢R) :
    mov2d_R d s β q ρ r (OscSpace.ofFun r (fun z => φ z)) =
      OscSpace.ofFun (r - movA d s) (mov2d_AR d s β q ρ (fun z => φ z)) := by
  obtain ⟨C, -, hd⟩ := mov2d_AR_data H r
  obtain ⟨K, hK0, hK⟩ := mov2d_AR_bdd H r
  refine mov2d_op_apply_of_class hd (Pr := fun f => ∃ ψ : 𝓢R, (⇑ψ : Euc d → ℝ) = f)
    (fun c => mov2d_hs_schwartz c) (fun f g ⟨ψ1, h1⟩ ⟨ψ2, h2⟩ => ⟨ψ1 - ψ2, by funext z; simp [← h1, ← h2]⟩)
    (fun f ⟨ψ, h⟩ => by rw [← h]; exact memOsc_schwartz r ψ) (K := K)
    (fun f ⟨ψ, h⟩ => by rw [← h]; exact hK ψ) ?_ ⟨φ, rfl⟩
  rintro f g ⟨ψ1, h1⟩ ⟨ψ2, h2⟩ α
  subst h1; subst h2
  rw [mov2d_AR_sub H, mova2_coeff_sub (hK ψ1).1.1 (hK ψ2).1.1]

end ThermalR

/-! ## D. The averaging lemma and the generator of `G` at `0` on Schwartz functions -/

lemma mov2d_avg_lim {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (U : ℝ → E →L[ℝ] E) (M : ℝ) (hU : ∀ t, 0 ≤ t → ‖U t‖ ≤ M) (hU0 : U 0 = 1)
    (hUc : ∀ x, ContinuousOn (fun t => U t x) (Set.Ici 0)) (g : ℝ → E)
    (hg : ContinuousOn g (Set.Ici 0))
    (hgi : ∀ h : ℝ, 0 < h → IntervalIntegrable (fun u => U (h - u) (g u)) volume 0 h) :
    Tendsto (fun h : ℝ => h⁻¹ • ∫ u in (0 : ℝ)..h, U (h - u) (g u)) (𝓝[>] 0) (𝓝 (g 0)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set M' : ℝ := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set ε' : ℝ := ε / (2 * (M' + 1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousWithinAt_iff.1 (hg 0 (Set.mem_Ici.2 le_rfl)) ε' hε'pos
  obtain ⟨δ2, hδ2, h2⟩ := Metric.continuousWithinAt_iff.1 (hUc (g 0) 0 (Set.mem_Ici.2 le_rfl)) ε' hε'pos
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun h hh hhd => ?_⟩
  have hh0 : 0 < h := hh
  have hhd' : h < min δ1 δ2 := by simpa [Real.dist_eq, abs_of_pos hh0] using hhd
  have hint := hgi h hh0
  have hc : (∫ u in (0 : ℝ)..h, U (h - u) (g u)) - h • g 0 = ∫ u in (0 : ℝ)..h, (U (h - u) (g u) - g 0) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const]
    simp
  have hbound : ∀ u ∈ Set.uIoc (0 : ℝ) h, ‖U (h - u) (g u) - g 0‖ ≤ (M' + 1) * ε' := by
    intro u hu
    rw [Set.uIoc_of_le hh0.le] at hu
    have hu0 : 0 ≤ u := hu.1.le
    have hgu : ‖g u - g 0‖ < ε' := by
      have := h1 (Set.mem_Ici.2 hu0) (by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hu0]
        exact lt_of_le_of_lt hu.2 (lt_of_lt_of_le hhd' (min_le_left _ _)))
      simpa [dist_eq_norm] using this
    have hUg : ‖U (h - u) (g 0) - g 0‖ < ε' := by
      have hhu : 0 ≤ h - u := by linarith [hu.2]
      have := h2 (Set.mem_Ici.2 hhu) (by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hhu]
        have : h - u < h := by linarith [hu.1]
        exact lt_of_lt_of_le (this.trans hhd') (min_le_right _ _))
      have h0 : U 0 (g 0) = g 0 := by rw [hU0]; rfl
      simpa [dist_eq_norm, h0] using this
    have hhu : 0 ≤ h - u := by linarith [hu.2]
    calc ‖U (h - u) (g u) - g 0‖ = ‖U (h - u) (g u - g 0) + (U (h - u) (g 0) - g 0)‖ := by
          rw [map_sub]; congr 1; abel
      _ ≤ ‖U (h - u) (g u - g 0)‖ + ‖U (h - u) (g 0) - g 0‖ := norm_add_le _ _
      _ ≤ M' * ‖g u - g 0‖ + ε' := by
          gcongr
          exact ((U (h - u)).le_opNorm _).trans (mul_le_mul_of_nonneg_right
            ((hU _ hhu).trans (le_max_left _ _)) (norm_nonneg _))
      _ ≤ M' * ε' + ε' := by gcongr
      _ = (M' + 1) * ε' := by ring
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [dist_eq_norm]
  have e : h⁻¹ • (∫ u in (0 : ℝ)..h, U (h - u) (g u)) - g 0 =
      h⁻¹ • ((∫ u in (0 : ℝ)..h, U (h - u) (g u)) - h • g 0) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hh0.ne', one_smul]
  rw [e, norm_smul, hc, norm_inv, Real.norm_of_nonneg hh0.le]
  calc h⁻¹ * ‖∫ u in (0 : ℝ)..h, (U (h - u) (g u) - g 0)‖ ≤ h⁻¹ * ((M' + 1) * ε' * |h - 0|) :=
        mul_le_mul_of_nonneg_left hn (inv_nonneg.2 hh0.le)
    _ = (M' + 1) * ε' := by rw [sub_zero, abs_of_pos hh0]; field_simp
    _ < ε := by
        rw [hε']
        have : (M' + 1) * (ε / (2 * (M' + 1))) = ε / 2 := by field_simp
        rw [this]; linarith

lemma mov2d_strong_comp_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : ℝ → E →L[ℝ] E) {M : ℝ} {S : Set ℝ} {τ g : ℝ → _} (hM : ∀ u ∈ S, ‖U (τ u)‖ ≤ M)
    (hUc : ∀ x, ContinuousOn (fun t => U t x) (Set.Ici 0))
    (hτ : ContinuousOn τ S) (hτS : ∀ u ∈ S, 0 ≤ τ u) (hg : ContinuousOn g S) :
    ContinuousOn (fun u => U (τ u) (g u)) S := by
  intro u0 hu0
  have h2 : ContinuousWithinAt (fun u => U (τ u) (g u0)) S u0 :=
    ((hUc (g u0)).comp hτ (fun u hu => Set.mem_Ici.2 (hτS u hu))) u0 hu0
  have h1 : Tendsto (fun u => U (τ u) (g u - g u0)) (𝓝[S] u0) (𝓝 0) := by
    have hgc : Tendsto (fun u => ‖g u - g u0‖) (𝓝[S] u0) (𝓝 0) := by
      have := ((hg u0 hu0).sub_const (g u0)).norm
      simpa using this
    have hB : Tendsto (fun u => (|M|) * ‖g u - g u0‖) (𝓝[S] u0) (𝓝 0) := by
      simpa using hgc.const_mul |M|
    refine squeeze_zero_norm' ?_ hB
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact ((U (τ u)).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      ((hM u hu).trans (le_abs_self M)) (norm_nonneg _))
  have : (fun u => U (τ u) (g u)) = fun u => U (τ u) (g u - g u0) + U (τ u) (g u0) := by
    funext u; rw [← map_add]; congr 1; abel
  rw [ContinuousWithinAt, this]
  simpa using h1.add h2

section GGen

variable {s : ℝ} {β q : ℝ} {ρ : Euc d → ℝ}

lemma mov2d_movS_eq (H : Mov2dTh d s β q ρ) (φ χ : 𝓢R) (hχ : (⇑χ : Euc d → ℝ) = mov_S0 d β q φ) :
    movS d s β ρ (fun z => φ z) = fun x => χ x + mov2d_AR d s β q ρ (fun z => φ z) x := by
  funext x
  have := mov_S_eq_S0 H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ φ x
  rw [this, show χ x = mov_S0 d β q φ x from congrFun hχ x]
  unfold mov2d_AR
  ring

/-- **The generator of the global flow at `0`** on a Schwartz function `φ`:
`(G(h) φ - φ)/h → -S φ` in `L² = Σ^0` as `h ↓ 0`. -/
theorem mov2d_G_gen (H : Mov2dTh d s β q ρ) (φ χ : 𝓢R) (hχ : (⇑χ : Euc d → ℝ) = mov_S0 d β q φ) :
    Tendsto (fun h : ℝ => h⁻¹ • (mov2d_G H 0 h (OscSpace.ofFun 0 (fun z => φ z)) -
        OscSpace.ofFun 0 (fun z => φ z))) (𝓝[>] 0)
      (𝓝 (-(OscSpace.ofFun 0 (movS d s β ρ (fun z => φ z))))) := by
  obtain ⟨ha0, ha2⟩ := mov2d_a_bounds d H.hd H.hsd
  set a := movA d s with hadef
  have h20 : (0 : ℝ) ≤ 2 := by norm_num
  have hab : (0 : ℝ) ≤ 2 - a := by linarith
  have hφ0 : MemOsc 0 (fun z => φ z) := memOsc_schwartz 0 φ
  have hφ2 : MemOsc 2 (fun z => φ z) := memOsc_schwartz 2 φ
  set e0 : OscSpace d 0 := OscSpace.ofFun 0 (fun z => φ z) with he0
  set e2 : OscSpace d 2 := OscSpace.ofFun 2 (fun z => φ z) with he2
  have hje : mov2d_j h20 e2 = e0 := mov2d_j_ofFun h20 hφ2
  obtain ⟨CR, hCR0, hCR⟩ := mov2d_AR_bdd H 2
  have hAR2 : MemOsc (2 - a) (mov2d_AR d s β q ρ (fun z => φ z)) := (hCR φ).1
  have hAR0 : MemOsc 0 (mov2d_AR d s β q ρ (fun z => φ z)) := (mo_mono hab hAR2).1
  set g : ℝ → OscSpace d 0 := fun u => mov2d_j hab (mov2d_R d s β q ρ 2 (mov2d_G H 2 u e2)) with hg
  have hg0 : g 0 = OscSpace.ofFun 0 (mov2d_AR d s β q ρ (fun z => φ z)) := by
    simp only [hg, mov2d_G_zero, he2]
    rw [mov2d_R_ofFun_schwartz H 2 φ, mov2d_j_ofFun hab hAR2]
  -- continuity of `g`
  have hgc : ContinuousOn g (Set.Ici 0) :=
    (mov2d_j hab).continuous.comp_continuousOn
      ((mov2d_R d s β q ρ 2).continuous.comp_continuousOn (mov2d_G_cont H 2 e2))
  set Sm0 : ℝ → OscSpace d 0 →L[ℝ] OscSpace d 0 := fun t => mov2d_Sm β q (le_refl 0) t with hSm0
  obtain ⟨M0, hM00, hM0⟩ := mov2d_Sm_refl_norm_le (d := d) H.hβ H.hq 0
  -- Duhamel at level 0 for `e0`
  have hD : ∀ h : ℝ, 0 < h → mov2d_G H 0 h e0 = Sm0 h e0 - ∫ u in (0 : ℝ)..h, Sm0 (h - u) (g u) := by
    intro h hh
    have hGc := mov2d_G_compat H h20 hh.le e2
    rw [hje] at hGc
    rw [← hGc, mov2d_G_duhamel H 2 hh.le e2, map_sub]
    have hSm := mov2d_Sm_compS (d := d) H.hβ H.hq (le_refl (2 : ℝ)) (le_refl (0 : ℝ)) h20 h20 hh e2
    rw [hje] at hSm
    rw [hSm]
    congr 1
    have hyp := mov2d_hyp' H hh
    have hint : IntervalIntegrable (fun u => mov2d_Sm β q (sub_le_self (2 : ℝ) ha0) (h - u)
        (mov2d_R d s β q ρ 2 (mov2d_G H 2 u e2))) volume 0 h :=
      mov2c_integrable hyp ha0 ha2 2 (y := fun u => mov2d_G H 2 u e2)
        ((mov2d_G_cont H 2 e2).mono (fun u hu => hu.1)) ⟨hh.le, le_rfl⟩
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    refine intervalIntegral.integral_congr_ae ?_
    have hae : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ ({h} : Set ℝ) :=
      (Set.finite_singleton h).countable.ae_notMem _
    refine hae.mono (fun u hu huI => ?_)
    rw [Set.uIoc_of_le hh.le] at huI
    have huh : u < h := lt_of_le_of_ne huI.2 hu
    exact mov2d_Sm_compS (d := d) H.hβ H.hq (sub_le_self (2 : ℝ) ha0) (le_refl (0 : ℝ)) hab h20
      (by linarith) _
  have hgi : ∀ h : ℝ, 0 < h → IntervalIntegrable (fun u => Sm0 (h - u) (g u)) volume 0 h := by
    intro h hh
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hh.le]
    exact mov2d_strong_comp_cont Sm0 (M := M0) (fun u hu => hM0 _ (by show 0 ≤ h - u; linarith [hu.2])) (fun x => mov2d_Sm_cont H.hβ H.hq 0 x)
      (continuousOn_const.sub continuousOn_id) (fun u hu => by show 0 ≤ h - u; linarith [hu.2])
      (hgc.mono (fun u hu => hu.1))
  have hAvg := mov2d_avg_lim Sm0 M0 (fun t ht => hM0 t ht) (mov2d_Sm_zero H.hβ H.hq 0)
    (fun x => mov2d_Sm_cont H.hβ H.hq 0 x) g hgc hgi
  -- the first bracket
  have hMO0 : ∀ h : ℝ, 0 < h → MemOsc 0 (mov_expS0 β q h (fun z => φ z)) := fun h hh => by
    obtain ⟨C, -, hC⟩ := mov_expS0_bounded (d := d) H.hβ H.hq 0
    exact (hC h hh.le _ hφ0).1
  have hχ0 : MemOsc 0 (fun z => χ z) := memOsc_schwartz 0 χ
  have hbr1 : ∀ h : ℝ, 0 < h → h⁻¹ • (Sm0 h e0 - e0) + OscSpace.ofFun 0 (fun z => χ z) =
      OscSpace.ofFun 0 (fun x => h⁻¹ * (mov_expS0 β q h (fun z => φ z) x - φ x) + χ x) := by
    intro h hh
    have hS := mov2d_Sm_ofFun (d := d) H.hβ H.hq (le_refl (0 : ℝ)) (t := h) (Or.inr rfl) hφ0
    rw [max_eq_left hh.le] at hS
    have hsub := mov2d_ofFun_sub (hMO0 h hh) hφ0
    have hsm := mov2d_ofFun_smul h⁻¹ (mov2d_memOsc_sub (hMO0 h hh) hφ0)
    have hsm' := (HRS.MS.MovC1.movc1_osc_smul 0 h⁻¹ (mov2d_memOsc_sub (hMO0 h hh) hφ0)).1
    rw [mov2d_ofFun_add hsm' hχ0, hsm, hsub]
    show h⁻¹ • (Sm0 h e0 - e0) + _ = _
    simp only [hSm0]
    rw [hS]
  have hT1 : Tendsto (fun h : ℝ => h⁻¹ • (Sm0 h e0 - e0) + OscSpace.ofFun 0 (fun z => χ z)) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (mov2d_S0_gen H.hβ H.hq φ χ hχ).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [hbr1 h hh]
    have hmem : MemOsc 0 (fun x => h⁻¹ * (mov_expS0 β q h (fun z => φ z) x - φ x) + χ x) :=
      (HRS.MS.MovC1.movc1_osc_add 0 (HRS.MS.MovC1.movc1_osc_smul 0 h⁻¹ (mov2d_memOsc_sub (hMO0 h hh) hφ0)).1 hχ0).1
    rw [OscSpace.norm_ofFun _ hmem]
  have hT2 : Tendsto (fun h : ℝ => h⁻¹ • (∫ u in (0 : ℝ)..h, Sm0 (h - u) (g u)) - g 0) (𝓝[>] 0) (𝓝 0) := by
    have := hAvg.sub_const (g 0)
    simpa using this
  -- assemble
  have hmovS : OscSpace.ofFun 0 (movS d s β ρ (fun z => φ z)) =
      OscSpace.ofFun 0 (fun z => χ z) + g 0 := by
    rw [mov2d_movS_eq H φ χ hχ, mov2d_ofFun_add hχ0 hAR0, hg0]
  have hF : ∀ h : ℝ, 0 < h → h⁻¹ • (mov2d_G H 0 h e0 - e0) + OscSpace.ofFun 0 (movS d s β ρ (fun z => φ z)) =
      (h⁻¹ • (Sm0 h e0 - e0) + OscSpace.ofFun 0 (fun z => χ z)) -
        (h⁻¹ • (∫ u in (0 : ℝ)..h, Sm0 (h - u) (g u)) - g 0) := by
    intro h hh
    rw [hD h hh, hmovS]
    simp only [smul_sub]
    abel
  have hlim : Tendsto (fun h : ℝ => h⁻¹ • (mov2d_G H 0 h e0 - e0) + OscSpace.ofFun 0 (movS d s β ρ (fun z => φ z)))
      (𝓝[>] 0) (𝓝 0) := by
    have := hT1.sub hT2
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (hF h hh).symm
  have hlim' : Tendsto (fun h : ℝ => h⁻¹ • (mov2d_G H 0 h e0 - e0) -
      (-(OscSpace.ofFun 0 (movS d s β ρ (fun z => φ z))))) (𝓝[>] 0) (𝓝 0) := by
    simpa [sub_neg_eq_add] using hlim
  exact tendsto_sub_nhds_zero_iff.1 hlim'

end GGen

/-! ## E. Schwartz seminorms are controlled by `oscNorm` -/

section Seminorms

/-- The word operator `f ↦ ∂_{J_0} ∂_{J_1} ⋯ f` on Schwartz functions. -/
def mov2d_Dw : List (Fin d) → 𝓢R →L[ℝ] 𝓢R
  | [] => ContinuousLinearMap.id ℝ _
  | j :: J => (mova1_D j).comp (mov2d_Dw J)

/-- The word operator `f ↦ x_{J_0} x_{J_1} ⋯ f`. -/
def mov2d_Xw : List (Fin d) → 𝓢R →L[ℝ] 𝓢R
  | [] => ContinuousLinearMap.id ℝ _
  | j :: J => (mova1_X j).comp (mov2d_Xw J)

lemma mov2d_Xw_apply (J : List (Fin d)) (f : 𝓢R) (x : Euc d) :
    mov2d_Xw J f x = (J.map (fun j => x j)).prod * f x := by
  induction J with
  | nil => simp [mov2d_Xw]
  | cons j J ih => simp [mov2d_Xw, mova1_X_apply, ih]; ring

lemma mov2d_Dw_osc (r : ℝ) (J : List (Fin d)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢R,
    oscNorm r (mov2d_Dw J f) ≤ C * oscNorm (r + J.length) f := by
  induction J generalizing r with
  | nil => exact ⟨1, zero_le_one, fun f => by simp [mov2d_Dw]⟩
  | cons j J ih =>
    obtain ⟨C1, hC1, h1⟩ := mo_partial (d := d) r
    obtain ⟨C2, hC2, h2⟩ := ih (r + 1)
    refine ⟨C1 * C2, mul_nonneg hC1 hC2, fun f => ?_⟩
    have h3 := (h1 j (mov2d_Dw J f)).2
    have h4 := h2 f
    have e : (⇑((mova1_D j) (mov2d_Dw J f)) : Euc d → ℝ) =
        fun x => fderiv ℝ (mov2d_Dw J f) x (EuclideanSpace.single j (1 : ℝ)) :=
      funext fun x => mova1_D_apply j _ x
    simp only [mov2d_Dw, ContinuousLinearMap.comp_apply]
    rw [e]
    refine h3.trans ?_
    have : r + 1 + (J.length : ℝ) = r + ((j :: J).length : ℝ) := by simp; ring
    rw [this] at h4
    calc C1 * oscNorm (r + 1) (mov2d_Dw J f) ≤ C1 * (C2 * oscNorm (r + ((j :: J).length : ℝ)) f) :=
          mul_le_mul_of_nonneg_left h4 hC1
      _ = _ := by ring

lemma mov2d_Xw_osc (r : ℝ) (J : List (Fin d)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢R,
    oscNorm r (mov2d_Xw J f) ≤ C * oscNorm (r + J.length) f := by
  induction J generalizing r with
  | nil => exact ⟨1, zero_le_one, fun f => by simp [mov2d_Xw]⟩
  | cons j J ih =>
    obtain ⟨C1, hC1, h1⟩ := mo_xmul (d := d) r
    obtain ⟨C2, hC2, h2⟩ := ih (r + 1)
    refine ⟨C1 * C2, mul_nonneg hC1 hC2, fun f => ?_⟩
    have h3 := (h1 j (mov2d_Xw J f)).2
    have h4 := h2 f
    have e : (⇑((mova1_X j) (mov2d_Xw J f)) : Euc d → ℝ) = fun x => x j * mov2d_Xw J f x :=
      funext fun x => mova1_X_apply j _ x
    simp only [mov2d_Xw, ContinuousLinearMap.comp_apply]
    rw [e]
    refine h3.trans ?_
    have : r + 1 + (J.length : ℝ) = r + ((j :: J).length : ℝ) := by simp; ring
    rw [this] at h4
    calc C1 * oscNorm (r + 1) (mov2d_Xw J f) ≤ C1 * (C2 * oscNorm (r + ((j :: J).length : ℝ)) f) :=
          mul_le_mul_of_nonneg_left h4 hC1
      _ = _ := by ring

/-- Sup norm of a Schwartz function by `oscNorm`. -/
lemma mov2d_sup_osc : ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : 𝓢R) (x : Euc d), |g x| ≤ C * oscNorm ((⌊(d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) g := by
  obtain ⟨C, hC, h⟩ := mo_sobolev_emb (d := d) 0 (⌊(d : ℝ) / 2⌋₊ + 1) (by
    have := Nat.lt_floor_add_one ((d : ℝ) / 2)
    simpa using this)
  refine ⟨C, hC, fun g x => ?_⟩
  have := h g x
  simpa using this

lemma mov2d_iter_word (n : ℕ) (f : 𝓢R) (J : Fin n → Fin d) :
    (fun y => iteratedFDeriv ℝ n f y (fun i => EuclideanSpace.single (J i) (1 : ℝ))) =
      ⇑(mov2d_Dw (List.ofFn J) f) := by
  induction n generalizing f with
  | zero => funext y; simp [mov2d_Dw, iteratedFDeriv_zero_apply]
  | succ n ih =>
    funext y
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) y :=
      (f.smooth ⊤).differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n) y
    rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' hdiff, List.ofFn_succ]
    simp only [mov2d_Dw, ContinuousLinearMap.comp_apply, mova1_D_apply]
    have := ih f (fun i => J i.succ)
    have e : (fun z => iteratedFDeriv ℝ n f z (Fin.tail fun i => EuclideanSpace.single (J i) (1 : ℝ))) =
        fun y => iteratedFDeriv ℝ n f y (fun i => EuclideanSpace.single (J i.succ) (1 : ℝ)) := rfl
    rw [e, this]

/-- The norm of a multilinear form on `ℝ^d` is bounded by the sum of its values on coordinate vectors. -/
lemma mov2d_multilinear_norm (n : ℕ) (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euc d) ℝ) :
    ‖M‖ ≤ ∑ J : Fin n → Fin d, |M (fun i => EuclideanSpace.single (J i) (1 : ℝ))| := by
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun m => ?_
  have hm : ∀ i, m i = ∑ j : Fin d, m i j • (EuclideanSpace.single j (1 : ℝ) : Euc d) := by
    intro i
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (m i)
    simpa [EuclideanSpace.basisFun_apply] using this.symm
  have hM : M m = ∑ J : Fin n → Fin d, (∏ i, m i (J i)) * M (fun i => EuclideanSpace.single (J i) (1 : ℝ)) := by
    have := M.toMultilinearMap.map_sum (fun i (j : Fin d) => m i j • (EuclideanSpace.single j (1 : ℝ) : Euc d))
    have e : (fun i => ∑ j : Fin d, m i j • (EuclideanSpace.single j (1 : ℝ) : Euc d)) = m := funext fun i => (hm i).symm
    rw [e] at this
    simp only [ContinuousMultilinearMap.coe_coe] at this
    rw [this]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [M.map_smul_univ]
    simp [smul_eq_mul]
  rw [hM, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun J _ => ?_)
  rw [norm_mul, Real.norm_eq_abs]
  have hp : |∏ i, m i (J i)| ≤ ∏ i, ‖m i‖ := by
    rw [Finset.abs_prod]
    gcongr with i _
    simpa using PiLp.norm_apply_le (m i) (J i)
  calc |∏ i, m i (J i)| * ‖M (fun i => EuclideanSpace.single (J i) (1 : ℝ))‖
      ≤ (∏ i, ‖m i‖) * |M (fun i => EuclideanSpace.single (J i) (1 : ℝ))| := by
        rw [Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)
    _ = _ := by ring

lemma mov2d_norm_le_sum (x : Euc d) (k : ℕ) : ‖x‖ ^ k ≤
    ∑ J' : Fin k → Fin d, ∏ i, |x (J' i)| := by
  have h1 : ‖x‖ ≤ ∑ j, |x j| := by
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
    simp only [Real.norm_eq_abs]
    rw [sq, Finset.sum_mul_sum]
    calc ∑ j, |x j| ^ 2 ≤ ∑ j, ∑ k, |x j| * |x k| := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [sq]
          exact Finset.single_le_sum (f := fun k => |x j| * |x k|) (fun _ _ => by positivity) (Finset.mem_univ j)
      _ = _ := rfl
  calc ‖x‖ ^ k ≤ (∑ j, |x j|) ^ k := pow_le_pow_left₀ (norm_nonneg _) h1 k
    _ = ∏ _i : Fin k, ∑ j, |x j| := by simp
    _ = _ := by
      rw [Finset.prod_univ_sum]
      simp [Fintype.piFinset_univ]

/-- **`Claim S`**: weighted derivative bounds for Schwartz functions by `oscNorm`. -/
lemma mov2d_seminorm_osc (k n : ℕ) : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (f : 𝓢R) (x : Euc d),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C * oscNorm (N : ℝ) f := by
  obtain ⟨CE, hCE0, hCE⟩ := mov2d_sup_osc (d := d)
  set n0 : ℕ := ⌊(d : ℝ) / 2⌋₊ + 1 with hn0
  -- constants for the words
  have hX : ∀ J' : Fin k → Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : 𝓢R,
      oscNorm (n0 : ℝ) (mov2d_Xw (List.ofFn J') g) ≤ C * oscNorm ((n0 : ℝ) + k) g := by
    intro J'
    obtain ⟨C, hC, h⟩ := mov2d_Xw_osc (d := d) (n0 : ℝ) (List.ofFn J')
    exact ⟨C, hC, fun g => by simpa using h g⟩
  have hD : ∀ J : Fin n → Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢R,
      oscNorm ((n0 : ℝ) + k) (mov2d_Dw (List.ofFn J) f) ≤ C * oscNorm ((n0 : ℝ) + k + n) f := by
    intro J
    obtain ⟨C, hC, h⟩ := mov2d_Dw_osc (d := d) ((n0 : ℝ) + k) (List.ofFn J)
    exact ⟨C, hC, fun f => by simpa using h f⟩
  choose CX hCX0 hCX using hX
  choose CD hCD0 hCD using hD
  refine ⟨CE * (∑ J' : Fin k → Fin d, CX J') * (∑ J : Fin n → Fin d, CD J), n0 + k + n,
    mul_nonneg (mul_nonneg hCE0 (Finset.sum_nonneg fun J' _ => hCX0 J'))
      (Finset.sum_nonneg fun J _ => hCD0 J), fun f x => ?_⟩
  have hsum := mov2d_multilinear_norm n (iteratedFDeriv ℝ n f x)
  have hword : ∀ (J' : Fin k → Fin d) (J : Fin n → Fin d),
      (∏ i, |x (J' i)|) * |iteratedFDeriv ℝ n f x (fun i => EuclideanSpace.single (J i) (1 : ℝ))| ≤
        CE * (CX J' * CD J) * oscNorm ((n0 + k + n : ℕ) : ℝ) f := by
    intro J' J
    have e1 := congrFun (mov2d_iter_word n f J) x
    rw [e1]
    set g : 𝓢R := mov2d_Dw (List.ofFn J) f
    have e2 : (∏ i, |x (J' i)|) * |g x| = |mov2d_Xw (List.ofFn J') g x| := by
      rw [mov2d_Xw_apply, abs_mul, List.map_ofFn, List.prod_ofFn, Finset.abs_prod]
      rfl
    rw [e2]
    have h1 := hCE (mov2d_Xw (List.ofFn J') g) x
    have h2 := hCX J' g
    have h3 := hCD J f
    have hN : ((n0 + k + n : ℕ) : ℝ) = (n0 : ℝ) + k + n := by push_cast; ring
    rw [hN]
    calc |mov2d_Xw (List.ofFn J') g x| ≤ CE * oscNorm (n0 : ℝ) (mov2d_Xw (List.ofFn J') g) := h1
      _ ≤ CE * (CX J' * oscNorm ((n0 : ℝ) + k) g) := mul_le_mul_of_nonneg_left h2 hCE0
      _ ≤ CE * (CX J' * (CD J * oscNorm ((n0 : ℝ) + k + n) f)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (hCX0 J')) hCE0
      _ = _ := by ring
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖
      ≤ (∑ J' : Fin k → Fin d, ∏ i, |x (J' i)|) *
        ∑ J : Fin n → Fin d, |iteratedFDeriv ℝ n f x (fun i => EuclideanSpace.single (J i) (1 : ℝ))| :=
        mul_le_mul (mov2d_norm_le_sum x k) hsum (norm_nonneg _)
          (Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _)
    _ = ∑ J' : Fin k → Fin d, ∑ J : Fin n → Fin d, (∏ i, |x (J' i)|) *
        |iteratedFDeriv ℝ n f x (fun i => EuclideanSpace.single (J i) (1 : ℝ))| := by
        rw [Finset.sum_mul_sum]
    _ ≤ ∑ J' : Fin k → Fin d, ∑ J : Fin n → Fin d,
        CE * (CX J' * CD J) * oscNorm ((n0 + k + n : ℕ) : ℝ) f :=
        Finset.sum_le_sum fun J' _ => Finset.sum_le_sum fun J _ => hword J' J
    _ = _ := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        ring

/-! ### Rapidly decaying Hermite series are Schwartz -/

lemma mov2d_summable_abs (hd1 : 1 ≤ d) (c : MultiIndex d → ℝ)
    (hc : ∀ N : ℕ, Summable fun α : MultiIndex d => oscEigenvalue d α ^ (N : ℝ) * c α ^ 2) (M : ℕ) :
    Summable fun α : MultiIndex d => |c α| * oscEigenvalue d α ^ ((M : ℝ) / 2) := by
  have hp : Summable fun α : MultiIndex d => oscEigenvalue d α ^ (-((d : ℝ) + 1)) :=
    (summable_oscEigenvalue_rpow_iff hd1 _).2 (by linarith)
  have hq := hc (M + d + 1)
  refine Summable.of_nonneg_of_le (fun α => by have := oscEv_pos (d := d) α; positivity)
    (fun α => ?_) ((hp.add hq).mul_left (1 / 2))
  have hL := oscEv_pos (d := d) α
  set L := oscEigenvalue d α with hLdef
  set a := L ^ (-((d : ℝ) + 1) / 2) with ha
  set b := |c α| * L ^ (((M + d + 1 : ℕ) : ℝ) / 2) with hb
  have hab : a * b = |c α| * L ^ ((M : ℝ) / 2) := by
    rw [ha, hb, mul_left_comm, ← Real.rpow_add hL]
    congr 2
    push_cast; ring
  have ha2 : a ^ 2 = L ^ (-((d : ℝ) + 1)) := rpow_half_sq _ _ hL
  have hb2 : b ^ 2 = L ^ (((M + d + 1 : ℕ) : ℝ)) * c α ^ 2 := by
    rw [hb, mul_pow, sq_abs, rpow_half_sq _ _ hL]; ring
  rw [← hab]
  nlinarith [sq_nonneg (a - b)]

lemma mov2d_osc_hermite (α : MultiIndex d) (N : ℕ) (φ : 𝓢R) (hφ : (⇑φ : Euc d → ℝ) = hermiteFunD α) :
    oscNorm (N : ℝ) (⇑φ) = oscEigenvalue d α ^ ((N : ℝ) / 2) := by
  have h1 : (⇑φ : Euc d → ℝ) = mo_hsum {α} (fun _ => (1 : ℝ)) := by
    funext z; simp [mo_hsum, hφ]
  have h2 := mo_hsum_oscNorm_sq (N : ℝ) {α} (fun _ => (1 : ℝ))
  rw [← h1] at h2
  simp only [Finset.sum_singleton, one_pow, mul_one] at h2
  have h3 : 0 ≤ oscNorm (N : ℝ) (⇑φ) := Real.sqrt_nonneg _
  have h4 : 0 ≤ oscEigenvalue d α ^ ((N : ℝ) / 2) := Real.rpow_nonneg (oscEv_pos α).le _
  have h5 : (oscEigenvalue d α ^ ((N : ℝ) / 2)) ^ 2 = oscEigenvalue d α ^ (N : ℝ) :=
    rpow_half_sq _ _ (oscEv_pos α)
  nlinarith [sq_nonneg (oscNorm (N : ℝ) (⇑φ) - oscEigenvalue d α ^ ((N : ℝ) / 2)),
    sq_nonneg (oscNorm (N : ℝ) (⇑φ) + oscEigenvalue d α ^ ((N : ℝ) / 2))]

lemma mov2d_series_schwartz (hd1 : 1 ≤ d) (c : MultiIndex d → ℝ)
    (hc : ∀ N : ℕ, Summable fun α : MultiIndex d => oscEigenvalue d α ^ (N : ℝ) * c α ^ 2) :
    ∃ ψ : 𝓢R, ∀ β, hermiteCoeff (⇑ψ : Euc d → ℝ) β = c β := by
  choose Φ hΦ using fun α : MultiIndex d => mova3c_hermite_schwartz (d := d) _ α rfl
  have hS := fun k n : ℕ => mov2d_seminorm_osc (d := d) k n
  choose C N hC0 hCS using hS
  -- the terms
  set f : MultiIndex d → Euc d → ℝ := fun α x => c α * hermiteFunD α x with hf
  have hfS : ∀ α, (⇑(c α • Φ α) : Euc d → ℝ) = f α := fun α => by
    funext x; simp [hf, hΦ α]
  have hfd : ∀ α, ContDiff ℝ ∞ (f α) := fun α => by rw [← hfS α]; exact (c α • Φ α).smooth ⊤
  -- bounds
  have hbd : ∀ k n : ℕ, ∀ α x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (f α) x‖ ≤
      C k n * (|c α| * oscEigenvalue d α ^ ((N k n : ℝ) / 2)) := by
    intro k n α x
    have h1 := hCS k n (c α • Φ α) x
    rw [hfS α] at h1
    have h2 : oscNorm (N k n : ℝ) (f α) = |c α| * oscEigenvalue d α ^ ((N k n : ℝ) / 2) := by
      have : f α = fun x => c α * (Φ α) x := by funext x; simp [hf, hΦ α]
      rw [this, oscNorm_const_mul, mov2d_osc_hermite α (N k n) (Φ α) (hΦ α)]
    rw [h2] at h1
    exact h1
  have hsum : ∀ k n : ℕ, Summable fun α : MultiIndex d =>
      C k n * (|c α| * oscEigenvalue d α ^ ((N k n : ℝ) / 2)) :=
    fun k n => (mov2d_summable_abs hd1 c hc (N k n)).mul_left _
  have hv : ∀ n : ℕ, (n : ℕ∞) ≤ (⊤ : ℕ∞) → Summable (fun α => C 0 n * (|c α| * oscEigenvalue d α ^ ((N 0 n : ℝ) / 2))) :=
    fun n _ => hsum 0 n
  have hb0 : ∀ (n : ℕ) (α : MultiIndex d) (x : Euc d), (n : ℕ∞) ≤ (⊤ : ℕ∞) →
      ‖iteratedFDeriv ℝ n (f α) x‖ ≤ C 0 n * (|c α| * oscEigenvalue d α ^ ((N 0 n : ℝ) / 2)) := by
    intro n α x _
    simpa using hbd 0 n α x
  have hsm : ContDiff ℝ ∞ (fun x => ∑' α, f α x) :=
    contDiff_tsum (N := (⊤ : ℕ∞)) hfd (fun n hn => hv n hn) (fun n α x hn => hb0 n α x (by exact_mod_cast hn))
  refine ⟨⟨fun x => ∑' α, f α x, hsm, fun k n => ?_⟩, ?_⟩
  · refine ⟨∑' α, C k n * (|c α| * oscEigenvalue d α ^ ((N k n : ℝ) / 2)), fun x => ?_⟩
    rw [iteratedFDeriv_tsum_apply (N := (⊤ : ℕ∞)) hfd (fun n hn => hv n hn)
      (fun n α x hn => hb0 n α x hn) (by exact_mod_cast le_top)]
    have hsn : Summable fun α => ‖iteratedFDeriv ℝ n (f α) x‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun α => by simpa using hbd 0 n α x) (hsum 0 n)
    calc ‖x‖ ^ k * ‖∑' α, iteratedFDeriv ℝ n (f α) x‖ ≤ ‖x‖ ^ k * ∑' α, ‖iteratedFDeriv ℝ n (f α) x‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsn) (by positivity)
      _ = ∑' α, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (f α) x‖ := (tsum_mul_left).symm
      _ ≤ _ := Summable.tsum_le_tsum (fun α => hbd k n α x) (hsn.mul_left _) (hsum k n)
  · intro β
    have hab := mov2d_summable_abs hd1 c hc 0
    simp only [Nat.cast_zero, zero_div, Real.rpow_zero, mul_one] at hab
    have hF : ∀ α, Integrable (fun x => f α x * hermiteFunD β x) := fun α => by
      have := (integrable_hermiteFunD_mul α β).const_mul (c α)
      simpa [hf, mul_assoc] using this
    have hint2 : ∀ α, ∫ x, ‖f α x * hermiteFunD β x‖ ≤ |c α| := fun α => by
      have hI : Integrable (fun x => (|c α| / 2) * (hermiteFunD α x * hermiteFunD α x +
          hermiteFunD β x * hermiteFunD β x)) :=
        ((integrable_hermiteFunD_mul α α).add (integrable_hermiteFunD_mul β β)).const_mul _
      have h1 : ∫ x, (|c α| / 2) * (hermiteFunD α x * hermiteFunD α x +
          hermiteFunD β x * hermiteFunD β x) = |c α| := by
        rw [integral_const_mul, integral_add (integrable_hermiteFunD_mul α α) (integrable_hermiteFunD_mul β β),
          hermiteFunD_orthonormal, hermiteFunD_orthonormal]
        simp; ring
      rw [← h1]
      refine integral_mono (hF α).norm hI fun x => ?_
      simp only [hf, norm_mul, Real.norm_eq_abs]
      have := abs_nonneg (c α)
      have e : |c α| * |hermiteFunD α x| * |hermiteFunD β x| ≤ |c α| / 2 *
          (hermiteFunD α x * hermiteFunD α x + hermiteFunD β x * hermiteFunD β x) := by
        have h2 : |hermiteFunD α x| * |hermiteFunD β x| ≤ (hermiteFunD α x * hermiteFunD α x +
            hermiteFunD β x * hermiteFunD β x) / 2 := by
          nlinarith [sq_nonneg (|hermiteFunD α x| - |hermiteFunD β x|), sq_abs (hermiteFunD α x),
            sq_abs (hermiteFunD β x)]
        nlinarith [mul_le_mul_of_nonneg_left h2 this]
      exact e
    have hsumF : Summable fun α => ∫ x, ‖f α x * hermiteFunD β x‖ :=
      Summable.of_nonneg_of_le (fun α => integral_nonneg fun x => norm_nonneg _) hint2 hab
    have hts := integral_tsum_of_summable_integral_norm hF hsumF
    unfold hermiteCoeff
    have e1 : (fun x => (∑' α, f α x) * hermiteFunD β x) = fun x => ∑' α, f α x * hermiteFunD β x := by
      funext x; rw [tsum_mul_right]
    show ∫ x, (∑' α, f α x) * hermiteFunD β x = c β
    rw [e1, ← hts]
    have e2 : ∀ α, ∫ x, f α x * hermiteFunD β x = if α = β then c α else 0 := by
      intro α
      simp only [hf, mul_assoc]
      rw [integral_const_mul, hermiteFunD_orthonormal]
      split_ifs <;> simp
    simp_rw [e2]
    rw [tsum_eq_single β]
    · simp
    · intro α hα; simp [hα]

end Seminorms

/-! ## F. Levels, coordinates and the Schwartz core -/

/-- The coordinate functional `x ↦ coord x α` on `OscSpace d r`. -/
def mov2d_coordL (r : ℝ) (α : MultiIndex d) : OscSpace d r →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun x => OscSpace.coord x α
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl } 1
    (fun x => by
      have := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
        (show lp (fun _ : MultiIndex d => ℝ) 2 from x) α
      show ‖OscSpace.coord x α‖ ≤ 1 * ‖x‖
      rw [one_mul]
      exact this)

lemma mov2d_coordL_apply (r : ℝ) (α : MultiIndex d) (x : OscSpace d r) :
    mov2d_coordL r α x = OscSpace.coord x α := rfl

/-- `j` rescales the coordinates by `λ_α^{(r'-r)/2}`. -/
lemma mov2d_j_coord {r r' : ℝ} (h : r' ≤ r) (x : OscSpace d r) (α : MultiIndex d) :
    OscSpace.coord (mov2d_j h x) α = oscEigenvalue d α ^ ((r' - r) / 2) * OscSpace.coord x α := by
  have key : ∀ x : OscSpace d r, mov2d_coordL r' α (mov2d_j h x) =
      oscEigenvalue d α ^ ((r' - r) / 2) * mov2d_coordL r α x := by
    refine fun x => (mov2d_e_dense r).induction_on x (isClosed_eq ?_ ?_) (fun c => ?_)
    · exact (mov2d_coordL r' α).continuous.comp (mov2d_j h).continuous
    · exact continuous_const.mul (mov2d_coordL r α).continuous
    · rw [mov2d_e_apply, mov2d_j_ofFun h (mov2d_hs_memOsc r c)]
      simp only [mov2d_coordL_apply]
      rw [OscSpace.coord_ofFun _ (mov2d_hs_memOsc r' c), OscSpace.coord_ofFun _ (mov2d_hs_memOsc r c)]
      rw [← mul_assoc, ← Real.rpow_add (oscEv_pos α)]
      congr 2; ring
  exact key x

/-- An element of level `0` that lies in every level is a Schwartz function. -/
lemma mov2d_exists_schwartz (hd1 : 1 ≤ d) (x : OscSpace d 0)
    (hx : ∀ N : ℕ, ∃ xN : OscSpace d (N : ℝ), mov2d_j (Nat.cast_nonneg N) xN = x) :
    ∃ ψ : 𝓢R, OscSpace.ofFun 0 (⇑ψ : Euc d → ℝ) = x := by
  have hc : ∀ N : ℕ, Summable fun α : MultiIndex d =>
      oscEigenvalue d α ^ (N : ℝ) * OscSpace.coord x α ^ 2 := by
    intro N
    obtain ⟨xN, hxN⟩ := hx N
    have h1 := lp_two_summable (ι := MultiIndex d) (show lp (fun _ : MultiIndex d => ℝ) 2 from xN)
    refine h1.congr fun α => ?_
    have := mov2d_j_coord (Nat.cast_nonneg N) xN α
    rw [hxN] at this
    show OscSpace.coord xN α ^ 2 = _
    have hL := oscEv_pos (d := d) α
    have e : OscSpace.coord xN α = oscEigenvalue d α ^ ((N : ℝ) / 2) * OscSpace.coord x α := by
      rw [this, ← mul_assoc, ← Real.rpow_add hL]
      have h0 : (N : ℝ) / 2 + (0 - (N : ℝ)) / 2 = 0 := by ring
      rw [h0, Real.rpow_zero, one_mul]
    rw [e, mul_pow, rpow_half_sq _ _ hL]
  obtain ⟨ψ, hψ⟩ := mov2d_series_schwartz hd1 (fun α => OscSpace.coord x α) hc
  refine ⟨ψ, ?_⟩
  apply lp.ext
  funext α
  change OscSpace.coord (OscSpace.ofFun 0 (⇑ψ : Euc d → ℝ)) α = OscSpace.coord x α
  rw [OscSpace.coord_ofFun _ (memOsc_schwartz 0 ψ), hψ α]
  simp

lemma mov2d_hasDerivWithinAt_Ici {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) (f' : E)
    (a : ℝ) (h : Tendsto (fun h : ℝ => h⁻¹ • (f (a + h) - f a)) (𝓝[>] 0) (𝓝 f')) :
    HasDerivWithinAt f f' (Set.Ici a) a := by
  rw [← hasDerivWithinAt_Ioi_iff_Ici, hasDerivWithinAt_iff_tendsto_slope]
  have hd : Set.Ioi a \ {a} = Set.Ioi a := Set.diff_singleton_eq_self (by simp)
  rw [hd]
  have hmap : Tendsto (fun y : ℝ => y - a) (𝓝[>] a) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun y : ℝ => y - a) (𝓝 a) (𝓝 (a - a)) := (continuous_sub_right a).tendsto a
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact sub_pos.2 (Set.mem_Ioi.1 hy)
  refine (h.comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp [slope_def_module, sub_add_cancel]

lemma mov2d_inner_ofFun {f g : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (hg : MemLp g 2 (volume : Measure (Euc d))) :
    inner ℝ (OscSpace.ofFun 0 f) (OscSpace.ofFun 0 g) = ∫ x, f x * g x := by
  have hfo : MemOsc 0 f := ⟨hf, by simpa using mov2b_coeff_sq_summable hf⟩
  have hgo : MemOsc 0 g := ⟨hg, by simpa using mov2b_coeff_sq_summable hg⟩
  rw [← (mova2_parseval_inner hf hg).tsum_eq]
  show ∑' i, inner ℝ (OscSpace.coord (OscSpace.ofFun 0 f) i) (OscSpace.coord (OscSpace.ofFun 0 g) i) = _
  refine tsum_congr fun α => ?_
  rw [OscSpace.coord_ofFun_eq hfo α, OscSpace.coord_ofFun_eq hgo α]
  simp [mul_comm]

section Core

variable {s : ℝ} {β q : ℝ} {ρ : Euc d → ℝ}

lemma mov2d_core_inv (H : Mov2dTh d s β q ρ) (φ : 𝓢R) {t : ℝ} (ht : 0 ≤ t) :
    ∃ ψ : 𝓢R, mov2d_G H 0 t (OscSpace.ofFun 0 (⇑φ : Euc d → ℝ)) = OscSpace.ofFun 0 (⇑ψ : Euc d → ℝ) := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  obtain ⟨ψ, hψ⟩ := mov2d_exists_schwartz hd1 (mov2d_G H 0 t (OscSpace.ofFun 0 (⇑φ : Euc d → ℝ)))
    (fun N => ⟨mov2d_G H (N : ℝ) t (OscSpace.ofFun (N : ℝ) (⇑φ : Euc d → ℝ)), by
      rw [mov2d_G_compat H (Nat.cast_nonneg N) ht, mov2d_j_ofFun _ (memOsc_schwartz (N : ℝ) φ)]⟩)
  exact ⟨ψ, hψ.symm⟩

/-- `∫ √ρ · (S ψ) = 0` in the order used below. -/
lemma mov2d_S_orth' (H : Mov2dTh d s β q ρ) (φ ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) :
    ∫ x, ψ0 x * movS d s β ρ φ x = 0 := by
  have := mov2d_S_orth H φ ψ0 hψ0
  rw [← this]
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hψ0]; ring)

lemma mov2d_movS_memLp (H : Mov2dTh d s β q ρ) (φ χ : 𝓢R) (hχ : (⇑χ : Euc d → ℝ) = mov_S0 d β q φ) :
    MemLp (movS d s β ρ (⇑φ : Euc d → ℝ)) 2 (volume : Measure (Euc d)) := by
  obtain ⟨ha0, ha2⟩ := mov2d_a_bounds d H.hd H.hsd
  obtain ⟨CR, -, hCR⟩ := mov2d_AR_bdd H 2
  have hAR2 := (hCR φ).1
  have hAR0 : MemOsc 0 (mov2d_AR d s β q ρ (fun z => φ z)) := (mo_mono (by linarith) hAR2).1
  rw [mov2d_movS_eq H φ χ hχ]
  exact (χ.memLp 2).add hAR0.1

/-- **`ℓ(G(t) x) = ℓ(x)`**: the functional `x ↦ ⟨√ρ, x⟩` is invariant under the flow. -/
theorem mov2d_ell_inv (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) (x : OscSpace d 0) {t : ℝ} (ht : 0 ≤ t) :
    inner ℝ (OscSpace.ofFun 0 (⇑ψ0 : Euc d → ℝ)) (mov2d_G H 0 t x) =
      inner ℝ (OscSpace.ofFun 0 (⇑ψ0 : Euc d → ℝ)) x := by
  set e1 : OscSpace d 0 := OscSpace.ofFun 0 (⇑ψ0 : Euc d → ℝ) with he1
  have hS : ∀ φ : 𝓢R, inner ℝ e1 (mov2d_G H 0 t (OscSpace.ofFun 0 (⇑φ : Euc d → ℝ))) =
      inner ℝ e1 (OscSpace.ofFun 0 (⇑φ : Euc d → ℝ)) := by
    intro φ
    set e : OscSpace d 0 := OscSpace.ofFun 0 (⇑φ : Euc d → ℝ) with he
    set u : ℝ → ℝ := fun τ => inner ℝ e1 (mov2d_G H 0 τ e) with hu
    have hcont : ContinuousOn u (Set.Icc 0 t) :=
      (continuous_const.inner continuous_id).comp_continuousOn
        ((mov2d_G_cont H 0 e).mono Set.Icc_subset_Ici_self)
    have hder : ∀ τ ∈ Set.Ico (0 : ℝ) t, HasDerivWithinAt u 0 (Set.Ici τ) τ := by
      intro τ hτ
      apply mov2d_hasDerivWithinAt_Ici
      obtain ⟨ψ, hψ⟩ := mov2d_core_inv H φ hτ.1
      obtain ⟨χ, hχ⟩ := mov2d_S0_schwartz (β := β) (q := q) ψ
      have hgen := mov2d_G_gen H ψ χ hχ
      have hlim := ((innerSL ℝ e1).continuous.tendsto _).comp hgen
      have hip : inner ℝ e1 (OscSpace.ofFun 0 (movS d s β ρ (⇑ψ : Euc d → ℝ))) = 0 := by
        rw [he1, mov2d_inner_ofFun (ψ0.memLp 2) (mov2d_movS_memLp H ψ χ hχ)]
        exact mov2d_S_orth' H ψ ψ0 hψ0
      have hzero : (innerSL ℝ e1) (-(OscSpace.ofFun 0 (movS d s β ρ (⇑ψ : Euc d → ℝ)))) = 0 := by
        rw [innerSL_apply_apply, inner_neg_right, hip, neg_zero]
      rw [Function.comp_def, hzero] at hlim
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh' : (0 : ℝ) ≤ h := le_of_lt hh
      have e1' : mov2d_G H 0 (τ + h) e = mov2d_G H 0 h (mov2d_G H 0 τ e) := mov2d_G_add H 0 hτ.1 hh' e
      simp only [hu, e1', hψ, innerSL_apply_apply, map_smul, inner_sub_right, inner_smul_right, smul_eq_mul]
      rw [hψ]
    have := constant_of_has_deriv_right_zero hcont hder t ⟨ht, le_rfl⟩
    simpa [hu, mov2d_G_zero] using this
  have hcl : IsClosed {x : OscSpace d 0 | inner ℝ e1 (mov2d_G H 0 t x) = inner ℝ e1 x} :=
    isClosed_eq (continuous_const.inner (mov2d_G H 0 t).continuous) (continuous_const.inner continuous_id)
  refine (mov2d_e_dense 0).induction_on x hcl fun c => ?_
  obtain ⟨φ, hφ⟩ := mov2d_hs_schwartz (d := d) c
  show inner ℝ e1 (mov2d_G H 0 t (OscSpace.ofFun 0 (mov2d_hs d c))) = inner ℝ e1 (OscSpace.ofFun 0 (mov2d_hs d c))
  rw [← hφ]
  exact hS φ

end Core

/-! ## G. The semigroup on `L²_0` -/

section Assembly

variable {s : ℝ} {β q : ℝ} {ρ : Euc d → ℝ}

/-- The isometry `Σ^0 = ℓ² ≃ L²` (Hermite coefficients). -/
def mov2d_Phi (d : ℕ) : OscSpace d 0 ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (Euc d)) :=
  (mov2b_basis d).repr.symm

lemma mov2d_Phi_ofFun {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) :
    mov2d_Phi d (OscSpace.ofFun 0 f) = hf.toLp f := by
  have hfo : MemOsc 0 f := ⟨hf, by simpa using mov2b_coeff_sq_summable hf⟩
  unfold mov2d_Phi
  have h2 : (mov2b_basis d).repr.symm ((mov2b_basis d).repr (hf.toLp f)) = hf.toLp f :=
    (mov2b_basis d).repr.symm_apply_apply _
  have e : (mov2b_basis d).repr (hf.toLp f) = (OscSpace.ofFun 0 f : lp (fun _ : MultiIndex d => ℝ) 2) := by
    apply lp.ext
    funext α
    rw [← mov2b_coeff_eq_repr hf α]
    change _ = OscSpace.coord (OscSpace.ofFun 0 f) α
    rw [OscSpace.coord_ofFun_eq hfo α]
    simp
  rw [e] at h2
  exact h2

lemma mov2d_sqrtLp (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) :
    movSqrtLp ρ = mov2d_Phi d (OscSpace.ofFun 0 (⇑ψ0 : Euc d → ℝ)) := by
  have hm : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by rw [← hψ0]; exact ψ0.memLp 2
  rw [mov2d_Phi_ofFun (ψ0.memLp 2)]
  unfold movSqrtLp
  rw [dif_pos hm]
  exact MemLp.toLp_congr hm (ψ0.memLp 2) (by rw [hψ0])

lemma mov2d_mem_zero_iff {v : Lp ℝ 2 (volume : Measure (Euc d))} :
    v ∈ MovL2Zero ρ ↔ inner ℝ (movSqrtLp ρ) v = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right

/-- The flow on `L²`. -/
def mov2d_Tl (H : Mov2dTh d s β q ρ) (t : ℝ) : Lp ℝ 2 (volume : Measure (Euc d)) →L[ℝ] Lp ℝ 2 (volume : Measure (Euc d)) :=
  (mov2d_Phi d).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((mov2d_G H 0 t).comp (mov2d_Phi d).symm.toContinuousLinearEquiv.toContinuousLinearMap)

lemma mov2d_Tl_apply (H : Mov2dTh d s β q ρ) (t : ℝ) (v : Lp ℝ 2 (volume : Measure (Euc d))) :
    mov2d_Tl H t v = mov2d_Phi d (mov2d_G H 0 t ((mov2d_Phi d).symm v)) := rfl

lemma mov2d_Tl_inv (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {t : ℝ} (ht : 0 ≤ t) {v : Lp ℝ 2 (volume : Measure (Euc d))} (hv : v ∈ MovL2Zero ρ) :
    mov2d_Tl H t v ∈ MovL2Zero ρ := by
  rw [mov2d_mem_zero_iff] at hv ⊢
  rw [mov2d_sqrtLp H ψ0 hψ0, mov2d_Tl_apply, LinearIsometryEquiv.inner_map_map, mov2d_ell_inv H ψ0 hψ0 _ ht]
  rw [mov2d_sqrtLp H ψ0 hψ0] at hv
  rw [← LinearIsometryEquiv.inner_map_map (mov2d_Phi d), LinearIsometryEquiv.apply_symm_apply]
  exact hv

open Classical in
/-- The semigroup `T(t)` on `L²_0`. -/
def mov2d_T (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    (t : ℝ) : MovL2Zero ρ →L[ℝ] MovL2Zero ρ :=
  if ht : 0 ≤ t then (mov2d_Tl H t).restrict (fun v hv => mov2d_Tl_inv H ψ0 hψ0 ht hv)
  else ContinuousLinearMap.id ℝ _

lemma mov2d_T_coe (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {t : ℝ} (ht : 0 ≤ t) (v : MovL2Zero ρ) :
    ((mov2d_T H ψ0 hψ0 t v : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) = mov2d_Tl H t v := by
  unfold mov2d_T
  rw [dif_pos ht]
  rfl

lemma mov2d_Tl_add (H : Mov2dTh d s β q ρ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (v : Lp ℝ 2 (volume : Measure (Euc d))) : mov2d_Tl H (a + b) v = mov2d_Tl H a (mov2d_Tl H b v) := by
  rw [mov2d_Tl_apply, mov2d_Tl_apply, mov2d_Tl_apply]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  rw [add_comm, mov2d_G_add H 0 hb ha]

lemma mov2d_Tl_zero (H : Mov2dTh d s β q ρ) (v : Lp ℝ 2 (volume : Measure (Euc d))) : mov2d_Tl H 0 v = v := by
  rw [mov2d_Tl_apply, mov2d_G_zero]
  simp

/-- The core `S`-membership of the ground state: `S φ ∈ L²_0`. -/
lemma mov2d_movS_mem (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    (φ χ : 𝓢R) (hχ : (⇑χ : Euc d → ℝ) = mov_S0 d β q φ) :
    ((mov2d_movS_memLp H φ χ hχ).toLp (movS d s β ρ (⇑φ : Euc d → ℝ))) ∈ MovL2Zero ρ := by
  rw [mov2d_mem_zero_iff, mov2d_sqrtLp H ψ0 hψ0, ← mov2d_Phi_ofFun (mov2d_movS_memLp H φ χ hχ),
    LinearIsometryEquiv.inner_map_map, mov2d_inner_ofFun (ψ0.memLp 2) (mov2d_movS_memLp H φ χ hχ)]
  exact mov2d_S_orth' H φ ψ0 hψ0

/-- The generator at the level of `L²`: the right slope of `t ↦ Tl t v` at `t`. -/
lemma mov2d_Tl_slope (H : Mov2dTh d s β q ρ) (φ χ : 𝓢R) (hχ : (⇑χ : Euc d → ℝ) = mov_S0 d β q φ)
    (v : Lp ℝ 2 (volume : Measure (Euc d)))
    (hy : (mov2d_Phi d).symm v = OscSpace.ofFun 0 (⇑φ : Euc d → ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun h : ℝ => h⁻¹ • (mov2d_Tl H (t + h) v - mov2d_Tl H t v)) (𝓝[>] 0)
      (𝓝 (-(mov2d_Tl H t ((mov2d_movS_memLp H φ χ hχ).toLp (movS d s β ρ (⇑φ : Euc d → ℝ)))))) := by
  set w0 : Lp ℝ 2 (volume : Measure (Euc d)) := (mov2d_movS_memLp H φ χ hχ).toLp (movS d s β ρ (⇑φ : Euc d → ℝ)) with hw0
  have hgen := mov2d_G_gen H φ χ hχ
  have hP : mov2d_Phi d (-(OscSpace.ofFun 0 (movS d s β ρ (⇑φ : Euc d → ℝ)))) = -w0 := by
    rw [map_neg, mov2d_Phi_ofFun (mov2d_movS_memLp H φ χ hχ)]
  have h1 := (((mov2d_Phi d).continuous.tendsto _).comp hgen)
  rw [Function.comp_def, hP] at h1
  have h2 := (((mov2d_Tl H t).continuous.tendsto _).comp h1)
  rw [Function.comp_def, map_neg] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : (0 : ℝ) ≤ h := le_of_lt hh
  rw [mov2d_Tl_add H ht hh', ← map_sub, ← map_smul]
  congr 1
  rw [map_smul, map_sub, ← hy]
  simp only [mov2d_Tl_apply, LinearIsometryEquiv.apply_symm_apply]

lemma mov2d_T_zero (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) :
    mov2d_T H ψ0 hψ0 0 = 1 := by
  refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
  rw [mov2d_T_coe H ψ0 hψ0 le_rfl, mov2d_Tl_zero]
  rfl

lemma mov2d_T_add (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    mov2d_T H ψ0 hψ0 (a + b) = mov2d_T H ψ0 hψ0 a * mov2d_T H ψ0 hψ0 b := by
  refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
  rw [mov2d_T_coe H ψ0 hψ0 (add_nonneg ha hb)]
  show _ = ((mov2d_T H ψ0 hψ0 a (mov2d_T H ψ0 hψ0 b v) : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d)))
  rw [mov2d_T_coe H ψ0 hψ0 ha, mov2d_T_coe H ψ0 hψ0 hb, mov2d_Tl_add H ha hb]

lemma mov2d_T_cont (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    (v : MovL2Zero ρ) : ContinuousOn (fun t => mov2d_T H ψ0 hψ0 t v) (Set.Ici 0) := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  have : ContinuousOn (fun t => mov2d_Phi d (mov2d_G H 0 t ((mov2d_Phi d).symm (v : Lp ℝ 2 (volume : Measure (Euc d))))))
      (Set.Ici 0) := (mov2d_Phi d).continuous.comp_continuousOn (mov2d_G_cont H 0 _)
  refine this.congr fun t ht => ?_
  show ((mov2d_T H ψ0 hψ0 t v : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) = _
  rw [mov2d_T_coe H ψ0 hψ0 ht, mov2d_Tl_apply]

lemma mov2d_T_gen (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    (φ : 𝓢R) (v : MovL2Zero ρ) (hv : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v x = φ x) :
    ∃ w : MovL2Zero ρ, (∀ᵐ x ∂(volume : Measure (Euc d)), movFun w x = movS d s β ρ φ x) ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (fun τ => mov2d_T H ψ0 hψ0 τ v) (-(mov2d_T H ψ0 hψ0 t w))
        (Set.Ici t) t := by
  obtain ⟨χ, hχ⟩ := mov2d_S0_schwartz (β := β) (q := q) φ
  have hφL : MemLp (fun z => φ z) 2 (volume : Measure (Euc d)) := φ.memLp 2
  have hv' : (⇑(v : Lp ℝ 2 (volume : Measure (Euc d))) : Euc d → ℝ) =ᵐ[volume] fun z => φ z := hv
  have hvφ : (v : Lp ℝ 2 (volume : Measure (Euc d))) = hφL.toLp _ :=
    Lp.ext (hv'.trans hφL.coeFn_toLp.symm)
  have hy : (mov2d_Phi d).symm (v : Lp ℝ 2 (volume : Measure (Euc d))) = OscSpace.ofFun 0 (⇑φ : Euc d → ℝ) := by
    rw [LinearIsometryEquiv.symm_apply_eq, mov2d_Phi_ofFun hφL, hvφ]
  refine ⟨⟨_, mov2d_movS_mem H ψ0 hψ0 φ χ hχ⟩, (mov2d_movS_memLp H φ χ hχ).coeFn_toLp, fun t ht => ?_⟩
  apply mov2d_hasDerivWithinAt_Ici
  rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
  have hcoe : ((-(mov2d_T H ψ0 hψ0 t) ⟨_, mov2d_movS_mem H ψ0 hψ0 φ χ hχ⟩ : MovL2Zero ρ) :
      Lp ℝ 2 (volume : Measure (Euc d))) =
      -(mov2d_Tl H t ((mov2d_movS_memLp H φ χ hχ).toLp (movS d s β ρ (⇑φ : Euc d → ℝ)))) := by
    rw [Submodule.coe_neg, mov2d_T_coe H ψ0 hψ0 ht]
  rw [Function.comp_def, hcoe]
  refine (mov2d_Tl_slope H φ χ hχ _ hy ht).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : (0 : ℝ) ≤ h := le_of_lt hh
  simp only [Submodule.coe_smul, Submodule.coe_sub]
  rw [mov2d_T_coe H ψ0 hψ0 (add_nonneg ht hh'), mov2d_T_coe H ψ0 hψ0 ht]

theorem mov2d_isSemigroup (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) :
    MovIsSemigroup d s β ρ (mov2d_T H ψ0 hψ0) :=
  ⟨mov2d_T_zero H ψ0 hψ0, fun _ _ ha hb => mov2d_T_add H ψ0 hψ0 ha hb, mov2d_T_cont H ψ0 hψ0,
    fun φ v hv => mov2d_T_gen H ψ0 hψ0 φ v hv⟩

/-! ## H. Uniqueness -/

lemma mov2d_slope_of_hasDerivWithinAt_Ici {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    {f' : E} {a : ℝ} (h : HasDerivWithinAt f f' (Set.Ici a) a) :
    Tendsto (fun h : ℝ => h⁻¹ • (f (a + h) - f a)) (𝓝[>] 0) (𝓝 f') := by
  rw [← hasDerivWithinAt_Ioi_iff_Ici, hasDerivWithinAt_iff_tendsto_slope] at h
  have hd : Set.Ioi a \ {a} = Set.Ioi a := Set.diff_singleton_eq_self (by simp)
  rw [hd] at h
  have hmap : Tendsto (fun y : ℝ => a + y) (𝓝[>] 0) (𝓝[>] a) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun y : ℝ => a + y) (𝓝 0) (𝓝 (a + 0)) := (continuous_const.add continuous_id).tendsto 0
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact lt_add_of_pos_right a (Set.mem_Ioi.1 hy)
  refine (h.comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp [slope_def_module]

lemma mov2d_unif_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (U : ℝ → E →L[ℝ] E) (hc : ∀ x, ContinuousOn (fun t => U t x) (Set.Ici 0)) (t : ℝ) :
    ∃ M : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) t, ‖U τ‖ ≤ M := by
  obtain ⟨M, hM⟩ := banach_steinhaus (g := fun i : Set.Icc (0 : ℝ) t => U i) (fun x => by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((hc x).mono (fun τ hτ => hτ.1))
    exact ⟨C, fun i => hC i i.2⟩)
  exact ⟨M, fun τ hτ => hM ⟨τ, hτ⟩⟩

/-- `T(σ) v` is again a.e. a Schwartz function when `v` is. -/
lemma mov2d_T_core (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    (φ : 𝓢R) (v : MovL2Zero ρ) (hv : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v x = φ x) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ φ' : 𝓢R, ∀ᵐ x ∂(volume : Measure (Euc d)), movFun (mov2d_T H ψ0 hψ0 σ v) x = φ' x := by
  have hφL : MemLp (fun z => φ z) 2 (volume : Measure (Euc d)) := φ.memLp 2
  have hv' : (⇑(v : Lp ℝ 2 (volume : Measure (Euc d))) : Euc d → ℝ) =ᵐ[volume] fun z => φ z := hv
  have hvφ : (v : Lp ℝ 2 (volume : Measure (Euc d))) = hφL.toLp _ := Lp.ext (hv'.trans hφL.coeFn_toLp.symm)
  have hy : (mov2d_Phi d).symm (v : Lp ℝ 2 (volume : Measure (Euc d))) = OscSpace.ofFun 0 (⇑φ : Euc d → ℝ) := by
    rw [LinearIsometryEquiv.symm_apply_eq, mov2d_Phi_ofFun hφL, hvφ]
  obtain ⟨φ', hφ'⟩ := mov2d_core_inv H φ hσ
  refine ⟨φ', ?_⟩
  have e : ((mov2d_T H ψ0 hψ0 σ v : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) = (φ'.memLp 2).toLp _ := by
    rw [mov2d_T_coe H ψ0 hψ0 hσ, mov2d_Tl_apply, hy, hφ', mov2d_Phi_ofFun (φ'.memLp 2)]
  have : movFun (mov2d_T H ψ0 hψ0 σ v) =ᵐ[volume] fun z => φ' z := by
    show (⇑((mov2d_T H ψ0 hψ0 σ v : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) : Euc d → ℝ) =ᵐ[volume] _
    rw [e]; exact (φ'.memLp 2).coeFn_toLp
  exact this

lemma mov2d_uniq_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T' T : ℝ → E →L[ℝ] E) (hT' : ∀ x, ContinuousOn (fun τ => T' τ x) (Set.Ici 0))
    (hT : ∀ x, ContinuousOn (fun τ => T τ x) (Set.Ici 0)) (v : E) (t : ℝ) :
    ContinuousOn (fun σ => T' (t - σ) (T σ v)) (Set.Icc 0 t) := by
  obtain ⟨M, hM⟩ := mov2d_unif_bound T' hT' t
  exact mov2d_strong_comp_cont T' (M := M) (S := Set.Icc 0 t) (τ := fun σ => t - σ) (g := fun σ => T σ v)
    (fun σ hσ => hM _ ⟨by linarith [hσ.2], by linarith [hσ.1]⟩) hT'
    (continuousOn_const.sub continuousOn_id) (fun σ hσ => by show 0 ≤ t - σ; linarith [hσ.2])
    ((hT v).mono (fun σ hσ => hσ.1))

lemma mov2d_uniq_slope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T' T : ℝ → E →L[ℝ] E) (M t σ : ℝ) (v : E) (hσ : σ ∈ Set.Ico (0 : ℝ) t)
    (hM : ∀ τ ∈ Set.Icc (0 : ℝ) t, ‖T' τ‖ ≤ M)
    (hadd' : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → T' (a + b) = T' a * T' b)
    (hadd : ∀ h : ℝ, 0 ≤ h → T (σ + h) v = T h (T σ v))
    (hslope : Tendsto (fun h : ℝ => h⁻¹ • (T h (T σ v) - T' h (T σ v))) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => h⁻¹ • (T' (t - (σ + h)) (T (σ + h) v) - T' (t - σ) (T σ v))) (𝓝[>] 0) (𝓝 0) := by
  have hB : Tendsto (fun h : ℝ => |M| * ‖h⁻¹ • (T h (T σ v) - T' h (T σ v))‖) (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_zero_iff_norm_tendsto_zero.1 hslope).const_mul |M|
    simpa using this
  refine squeeze_zero_norm' ?_ hB
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ h < t - σ := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < t - σ by linarith [hσ.2])] with h h1 h2
    exact ⟨h1, h2.2⟩
  filter_upwards [hpos] with h hh
  have e1 : T' (t - σ) (T σ v) = T' (t - σ - h) (T' h (T σ v)) := by
    have := hadd' (t - σ - h) h (by linarith [hh.2]) hh.1.le
    rw [show t - σ - h + h = t - σ by ring] at this
    rw [this]; rfl
  have e2 : T' (t - (σ + h)) (T (σ + h) v) = T' (t - σ - h) (T h (T σ v)) := by
    rw [hadd h hh.1.le, show t - (σ + h) = t - σ - h by ring]
  rw [e1, e2, ← map_sub, ← map_smul]
  refine ((T' (t - σ - h)).le_opNorm _).trans ?_
  exact mul_le_mul_of_nonneg_right ((hM _ ⟨by linarith [hh.2], by linarith [hσ.1, hh.1]⟩).trans (le_abs_self M))
    (norm_nonneg _)

lemma mov2d_uniq_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T' T : ℝ → E →L[ℝ] E) (M t σ : ℝ) (v : E) (hσ : σ ∈ Set.Ico (0 : ℝ) t)
    (hM : ∀ τ ∈ Set.Icc (0 : ℝ) t, ‖T' τ‖ ≤ M)
    (hadd' : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → T' (a + b) = T' a * T' b)
    (hadd : ∀ h : ℝ, 0 ≤ h → T (σ + h) v = T h (T σ v)) (hT0 : T 0 = 1) (hT'0 : T' 0 = 1) (w : E)
    (hwd : HasDerivWithinAt (fun τ => T τ (T σ v)) (-(T 0 w)) (Set.Ici 0) 0)
    (hwd' : HasDerivWithinAt (fun τ => T' τ (T σ v)) (-(T' 0 w)) (Set.Ici 0) 0) :
    HasDerivWithinAt (fun σ => T' (t - σ) (T σ v)) 0 (Set.Ici σ) σ := by
  apply mov2d_hasDerivWithinAt_Ici
  have h1 := mov2d_slope_of_hasDerivWithinAt_Ici hwd
  have h2 := mov2d_slope_of_hasDerivWithinAt_Ici hwd'
  rw [hT0] at h1
  rw [hT'0] at h2
  have h3 := h1.sub h2
  simp only [ContinuousLinearMap.one_apply, sub_self, zero_add, ← smul_sub] at h3
  refine mov2d_uniq_slope T' T M t σ v hσ hM hadd' hadd ?_
  refine h3.congr' ?_
  filter_upwards with h
  rw [sub_sub_sub_cancel_right]

/-- The two semigroups agree on the Schwartz core of `L²_0`. -/
lemma mov2d_uniq_core (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {T' : ℝ → (MovL2Zero ρ →L[ℝ] MovL2Zero ρ)} (hT' : MovIsSemigroup d s β ρ T')
    (φ : 𝓢R) (v : MovL2Zero ρ) (hv : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v x = φ x) {t : ℝ} (ht : 0 ≤ t) :
    T' t v = mov2d_T H ψ0 hψ0 t v := by
  have hTs : MovIsSemigroup d s β ρ (mov2d_T H ψ0 hψ0) := mov2d_isSemigroup H ψ0 hψ0
  obtain ⟨M, hM⟩ := mov2d_unif_bound T' hT'.cont t
  have hcont := mov2d_uniq_cont T' (mov2d_T H ψ0 hψ0) hT'.cont hTs.cont v t
  have hder : ∀ σ ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt (fun σ => T' (t - σ) (mov2d_T H ψ0 hψ0 σ v)) 0 (Set.Ici σ) σ := by
    intro σ hσ
    obtain ⟨φ', hφ'⟩ := mov2d_T_core H ψ0 hψ0 φ v hv hσ.1
    obtain ⟨w, hw, hwd⟩ := mov2d_T_gen H ψ0 hψ0 φ' (mov2d_T H ψ0 hψ0 σ v) hφ'
    obtain ⟨w', hw', hwd'⟩ := hT'.generator φ' (mov2d_T H ψ0 hψ0 σ v) hφ'
    have hww : w' = w := by
      refine Subtype.ext (Lp.ext ?_)
      filter_upwards [hw', hw] with x h1 h2
      exact h1.trans h2.symm
    have hwd'' := hwd' 0 le_rfl
    rw [hww] at hwd''
    have hadd : ∀ h : ℝ, 0 ≤ h →
        mov2d_T H ψ0 hψ0 (σ + h) v = mov2d_T H ψ0 hψ0 h (mov2d_T H ψ0 hψ0 σ v) := by
      intro h hh
      rw [add_comm, hTs.add h σ hh hσ.1]
      generalize mov2d_T H ψ0 hψ0 h = A
      generalize mov2d_T H ψ0 hψ0 σ = B
      rfl
    exact mov2d_uniq_step T' (mov2d_T H ψ0 hψ0) M t σ v hσ hM (fun a b ha hb => hT'.add a b ha hb)
      hadd (mov2d_T_zero H ψ0 hψ0) hT'.zero w (hwd 0 le_rfl) hwd''
  have := constant_of_has_deriv_right_zero hcont hder t ⟨ht, le_rfl⟩
  simpa [hT'.zero, mov2d_T_zero H ψ0 hψ0] using this.symm

end Assembly

end HRS.MS.MovLin
