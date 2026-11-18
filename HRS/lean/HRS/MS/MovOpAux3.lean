import HRS.MS.MovOpAux2

/-!
# MOV-C1 (3): `P` is bounded `Σ^r → Σ^{r-a}` for every real `r`; the frozen `mov_operators_P` (S6.1, step 9)

Namespace `HRS.MS.MovC1`, helper prefix `movc1_`.

**Statements.**
* `mov_P_bound` (file `MovOpAux3`): under the standing assumptions of `HRS.Whole.mov_operators_P`
  (`2 ≤ d`, `0 ≤ s < d`, `β, q > 0`, `IsThermalEquilibrium d s q β ρ`), for **every real** `r` there is `C ≥ 0` with
  `MemOsc (r - movA d s) (movP d s ρ v)` and `oscNorm (r - movA d s) (movP d s ρ v) ≤ C * oscNorm r v` for all Schwartz
  `v`.  Constants depend on `d, s, q, β, r` only (through `ρ = thermalDensity`).
* `mov_operators_P_proof`: the frozen `HRS.Whole.mov_operators_P` (the restriction `r ≥ -a` is dropped); the file ends
  with the tie `example := (@mov_operators_P_proof : type_of% @HRS.Whole.mov_operators_P)`.
* `movc1_P_bound_gen`: the same for any `MovcTherm d ρ q' B` (`GapRef d ρ q' B`, `q' > 0`).
* `mv1_far_pair` (plan step 4(b), pairing form of the far field): for `U_far = g_far * (ψ v)`, every real `r` and every
  `K`, the coordinate-iterated derivatives (order `≤ K`) of `∂_i U_far` and of `x_{i'} ∂_i U_far` are bounded uniformly
  in `x` by `C ‖v‖_{Σ^r}` (in the form `mova3b2_Q K 0 A b`, as used by the multiplier bridge `mo_mult_cb`); in
  particular `|∂_i U_far(x)| + ‖x‖ |∂_i U_far(x)| ≤ d C ‖v‖_{Σ^r}`.  The Fréchet-norm form `‖D^j ∇U_far‖` of the plan is
  not stated: the coordinate form is what the bridges consume.

**Proof architecture** (no new analysis beyond the merged bridges).
`movc1_P_decomp`: `P v = -ψ (∑_i g_loc*∂_i∂_i h + ∑_i (∂_iκ_i)*h + ∑_i ∂_i log ρ (g_loc*∂_i h + κ_i*h))`,
`h = ψ v`, `ψ = √ρ`, `κ_i = ∂_i g_far` (from `mv1_P_formula`, `movb2_ibp`, `movc1_ibp`).
Local terms: `ψ v ∈ H^r` (`movc1_B1`, B1 by duality for all real `r`), `∂_j : H^t → H^{t-1}`,
`g_loc * : H^t → H^{t+d-s}` (`tc3_riesz_loc_sobolev_gain`), `ψ·, (ψ ∂_i log ρ)· : H^σ → Σ^σ` (`mo_bridge2`)
(`movc1_loc_D1`, `movc1_loc_D2`), with `σ = r - a ≤ r - 2 + d - s` and `σ ≤ r - 1 + d - s`.
Far terms: `movc1_far_term` (pairing form of step 4(b), `mo_dual_le` + `mo_mult_cb`) for the kernels `∂_iκ_i`, `z_i κ_i`,
`κ_i`; the growing factor `-q' x_i` of `∂_i log ρ` is handled by `movc1_xT`
(`x_i (κ*h) = (z_i κ)*h + κ*(y_i h)`), the bounded part `B_i` by B3 (`movc1_mult_B`).  The six families are assembled by
the pointwise identity `movc1_P_identity` and the triangle inequality in `Σ^σ`.

`MemLp (movP v) 2` needs no separate argument: every term lies in `MemOsc σ`, which contains `L²`.

**Not delivered** (not needed by the frozen statement; row 11 of the plan, packet MOV-C3): `mov_Padj_bound`,
`mov_P_schwartz`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovC1

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.Mov0 HRS.MS.MovForce

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

section Decomp

variable {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

/-- Splitting the kernel `g = g_loc + g_far` in a convolution with a Gaussian-bounded continuous function. -/
lemma movc1_split_T {f : Euc d → ℝ} (hf : Continuous f) {c E : ℝ} (hc : 0 < c) (hE : 0 ≤ E)
    (h0 : ∀ y, |f y| ≤ E * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) :
    HRS.Whole.convFun (rieszKernel d s) f x = movb2_T (movb2_gloc d s) f x + movb2_T (movb2_gfar d s) f x := by
  have hI1 := movb2_T_integrable hd hs0 hsd (movb2_gloc_ker hd hs0 hsd) hc hE hf h0 x
  have hI2 := movb2_T_integrable hd hs0 hsd (movb2_gfar_ker hd hs0 hsd) hc hE hf h0 x
  rw [mv1_convFun_eq]
  unfold movb2_T
  rw [← integral_add hI1 hI2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [← add_mul, movb2_gloc_add_gfar]

/-- Linearity of `movb2_T` in the profile for finite sums. -/
lemma movc1_T_sum {ι : Type*} (S : Finset ι) {κ : Euc d → ℝ} (hκ : MovKer d s κ) {c : ℝ} (hc : 0 < c)
    {f : ι → Euc d → ℝ} {E : ι → ℝ} (hE : ∀ i, 0 ≤ E i) (hfc : ∀ i, Continuous (f i))
    (h0 : ∀ i y, |f i y| ≤ E i * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) :
    movb2_T κ (fun y => ∑ i ∈ S, f i y) x = ∑ i ∈ S, movb2_T κ (f i) x := by
  unfold movb2_T
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ fun i _ => movb2_T_integrable hd hs0 hsd hκ hc (hE i) (hfc i) (h0 i) x

lemma movc1_conv_int {f : Euc d → ℝ} (hf : Continuous f) {c E : ℝ} (hc : 0 < c) (hE : 0 ≤ E)
    (h0 : ∀ y, |f y| ≤ E * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) :
    Integrable (fun z => rieszKernel d s z * f (x - z)) volume := by
  have hI1 := movb2_T_integrable hd hs0 hsd (movb2_gloc_ker hd hs0 hsd) hc hE hf h0 x
  have hI2 := movb2_T_integrable hd hs0 hsd (movb2_gfar_ker hd hs0 hsd) hc hE hf h0 x
  refine (hI1.add hI2).congr (Eventually.of_forall fun z => ?_)
  show movb2_gloc d s z * f (x - z) + movb2_gfar d s z * f (x - z) = rieszKernel d s z * f (x - z)
  rw [← add_mul, movb2_gloc_add_gfar]

/-- **Exact decomposition of `P v`** into local and far parts (`h = ψ v`, `ψ = √ρ`):
`P v = -ψ (∑_i g_loc * ∂_i∂_i h + ∑_i (∂_i κ_i) * h + ∑_i ∂_i log ρ (g_loc * ∂_i h + κ_i * h))`,
`κ_i = ∂_i g_far`. -/
theorem movc1_P_decomp {ρ : Euc d → ℝ} (hpos : ∀ x, 0 < ρ x) (hρs : ContDiff ℝ ∞ ρ)
    (hψ : MovcG (fun y => Real.sqrt (ρ y))) (v : 𝓢R) (x : Euc d) :
    movP d s ρ v x = -(Real.sqrt (ρ x)) *
      ((∑ i : Fin d, movb2_T (movb2_gloc d s)
          (mova3b1_Dj i (mova3b1_Dj i (fun y => Real.sqrt (ρ y) * v y))) x) +
        (∑ i : Fin d, movb2_T (mova3b1_Dj i (movb2_kfar d s i)) (fun y => Real.sqrt (ρ y) * v y) x) +
        ∑ i : Fin d, gradient (fun y => Real.log (ρ y)) x i *
          (movb2_T (movb2_gloc d s) (mova3b1_Dj i (fun y => Real.sqrt (ρ y) * v y)) x +
            movb2_T (movb2_kfar d s i) (fun y => Real.sqrt (ρ y) * v y) x)) := by
  set h : Euc d → ℝ := fun y => Real.sqrt (ρ y) * v y with hhdef
  have hρd : MovRhoData d ρ := ⟨hpos, hρs, fun k => by
    obtain ⟨-, c, hc, hk⟩ := hψ
    obtain ⟨C, hC⟩ := hk k
    exact ⟨C, c, hc, hC⟩⟩
  rw [mv1_P_formula hd hs0 hsd hρd v x]
  have hh : MovcG h := movc1_schwartz_G_mul hψ v
  have hh1 : ∀ i, MovcG (mova3b1_Dj i h) := fun i => movc1_G_Dj hh i
  have hh2 : ∀ i, MovcG (mova3b1_Dj i (mova3b1_Dj i h)) := fun i => movc1_G_Dj (hh1 i) i
  -- Gaussian data
  obtain ⟨c0, E0, hc0, hE0, hga0⟩ := movc1_G_GA hh 1
  have hu0 : ContDiff ℝ 1 h := hh.1.of_le (by exact_mod_cast le_top)
  -- the gradient terms
  have hgrad : ∀ i : Fin d, HRS.Whole.convFun (rieszKernel d s) (fun y => gradient h y i) x =
      movb2_T (movb2_gloc d s) (mova3b1_Dj i h) x + movb2_T (movb2_kfar d s i) h x := by
    intro i
    have e : (fun y => gradient h y i) = mova3b1_Dj i h := by
      funext y; exact movtr_gradient_apply h y i
    rw [e]
    obtain ⟨c1, E1, hc1, hE1, hga1⟩ := movc1_G_GA (hh1 i) 1
    obtain ⟨h01, -⟩ := movb2_GA_01 hga1
    rw [movc1_split_T hd hs0 hsd (hh1 i).1.continuous hc1 hE1 h01 x]
    congr 1
    exact movb2_ibp hd hs0 hsd hc0 hu0 hga0 i x
  -- the Laplacian term
  have hlap : HRS.Whole.convFun (rieszKernel d s) (fun y => Laplacian.laplacian h y) x =
      (∑ i : Fin d, movb2_T (movb2_gloc d s) (mova3b1_Dj i (mova3b1_Dj i h)) x) +
        ∑ i : Fin d, movb2_T (mova3b1_Dj i (movb2_kfar d s i)) h x := by
    have e : (fun y => Laplacian.laplacian h y) = fun y => ∑ i : Fin d, mova3b1_Dj i (mova3b1_Dj i h) y := by
      funext y
      exact mv1_laplacian_eq (hh.1.of_le (by norm_num)) y
    rw [e, mv1_convFun_eq]
    have hint : ∀ i : Fin d, Integrable (fun z => rieszKernel d s z * mova3b1_Dj i (mova3b1_Dj i h) (x - z)) volume := by
      intro i
      obtain ⟨c2, E2, hc2, hE2, hga2⟩ := movc1_G_GA (hh2 i) 1
      obtain ⟨h02, -⟩ := movb2_GA_01 hga2
      exact movc1_conv_int hd hs0 hsd (hh2 i).1.continuous hc2 hE2 h02 x
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun i _ => hint i, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨c2, E2, hc2, hE2, hga2⟩ := movc1_G_GA (hh2 i) 1
    obtain ⟨h02, -⟩ := movb2_GA_01 hga2
    obtain ⟨c1, E1, hc1, hE1, hga1⟩ := movc1_G_GA (hh1 i) 1
    have hsp := movc1_split_T hd hs0 hsd (hh2 i).1.continuous hc2 hE2 h02 x
    rw [mv1_convFun_eq] at hsp
    rw [hsp]
    congr 1
    -- ∂_i ∂_i h against g_far
    have hu1 : ContDiff ℝ 1 (mova3b1_Dj i h) := (hh1 i).1.of_le (by exact_mod_cast le_top)
    have s1 := movb2_ibp hd hs0 hsd hc1 hu1 hga1 i x
    have hκ : MovcB (movb2_kfar d s i) := movc1_K_B (movc1_kfar_K hs0 i)
    obtain ⟨A, hA0, hA⟩ := movc1_B_Bd hκ 1
    have s2 := movc1_ibp hd hs0 hsd hκ.1 hA hc0 hu0 hga0 i x
    exact s1.trans s2
  have hgrad' : ∀ i : Fin d, HRS.Whole.convFun (rieszKernel d s)
      (fun y => gradient (fun z => Real.sqrt (ρ z) * v z) y i) x =
      movb2_T (movb2_gloc d s) (mova3b1_Dj i h) x + movb2_T (movb2_kfar d s i) h x := fun i => hgrad i
  rw [hlap]
  simp only [hgrad']

end Decomp

/-! ### Thermal data -/

lemma movc1_proj_norm_le (i : Fin d) : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  have : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) w‖ ≤ ‖w‖ := by simpa using PiLp.norm_apply_le w i
  simpa using this

lemma movc1_comp_iter_le {F : Euc d → Euc d} (hF : ContDiff ℝ ∞ F) (i : Fin d) (k : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ k (fun y => F y i) x‖ ≤ ‖iteratedFDeriv ℝ k F x‖ := by
  have h := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left
    (hF.contDiffAt) (x := x) (n := k) (by exact_mod_cast le_top)
  have e : ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) ∘ F) = fun y => F y i := rfl
  rw [e] at h
  exact h.trans (mul_le_of_le_one_left (norm_nonneg _) (movc1_proj_norm_le i))

lemma movc1_comp_B {F : Euc d → Euc d} (hF : ContDiff ℝ ∞ F) (hFb : ∀ k : ℕ, ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ M)
    (i : Fin d) : MovcB (fun y => F y i) := by
  refine ⟨(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.comp hF, fun k => ?_⟩
  obtain ⟨M, hM⟩ := hFb k
  exact ⟨M, fun x => (movc1_comp_iter_le hF i k x).trans (hM x)⟩

/-- Data of the thermal density: `ψ = √ρ ∈ MovcG`, and the coordinates `ℓ_i = ∂_i log ρ` are smooth with linearly
growing derivatives. -/
structure MovcTherm (d : ℕ) (ρ : Euc d → ℝ) (q' : ℝ) (B : Euc d → Euc d) : Prop where
  hq : 0 < q'
  R : HRS.MS.Gap.GapRef d ρ q' B

lemma MovcTherm.psi {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (h : MovcTherm d ρ q' B) :
    MovcG (fun y => Real.sqrt (ρ y)) := by
  obtain ⟨hs, -, c, hc, hk⟩ := mv0_sqrt_gauss h.hq h.R
  exact ⟨hs, c, hc, hk⟩

lemma MovcTherm.ell_eq {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (h : MovcTherm d ρ q' B) (x : Euc d) (i : Fin d) :
    gradient (fun y => Real.log (ρ y)) x i = -q' * x i + B x i := by
  rw [mov0_grad_log h.R x]
  simp

lemma MovcTherm.B_B {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (h : MovcTherm d ρ q' B) (i : Fin d) :
    MovcB (fun y => B y i) := by
  refine movc1_comp_B (mov0_B_smooth h.R) (fun k => ?_) i
  obtain ⟨Mb, hMb⟩ := h.R.cb k
  exact ⟨Mb, fun x => hMb.2 k le_rfl x⟩

lemma MovcTherm.ell_smooth {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (h : MovcTherm d ρ q' B) :
    ContDiff ℝ ∞ (fun y => gradient (fun z => Real.log (ρ z)) y) := by
  have : (fun y => gradient (fun z => Real.log (ρ z)) y) = fun y => (-q') • y + B y :=
    funext (mov0_grad_log h.R)
  rw [this]
  exact (contDiff_id.const_smul (-q')).add (mov0_B_smooth h.R)

lemma MovcTherm.psi_ell {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (h : MovcTherm d ρ q' B) (i : Fin d) :
    MovcG (fun x => Real.sqrt (ρ x) * gradient (fun y => Real.log (ρ y)) x i) := by
  obtain ⟨hdl, M, hM⟩ := mv0_dlog_bounds h.hq.le h.R
  have hsm := h.ell_smooth
  have hG : MovcG (fun x => gradient (fun y => Real.log (ρ y)) x i * Real.sqrt (ρ x)) := by
    refine movc1_G_mul h.psi ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.comp hsm) (fun k => ?_)
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      refine ⟨max (max q' M) 0, le_max_right _ _, fun x => ?_⟩
      rw [norm_iteratedFDeriv_zero]
      have h1 : ‖gradient (fun y => Real.log (ρ y)) x i‖ ≤ ‖gradient (fun y => Real.log (ρ y)) x‖ := by
        simpa using PiLp.norm_apply_le (gradient (fun y => Real.log (ρ y)) x) i
      have h2 := hM x
      have hm1 : q' ≤ max (max q' M) 0 := (le_max_left _ _).trans (le_max_left _ _)
      have hm2 : M ≤ max (max q' M) 0 := (le_max_right _ _).trans (le_max_left _ _)
      have hn := norm_nonneg x
      change ‖(gradient (fun y => Real.log (ρ y)) x) i‖ ≤ _
      nlinarith [mul_le_mul_of_nonneg_right hm1 hn]
    · obtain ⟨C, hC⟩ := hdl k hpos
      refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
      refine (movc1_comp_iter_le hsm i k x).trans ((hC x).trans ?_)
      have := norm_nonneg x
      nlinarith [le_max_left C 0, le_max_right C 0]
  have e : (fun x => Real.sqrt (ρ x) * gradient (fun y => Real.log (ρ y)) x i) =
      fun x => gradient (fun y => Real.log (ρ y)) x i * Real.sqrt (ρ x) := by funext x; ring
  rw [e]; exact hG

/-! ### Local terms for the profile `h = ψ v` -/

lemma movc1_D_coe (F : 𝓢R) (i : Fin d) : (⇑(mova1_D i F) : Euc d → ℝ) = mova3b1_Dj i ⇑F := by
  funext x; exact mova1_D_apply i F x

/-- Local term with two derivatives on the profile. -/
theorem movc1_loc_D2 {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ps b : Euc d → ℝ} (hps : MovcG ps) (hb : MovcG b)
    (r σ : ℝ) (hσ : σ ≤ r - 1 - 1 + ((d : ℝ) - s)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : 𝓢R) (i : Fin d),
      MemOsc σ (fun x => b x * movb2_T (movb2_gloc d s) (mova3b1_Dj i (mova3b1_Dj i (fun y => ps y * v y))) x) ∧
        oscNorm σ (fun x => b x * movb2_T (movb2_gloc d s)
          (mova3b1_Dj i (mova3b1_Dj i (fun y => ps y * v y))) x) ≤ C * oscNorm r v := by
  obtain ⟨C1, hC1, hB1⟩ := movc1_B1 hps r
  obtain ⟨C2, hC2, hloc⟩ := movc1_loc_term hs0 hsd hb hσ
  refine ⟨C2 * C1, mul_nonneg hC2 hC1, fun v i => ?_⟩
  obtain ⟨F, hF⟩ := movc1_G_schwartz (movc1_schwartz_G_mul hps v)
  obtain ⟨hFm, hFn⟩ := hB1 v
  rw [← hF] at hFm hFn ⊢
  obtain ⟨hD1, hD1n⟩ := movc1_sob_D F i hFm
  obtain ⟨hD2, hD2n⟩ := movc1_sob_D (mova1_D i F) i hD1
  rw [← movc1_D_coe, ← movc1_D_coe]
  obtain ⟨h1, h2⟩ := hloc _ hD2
  refine ⟨h1, h2.trans ?_⟩
  have h3 : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (r - 1 - 1) (⇑(mova1_D i (mova1_D i F)))) ≤ C1 * oscNorm r v :=
    (Real.sqrt_le_sqrt (hD2n.trans hD1n)).trans hFn
  calc C2 * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (r - 1 - 1) (⇑(mova1_D i (mova1_D i F))))
      ≤ C2 * (C1 * oscNorm r v) := mul_le_mul_of_nonneg_left h3 hC2
    _ = _ := by ring

/-- Local term with one derivative on the profile. -/
theorem movc1_loc_D1 {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ps b : Euc d → ℝ} (hps : MovcG ps) (hb : MovcG b)
    (r σ : ℝ) (hσ : σ ≤ r - 1 + ((d : ℝ) - s)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : 𝓢R) (i : Fin d),
      MemOsc σ (fun x => b x * movb2_T (movb2_gloc d s) (mova3b1_Dj i (fun y => ps y * v y)) x) ∧
        oscNorm σ (fun x => b x * movb2_T (movb2_gloc d s)
          (mova3b1_Dj i (fun y => ps y * v y)) x) ≤ C * oscNorm r v := by
  obtain ⟨C1, hC1, hB1⟩ := movc1_B1 hps r
  obtain ⟨C2, hC2, hloc⟩ := movc1_loc_term hs0 hsd hb hσ
  refine ⟨C2 * C1, mul_nonneg hC2 hC1, fun v i => ?_⟩
  obtain ⟨F, hF⟩ := movc1_G_schwartz (movc1_schwartz_G_mul hps v)
  obtain ⟨hFm, hFn⟩ := hB1 v
  rw [← hF] at hFm hFn ⊢
  obtain ⟨hD1, hD1n⟩ := movc1_sob_D F i hFm
  rw [← movc1_D_coe]
  obtain ⟨h1, h2⟩ := hloc _ hD1
  refine ⟨h1, h2.trans ?_⟩
  have h3 : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (r - 1) (⇑(mova1_D i F))) ≤ C1 * oscNorm r v :=
    (Real.sqrt_le_sqrt hD1n).trans hFn
  calc C2 * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (r - 1) (⇑(mova1_D i F)))
      ≤ C2 * (C1 * oscNorm r v) := mul_le_mul_of_nonneg_left h3 hC2
    _ = _ := by ring

/-! ### Families and linear combinations in `Σ^σ` -/

lemma movc1_osc_fam (σ : ℝ) {f : Fin d → Euc d → ℝ} {C : Fin d → ℝ} {K N : ℝ} (hK : ∀ i, C i ≤ K)
    (hN : 0 ≤ N) (h : ∀ i, MemOsc σ (f i) ∧ oscNorm σ (f i) ≤ C i * N) :
    MemOsc σ (fun x => ∑ i, f i x) ∧ oscNorm σ (fun x => ∑ i, f i x) ≤ (d * K) * N := by
  obtain ⟨h1, h2⟩ := movc1_osc_sum σ Finset.univ (f := f) (fun i _ => (h i).1)
  refine ⟨h1, h2.trans ?_⟩
  calc ∑ i, oscNorm σ (f i) ≤ ∑ _i : Fin d, K * N :=
        Finset.sum_le_sum fun i _ => (h i).2.trans (mul_le_mul_of_nonneg_right (hK i) hN)
    _ = (d * K) * N := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma movc1_osc_lin (σ : ℝ) {f g : Euc d → ℝ} (a b : ℝ) (hf : MemOsc σ f) (hg : MemOsc σ g) :
    MemOsc σ (fun x => a * f x + b * g x) ∧
      oscNorm σ (fun x => a * f x + b * g x) ≤ |a| * oscNorm σ f + |b| * oscNorm σ g := by
  obtain ⟨h1, h1n⟩ := movc1_osc_smul σ a hf
  obtain ⟨h2, h2n⟩ := movc1_osc_smul σ b hg
  obtain ⟨h3, h3n⟩ := movc1_osc_add σ h1 h2
  refine ⟨h3, h3n.trans ?_⟩
  rw [h1n, h2n]

/-! ### The six families of terms of `P v` -/

section Main

variable {s : ℝ} {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d}

/-- `ψ g_loc * ∂_i∂_i h`. -/
def movc1_U1 (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (v : Euc d → ℝ) (i : Fin d) (x : Euc d) : ℝ :=
  Real.sqrt (ρ x) * movb2_T (movb2_gloc d s)
    (mova3b1_Dj i (mova3b1_Dj i (fun y => Real.sqrt (ρ y) * v y))) x

/-- `(∂_i κ_i) * h · ψ`. -/
def movc1_U2 (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (v : Euc d → ℝ) (i : Fin d) (x : Euc d) : ℝ :=
  movb2_T (mova3b1_Dj i (movb2_kfar d s i)) (fun y => Real.sqrt (ρ y) * v y) x * Real.sqrt (ρ x)

/-- `ψ ∂_i log ρ · (g_loc * ∂_i h)`. -/
def movc1_U3 (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (v : Euc d → ℝ) (i : Fin d) (x : Euc d) : ℝ :=
  (Real.sqrt (ρ x) * gradient (fun y => Real.log (ρ y)) x i) *
    movb2_T (movb2_gloc d s) (mova3b1_Dj i (fun y => Real.sqrt (ρ y) * v y)) x

/-- `((z_i κ_i) * h) ψ`. -/
def movc1_U4 (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (v : Euc d → ℝ) (i : Fin d) (x : Euc d) : ℝ :=
  movb2_T (fun z => z i * movb2_kfar d s i z) (fun y => Real.sqrt (ρ y) * v y) x * Real.sqrt (ρ x)

/-- `(κ_i * (y_i ψ v)) ψ`. -/
def movc1_U5 (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (v : Euc d → ℝ) (i : Fin d) (x : Euc d) : ℝ :=
  movb2_T (movb2_kfar d s i) (fun y => (y i * Real.sqrt (ρ y)) * v y) x * Real.sqrt (ρ x)

/-- `B_i · ((κ_i * h) ψ)`. -/
def movc1_U6 (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (B : Euc d → Euc d) (v : Euc d → ℝ) (i : Fin d) (x : Euc d) : ℝ :=
  B x i * (movb2_T (movb2_kfar d s i) (fun y => Real.sqrt (ρ y) * v y) x * Real.sqrt (ρ x))

variable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

/-- **Pointwise identity**: `P v = -∑U1 - ∑U2 - ∑U3 + q' ∑U4 + q' ∑U5 - ∑U6`. -/
theorem movc1_P_identity (T : MovcTherm d ρ q' B) (v : 𝓢R) (x : Euc d) :
    movP d s ρ v x = -(∑ i, movc1_U1 d s ρ v i x) - (∑ i, movc1_U2 d s ρ v i x) - (∑ i, movc1_U3 d s ρ v i x)
      + q' * (∑ i, movc1_U4 d s ρ v i x) + q' * (∑ i, movc1_U5 d s ρ v i x) - ∑ i, movc1_U6 d s ρ B v i x := by
  rw [movc1_P_decomp hd hs0 hsd T.R.pos T.R.smooth T.psi v x]
  set ψx := Real.sqrt (ρ x) with hψx
  have hh : MovcG (fun y => Real.sqrt (ρ y) * v y) := movc1_schwartz_G_mul T.psi v
  have hper : ∀ i : Fin d,
      -ψx * (movb2_T (movb2_gloc d s) (mova3b1_Dj i (mova3b1_Dj i (fun y => Real.sqrt (ρ y) * v y))) x +
        movb2_T (mova3b1_Dj i (movb2_kfar d s i)) (fun y => Real.sqrt (ρ y) * v y) x +
        gradient (fun y => Real.log (ρ y)) x i *
          (movb2_T (movb2_gloc d s) (mova3b1_Dj i (fun y => Real.sqrt (ρ y) * v y)) x +
            movb2_T (movb2_kfar d s i) (fun y => Real.sqrt (ρ y) * v y) x)) =
      -movc1_U1 d s ρ v i x - movc1_U2 d s ρ v i x - movc1_U3 d s ρ v i x + q' * movc1_U4 d s ρ v i x +
        q' * movc1_U5 d s ρ v i x - movc1_U6 d s ρ B v i x := by
    intro i
    have hκ : MovcB (movb2_kfar d s i) := movc1_K_B (movc1_kfar_K hs0 i)
    have hκ' : MovcB (fun z => z i * movb2_kfar d s i z) := movc1_coord_B (movc1_kfar_K hs0 i) i
    have hxT := movc1_xT hd hs0 hsd i hκ hκ' hh x
    have hU5 : movb2_T (movb2_kfar d s i) (fun y => (y i * Real.sqrt (ρ y)) * v y) x =
        movb2_T (movb2_kfar d s i) (fun y => y i * (Real.sqrt (ρ y) * v y)) x := by
      congr 1; funext y; ring
    simp only [movc1_U1, movc1_U2, movc1_U3, movc1_U4, movc1_U5, movc1_U6]
    rw [hU5, T.ell_eq x i]
    linear_combination (q' * ψx) * hxT
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i _ => hper i]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum]

omit hd hs0 hsd in
/-- A uniform constant for a finite family of constants. -/
lemma movc1_unif_const {ι : Type*} [Fintype ι] (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i, C i ≤ K :=
  ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC i, fun i => Finset.single_le_sum (f := C) (fun i _ => hC i) (Finset.mem_univ i)⟩

/-- **`P` is bounded `Σ^r → Σ^{r-a}` for every real `r`** (Schwartz `v`), general thermal data. -/
theorem movc1_P_bound_gen (T : MovcTherm d ρ q' B) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : 𝓢R, MemOsc (r - movA d s) (movP d s ρ v) ∧
      oscNorm (r - movA d s) (movP d s ρ v) ≤ C * oscNorm r v := by
  set σ : ℝ := r - movA d s with hσ
  have hma1 : (1 : ℝ) ≤ movA d s := le_max_left _ _
  have hma2 : (s : ℝ) + 2 - d ≤ movA d s := le_max_right _ _
  have hds : (0 : ℝ) < d - s := by linarith
  have hσ1 : σ ≤ r - 1 - 1 + ((d : ℝ) - s) := by rw [hσ]; linarith
  have hσ2 : σ ≤ r - 1 + ((d : ℝ) - s) := by rw [hσ]; linarith
  have hψ := T.psi
  -- U1
  obtain ⟨C1, hC1, h1⟩ := movc1_loc_D2 hs0 hsd hψ hψ r σ hσ1
  -- U3 (one constant per coordinate)
  choose C3 hC3 h3 using fun i : Fin d => movc1_loc_D1 hs0 hsd hψ (T.psi_ell i) r σ hσ2
  -- far kernels
  have hK : ∀ i : Fin d, MovcK (movb2_kfar d s i) := fun i => movc1_kfar_K hs0 i
  choose C2 hC2 h2 using fun i : Fin d =>
    movc1_far_term hd hs0 hsd hψ hψ (movc1_K_B (movc1_K_Dj (hK i) i)) r σ
  choose C4 hC4 h4 using fun i : Fin d =>
    movc1_far_term hd hs0 hsd hψ hψ (movc1_coord_B (hK i) i) r σ
  choose C5 hC5 h5 using fun i : Fin d =>
    movc1_far_term hd hs0 hsd (movc1_G_coord hψ i) hψ (movc1_K_B (hK i)) r σ
  choose C6 hC6 h6 using fun i : Fin d =>
    movc1_far_term hd hs0 hsd hψ hψ (movc1_K_B (hK i)) r σ
  choose CB hCB hB using fun i : Fin d => movc1_mult_B (T.B_B i) σ
  obtain ⟨K2, hK2, hK2'⟩ := movc1_unif_const C2 hC2
  obtain ⟨K3, hK3, hK3'⟩ := movc1_unif_const C3 hC3
  obtain ⟨K4, hK4, hK4'⟩ := movc1_unif_const C4 hC4
  obtain ⟨K5, hK5, hK5'⟩ := movc1_unif_const C5 hC5
  obtain ⟨K6, hK6, hK6'⟩ := movc1_unif_const (fun i => CB i * C6 i) (fun i => mul_nonneg (hCB i) (hC6 i))
  refine ⟨(d * C1) + (d * K2) + (d * K3) + |q'| * (d * K4) + |q'| * (d * K5) + (d * K6), by positivity, fun v => ?_⟩
  have hN : 0 ≤ oscNorm r v := movc1_osc_nonneg _ _
  obtain ⟨hm1, hn1⟩ := movc1_osc_fam σ (f := fun i => movc1_U1 d s ρ v i) (C := fun _ => C1) (K := C1) (N := oscNorm r v)
    (fun _ => le_rfl) hN (fun i => h1 v i)
  obtain ⟨hm2, hn2⟩ := movc1_osc_fam σ (f := fun i => movc1_U2 d s ρ v i) (C := C2) (K := K2) (N := oscNorm r v)
    hK2' hN (fun i => h2 i v)
  obtain ⟨hm3, hn3⟩ := movc1_osc_fam σ (f := fun i => movc1_U3 d s ρ v i) (C := C3) (K := K3) (N := oscNorm r v)
    hK3' hN (fun i => h3 i v i)
  obtain ⟨hm4, hn4⟩ := movc1_osc_fam σ (f := fun i => movc1_U4 d s ρ v i) (C := C4) (K := K4) (N := oscNorm r v)
    hK4' hN (fun i => h4 i v)
  obtain ⟨hm5, hn5⟩ := movc1_osc_fam σ (f := fun i => movc1_U5 d s ρ v i) (C := C5) (K := K5) (N := oscNorm r v)
    hK5' hN (fun i => h5 i v)
  obtain ⟨hm6, hn6⟩ := movc1_osc_fam σ (f := fun i => movc1_U6 d s ρ B v i) (C := fun i => CB i * C6 i) (K := K6)
    (N := oscNorm r v) hK6' hN (fun i => by
      obtain ⟨g1, g2⟩ := h6 i v
      obtain ⟨b1, b2⟩ := hB i _ g1
      refine ⟨b1, b2.trans ?_⟩
      calc CB i * oscNorm σ (fun x => movb2_T (movb2_kfar d s i) (fun y => Real.sqrt (ρ y) * v y) x * Real.sqrt (ρ x))
          ≤ CB i * (C6 i * oscNorm r v) := mul_le_mul_of_nonneg_left g2 (hCB i)
        _ = CB i * C6 i * oscNorm r v := by ring)
  obtain ⟨hp1, hpn1⟩ := movc1_osc_lin σ (-1) (-1) hm1 hm2
  obtain ⟨hp2, hpn2⟩ := movc1_osc_lin σ 1 (-1) hp1 hm3
  obtain ⟨hp3, hpn3⟩ := movc1_osc_lin σ 1 q' hp2 hm4
  obtain ⟨hp4, hpn4⟩ := movc1_osc_lin σ 1 q' hp3 hm5
  obtain ⟨hp5, hpn5⟩ := movc1_osc_lin σ 1 (-1) hp4 hm6
  have e : movP d s ρ v = fun x => 1 * (1 * (1 * (1 * (-1 * (∑ i, movc1_U1 d s ρ v i x) +
      -1 * (∑ i, movc1_U2 d s ρ v i x)) + -1 * (∑ i, movc1_U3 d s ρ v i x)) +
      q' * (∑ i, movc1_U4 d s ρ v i x)) + q' * (∑ i, movc1_U5 d s ρ v i x)) +
      -1 * (∑ i, movc1_U6 d s ρ B v i x) := by
    funext x
    rw [movc1_P_identity hd hs0 hsd T v x]
    ring
  rw [e]
  refine ⟨hp5, ?_⟩
  simp only [abs_one, abs_neg] at hpn1 hpn2 hpn3 hpn4 hpn5
  have hq0 : 0 ≤ |q'| := abs_nonneg _
  have hq4 := mul_le_mul_of_nonneg_left hn4 hq0
  have hq5 := mul_le_mul_of_nonneg_left hn5 hq0
  linarith
end Main

/-! ### Step 4(b): the far potential in pairing form -/

lemma movc1_Q_add : ∀ {K m : ℕ} {A A' : ℝ} {b1 b2 : Euc d → ℝ}, ContDiff ℝ ∞ b1 → ContDiff ℝ ∞ b2 →
    mova3b2_Q K m A b1 → mova3b2_Q K m A' b2 → mova3b2_Q K m (A + A') (fun x => b1 x + b2 x) := by
  intro K
  induction K with
  | zero =>
    intro m A A' b1 b2 _ _ h1 h2 x
    calc |b1 x + b2 x| * (1 + ‖x‖) ^ m ≤ (|b1 x| + |b2 x|) * (1 + ‖x‖) ^ m :=
          mul_le_mul_of_nonneg_right (abs_add_le _ _) (by positivity)
      _ = |b1 x| * (1 + ‖x‖) ^ m + |b2 x| * (1 + ‖x‖) ^ m := by ring
      _ ≤ A + A' := add_le_add (h1 x) (h2 x)
  | succ K ih =>
    intro m A A' b1 b2 hb1 hb2 h1 h2
    refine ⟨fun x => ?_, fun j => ?_⟩
    · calc |b1 x + b2 x| * (1 + ‖x‖) ^ m ≤ (|b1 x| + |b2 x|) * (1 + ‖x‖) ^ m :=
            mul_le_mul_of_nonneg_right (abs_add_le _ _) (by positivity)
        _ = |b1 x| * (1 + ‖x‖) ^ m + |b2 x| * (1 + ‖x‖) ^ m := by ring
        _ ≤ A + A' := add_le_add (h1.1 x) (h2.1 x)
    · have e : mova3b1_Dj j (fun x => b1 x + b2 x) = fun x => mova3b1_Dj j b1 x + mova3b1_Dj j b2 x := by
        funext x
        simp only [mova3b1_Dj]
        rw [show (fun x => b1 x + b2 x) = b1 + b2 from rfl,
          ((hb1.differentiable (by simp) x).hasFDerivAt.add (hb2.differentiable (by simp) x).hasFDerivAt).fderiv]
        rfl
      rw [e]
      exact ih (mova3b2_contDiff_Dj j hb1) (mova3b2_contDiff_Dj j hb2) (h1.2 j) (h2.2 j)

section FarPair

variable {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

/-- `∂_i (g_far * h) = κ_i * h` with `κ_i = ∂_i g_far`. -/
lemma movc1_dUfar {h : Euc d → ℝ} (hh : MovcG h) (i : Fin d) :
    mova3b1_Dj i (movb2_T (movb2_gfar d s) h) = movb2_T (movb2_kfar d s i) h := by
  funext x
  obtain ⟨c, E, hc, hE, hga⟩ := movc1_G_GA hh 1
  have hu : ContDiff ℝ 1 h := hh.1.of_le (by exact_mod_cast le_top)
  obtain ⟨hF, hL⟩ := movb2_T_fderiv hd hs0 hsd (movb2_gfar_ker hd hs0 hsd) hc hu hga x
  simp only [mova3b1_Dj]
  rw [hF.fderiv, hL]
  exact movb2_ibp hd hs0 hsd hc hu hga i x

/-- **Far field, pairing form** (plan step 4(b), `mv1_far_pair`): for `U_far = g_far * (ψ v)` and every real `r`,
the coordinate-iterated derivatives (order `≤ K`) of `∂_i U_far` and of `x_{i'} ∂_i U_far` are bounded, uniformly
in `x`, by `C ‖v‖_{Σ^r}` (`mova3b2_Q K 0 A b` means `|∂_{j_1}⋯∂_{j_k} b| ≤ A` for `k ≤ K`); in particular
`|∂_i U_far(x)| + ‖x‖ |∂_i U_far(x)| ≤ d C ‖v‖_{Σ^r}`. -/
theorem mv1_far_pair {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (T : MovcTherm d ρ q' B) (r : ℝ) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i i' : Fin d) (v : 𝓢R),
      mova3b2_Q K 0 (C * oscNorm r v)
        (fun x => mova3b1_Dj i (movb2_T (movb2_gfar d s) (fun y => Real.sqrt (ρ y) * v y)) x) ∧
      mova3b2_Q K 0 (C * oscNorm r v)
        (fun x => x i' * mova3b1_Dj i (movb2_T (movb2_gfar d s) (fun y => Real.sqrt (ρ y) * v y)) x) := by
  obtain ⟨C0, hC0, hfar⟩ := movc1_farK hd hs0 hsd T.psi r
  have hK : ∀ i : Fin d, MovcK (movb2_kfar d s i) := fun i => movc1_kfar_K hs0 i
  choose C1 hC1 hfar1 using fun i' : Fin d => movc1_farK hd hs0 hsd (movc1_G_coord T.psi i') r
  -- derivative bounds of the kernels
  choose A hA0 hA using fun i : Fin d => movc1_B_Bd (movc1_K_B (hK i)) (⌈|r|⌉₊ + K)
  choose A' hA'0 hA' using fun p : Fin d × Fin d =>
    movc1_B_Bd (movc1_coord_B (hK p.1) p.2) (⌈|r|⌉₊ + K)
  have hCt : ∀ p : Fin d × Fin d, 0 ≤ C0 * A p.1 + C0 * A' p + C1 p.2 * A p.1 := fun p =>
    add_nonneg (add_nonneg (mul_nonneg hC0 (hA0 _)) (mul_nonneg hC0 (hA'0 p))) (mul_nonneg (hC1 _) (hA0 _))
  obtain ⟨Kt, hKt, hKt'⟩ := movc1_unif_const _ hCt
  refine ⟨Kt, hKt, fun i i' v => ?_⟩
  have hh : MovcG (fun y => Real.sqrt (ρ y) * v y) := movc1_schwartz_G_mul T.psi v
  have hN : 0 ≤ oscNorm r v := movc1_osc_nonneg _ _
  have hΘ : mova3b2_Q K 0 (C0 * A i * oscNorm r v) (movb2_T (movb2_kfar d s i) (fun y => Real.sqrt (ρ y) * v y)) :=
    hfar K (hA0 i) (movc1_K_B (hK i)) (hA i) v
  have hΘ1 : mova3b2_Q K 0 (C0 * A' (i, i') * oscNorm r v)
      (movb2_T (fun z => z i' * movb2_kfar d s i z) (fun y => Real.sqrt (ρ y) * v y)) :=
    hfar K (hA'0 (i, i')) (movc1_coord_B (hK i) i') (hA' (i, i')) v
  have hΘ2 : mova3b2_Q K 0 (C1 i' * A i * oscNorm r v)
      (movb2_T (movb2_kfar d s i) (fun y => (y i' * Real.sqrt (ρ y)) * v y)) :=
    hfar1 i' K (hA0 i) (movc1_K_B (hK i)) (hA i) v
  have hle : ∀ t : ℝ, 0 ≤ t → t ≤ Kt → t * oscNorm r v ≤ Kt * oscNorm r v := fun t _ ht =>
    mul_le_mul_of_nonneg_right ht hN
  have hkt := hKt' (i, i')
  simp only at hkt
  have e1 : (fun x => mova3b1_Dj i (movb2_T (movb2_gfar d s) (fun y => Real.sqrt (ρ y) * v y)) x) =
      movb2_T (movb2_kfar d s i) (fun y => Real.sqrt (ρ y) * v y) := by
    funext x
    rw [movc1_dUfar hd hs0 hsd hh i]
  refine ⟨?_, ?_⟩
  · rw [e1]
    refine mova3b2_Q_mono_A ?_ hΘ
    refine mul_le_mul_of_nonneg_right ?_ hN
    have : 0 ≤ C0 * A' (i, i') := mul_nonneg hC0 (hA'0 _)
    have : 0 ≤ C1 i' * A i := mul_nonneg (hC1 _) (hA0 _)
    linarith
  · have e2 : (fun x => x i' * mova3b1_Dj i (movb2_T (movb2_gfar d s) (fun y => Real.sqrt (ρ y) * v y)) x) =
        fun x => movb2_T (fun z => z i' * movb2_kfar d s i z) (fun y => Real.sqrt (ρ y) * v y) x +
          movb2_T (movb2_kfar d s i) (fun y => (y i' * Real.sqrt (ρ y)) * v y) x := by
      funext x
      rw [movc1_dUfar hd hs0 hsd hh i, movc1_xT hd hs0 hsd i' (movc1_K_B (hK i)) (movc1_coord_B (hK i) i') hh x]
      congr 1
      congr 1; funext y; ring
    rw [e2]
    refine mova3b2_Q_mono_A ?_ (movc1_Q_add (movc1_T_tg hd hs0 hsd (movc1_coord_B (hK i) i') hh).1
      (movc1_T_tg hd hs0 hsd (movc1_K_B (hK i)) (movc1_schwartz_G_mul (movc1_G_coord T.psi i') v)).1
      hΘ1 hΘ2)
    have h0 : 0 ≤ C0 * A i * oscNorm r v := mul_nonneg (mul_nonneg hC0 (hA0 i)) hN
    have h3 := mul_le_mul_of_nonneg_right hkt hN
    nlinarith

end FarPair

/-! ### The thermal statement and the tie with the frozen `mov_operators_P` -/

/-- **`mov_P_bound`** (S6.1, step 9, plan row 9): for every real `r` there is `C` with
`P v ∈ Σ^{r-a}` and `‖P v‖_{Σ^{r-a}} ≤ C ‖v‖_{Σ^r}` for all Schwartz `v` (`a = movA d s`).  True for all real `r`,
in particular for `r ≥ -a`. -/
theorem mov_P_bound {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β) (hq : 0 < q)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SchwartzMap (Euc d) ℝ, MemOsc (r - movA d s) (movP d s ρ v) ∧
      oscNorm (r - movA d s) (movP d s ρ v) ≤ C * oscNorm r v := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨B, -, hR, -⟩ := mv0_gapref hd hs0 hsd hq hβ hρ
  exact movc1_P_bound_gen hd1 hs0 hsd ⟨mul_pos hβ hq, hR⟩ r

/-- **`mov_operators_P_proof`**: the frozen statement `HRS.Whole.mov_operators_P` (S6.1, first assertion). -/
theorem mov_operators_P_proof {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) :
    ∀ r : ℝ, -movA d s ≤ r → ∃ C : ℝ, ∀ v : SchwartzMap (Euc d) ℝ,
      MemOsc (r - movA d s) (movP d s ρ v) ∧
        oscNorm (r - movA d s) (movP d s ρ v) ≤ C * oscNorm r v := by
  intro r _
  obtain ⟨C, -, hC⟩ := mov_P_bound hd hs0 hsd β q hβ hq ρ hρ r
  exact ⟨C, hC⟩

end HRS.MS.MovC1

/-- Tie: `mov_operators_P_proof` has exactly the type of the frozen statement. -/
example := (@HRS.MS.MovC1.mov_operators_P_proof : type_of% @HRS.Whole.mov_operators_P)

end
