import HRS.MS.MovOpAux3

/-!
# MOV-C3a (1): the force tail of the thermal density, temperate growth of `g * u`, `P(Schwartz) ⊂ Schwartz`

Namespace `HRS.MS.MovC1`, helper prefix `movc3a_`.  Infrastructure for S6.2/S6.3 (plan row 11); not manuscript rows.

* `mov_force_tail_thermal` (plan step 4(a) with `h = ρ`, section 5 item 10 of `docs/MOV_PLAN.md`): for the actual
  thermal density `ρ` (`IsThermalEquilibrium d s q β ρ`, so `ρ = thermalDensity` pointwise) the field
  `∇(g * ρ) = movForce d s ρ` is `C^∞` and for every `j` both `‖D^j ∇(g*ρ)(x)‖` and `‖x‖ ‖D^j ∇(g*ρ)(x)‖` are bounded
  (hence `(1 + ‖x‖) ‖D^j ∇(g*ρ)(x)‖ ≤ 2 C`).  The statement includes the smoothness conjunct, because
  `iteratedFDeriv` of a non-smooth function is junk.  The decay exponent `s + 1` of `mv1_far_direct` is not
  claimed (the local part of the force is controlled by `mv1_loc_cb` only through the first weight).
* `movc3a_Tg_*`: the full convolution `g * u` (`g = rieszKernel d s`, no splitting) of a Gaussian-class `u` is
  continuous, `C^∞`, of linear growth with every derivative (`HasTemperateGrowth`), and `∂_i (g * u) = g * ∂_i u`.
* `mov_P_schwartz`: `P v` is a Schwartz function for every Schwartz `v` (core invariance), stated as
  `∃ φ : SchwartzMap, ⇑φ = movP d s ρ v`.  Proved directly (`P v = ψ · (temperate-growth function)` with `ψ = √ρ` of
  Gaussian class and `SchwartzMap.smulLeftCLM`), not through `Σ^∞ = Schwartz`; the plan route would need
  `mo_int_equiv` for non-Schwartz functions.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovC1

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.Mov0 HRS.MS.MovForce

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-! ### The force tail of the thermal density -/

/-- **`mov_force_tail_thermal`** (plan row 11, section 5 item 10).  For the thermal density `ρ`, the force
`∇(g * ρ)` is `C^∞` and `‖D^j ∇(g*ρ)(x)‖`, `‖x‖ ‖D^j ∇(g*ρ)(x)‖` are bounded for every `j`. -/
theorem mov_force_tail_thermal {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β) (hq : 0 < q)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) :
    (∀ x, movForce d s ρ x = gradient (HRS.Whole.convFun (rieszKernel d s) ρ) x) ∧
      ContDiff ℝ ∞ (fun x => gradient (HRS.Whole.convFun (rieszKernel d s) ρ) x) ∧
      ∀ j : ℕ, ∃ C : ℝ, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (fun y => gradient (HRS.Whole.convFun (rieszKernel d s) ρ) y) x‖ ≤ C ∧
          ‖x‖ * ‖iteratedFDeriv ℝ j (fun y => gradient (HRS.Whole.convFun (rieszKernel d s) ρ) y) x‖ ≤ C := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨B, -, hR, -⟩ := mv0_gapref hd hs0 hsd hq hβ hρ
  have hq' : 0 < β * q := mul_pos hβ hq
  obtain ⟨hρs, c, hc, hk⟩ := mv0_hgauss_gapref hq' hR
  have hG : MovcG ρ := ⟨hρs, c, hc, hk⟩
  -- the force is the gradient of the potential
  obtain ⟨c1, E1, hc1, hE1, hga1⟩ := movc1_G_GA hG 1
  obtain ⟨h0, h1⟩ := movb2_GA_01 hga1
  have heq : ∀ x, movForce d s ρ x = gradient (HRS.Whole.convFun (rieszKernel d s) ρ) x := fun x =>
    (mv1_force_eq_grad hd1 hs0 hsd hc1 hE1 (hρs.of_le (by exact_mod_cast le_top)) h0 h1 x).1
  have hfun : (fun y => gradient (HRS.Whole.convFun (rieszKernel d s) ρ) y) = movForce d s ρ :=
    funext fun y => (heq y).symm
  have key : ∀ k : ℕ, ∃ C : ℝ, ContDiff ℝ (k : WithTop ℕ∞) (movForce d s ρ) ∧ ∀ x : Euc d,
      ‖iteratedFDeriv ℝ k (movForce d s ρ) x‖ ≤ C ∧ ‖x‖ * ‖iteratedFDeriv ℝ k (movForce d s ρ) x‖ ≤ C := by
    intro k
    obtain ⟨c2, E2, hc2, hE2, hga2⟩ := movc1_G_GA hG (k + 1)
    obtain ⟨C0, hC0, hC⟩ := mv1_force_deriv_bound (d := d) (s := s) hd1 hs0 hsd hc2 k
    obtain ⟨hcd, hb⟩ := hC (hρs.of_le (by exact_mod_cast le_top)) hga2
    exact ⟨C0 * E2, hcd, hb⟩
  refine ⟨heq, ?_, fun j => ?_⟩
  · rw [hfun]
    exact contDiff_infty.2 fun k => (key k).choose_spec.1
  · rw [hfun]
    obtain ⟨C, -, hC⟩ := key j
    exact ⟨C, hC⟩


/-! ### The full convolution `g * u`: growth, smoothness, derivatives -/

section Tg

variable {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)

omit hd hs0 hsd in
/-- The far kernel grows at most linearly. -/
lemma movc3a_gfar_le (hs0 : 0 ≤ s) (z : Euc d) : |movb2_gfar d s z| ≤ 1 + ‖z‖ := by
  by_cases hz : ‖z‖ ≤ 1
  · rw [movb2_gfar_eq_zero hz, abs_zero]; positivity
  · push Not at hz
    refine (movb2_abs_gfar_le s z).trans ?_
    unfold rieszKernel
    split_ifs with h0
    · have h1 : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hz.le
      have h2 := Real.log_le_sub_one_of_pos (by linarith : 0 < ‖z‖)
      rw [abs_neg, abs_of_nonneg h1]
      linarith
    · have h1 : ‖z‖ ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hz.le (by linarith)
      rw [abs_of_nonneg (by positivity)]
      linarith [norm_nonneg z]

include hd hs0 hsd

lemma movc3a_g_ker : MovKer d s (rieszKernel d s) := by
  refine ⟨(mv1_g_data (d := d) hd hs0 hsd (c := 1) one_pos).1, 1, zero_le_one, ?_⟩
  filter_upwards [(mv1_g_data (d := d) hd hs0 hsd (c := 1) one_pos).2.1] with z hz
  rw [one_mul]; exact hz

lemma movc3a_split {f : Euc d → ℝ} (hf : Continuous f) {c E : ℝ} (hc : 0 < c) (hE : 0 ≤ E)
    (h0 : ∀ y, |f y| ≤ E * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) :
    movb2_T (rieszKernel d s) f x = movb2_T (movb2_gloc d s) f x + movb2_T (movb2_gfar d s) f x := by
  have := movc1_split_T hd hs0 hsd hf hc hE h0 x
  rw [mv1_convFun_eq] at this
  exact this

/-- **Linear growth of `g * u`** for a Gaussian-bounded continuous `u`. -/
theorem movc3a_Tg_bound {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {E : ℝ} {u : Euc d → ℝ}, 0 ≤ E → Continuous u →
      (∀ y, |u y| ≤ E * Real.exp (-c * ‖y‖ ^ 2)) → ∀ x : Euc d,
        |movb2_T (rieszKernel d s) u x| ≤ K * E * (1 + ‖x‖) := by
  set L1 : ℝ := ∫ z, |movb2_gloc d s z| with hL1
  have hL1i : Integrable (fun z => |movb2_gloc d s z|) volume := (mv1_gloc_integrable hd hs0 hsd).1.abs
  have hL10 : 0 ≤ L1 := integral_nonneg fun z => abs_nonneg _
  set A1 : ℝ := movb2_A1 d c with hA1
  have hA10 : 0 ≤ A1 := movb2_A1_nonneg hc
  have hA1i := movb2_A1_integrable hd hc
  refine ⟨L1 + A1, add_nonneg hL10 hA10, fun {E u} hE hu h0 x => ?_⟩
  rw [movc3a_split hd hs0 hsd hu hc hE h0 x]
  -- local part
  have hloc : |movb2_T (movb2_gloc d s) u x| ≤ E * L1 := by
    have hb : ∀ z, ‖movb2_gloc d s z * u (x - z)‖ ≤ |movb2_gloc d s z| * E := fun z => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((h0 _).trans (mul_le_of_le_one_right hE (movb2_exp_le_one hc _)))
        (abs_nonneg _)
    have := norm_integral_le_of_norm_le (hL1i.mul_const E) (Filter.Eventually.of_forall hb)
    rw [integral_mul_const] at this
    rw [Real.norm_eq_abs] at this
    unfold movb2_T
    linarith [this.trans_eq (mul_comm _ _)]
  -- far part
  have hfar : |movb2_T (movb2_gfar d s) u x| ≤ E * (1 + ‖x‖) * A1 := by
    have hb : ∀ z, ‖movb2_gfar d s z * u (x - z)‖ ≤ E * (1 + ‖x‖) *
        ((1 + ‖x - z‖) * Real.exp (-c * ‖x - z‖ ^ 2)) := fun z => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := movc3a_gfar_le (d := d) (s := s) hs0 z
      have h2 : 1 + ‖z‖ ≤ (1 + ‖x‖) * (1 + ‖x - z‖) := by
        have : ‖z‖ ≤ ‖x‖ + ‖x - z‖ := by
          calc ‖z‖ = ‖x - (x - z)‖ := by simp
            _ ≤ _ := norm_sub_le _ _
        nlinarith [norm_nonneg x, norm_nonneg (x - z), mul_nonneg (norm_nonneg x) (norm_nonneg (x - z))]
      calc |movb2_gfar d s z| * |u (x - z)|
          ≤ ((1 + ‖x‖) * (1 + ‖x - z‖)) * (E * Real.exp (-c * ‖x - z‖ ^ 2)) :=
            mul_le_mul (h1.trans h2) (h0 _) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hΦ : Integrable (fun z => E * (1 + ‖x‖) *
        ((1 + ‖x - z‖) * Real.exp (-c * ‖x - z‖ ^ 2))) volume := by
      have := (hA1i.comp_sub_left x).const_mul (E * (1 + ‖x‖))
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp
    have := norm_integral_le_of_norm_le hΦ (Filter.Eventually.of_forall hb)
    rw [integral_const_mul] at this
    have e : ∫ z : Euc d, (1 + ‖x - z‖) * Real.exp (-c * ‖x - z‖ ^ 2) = A1 :=
      integral_sub_left_eq_self (fun y : Euc d => (1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) volume x
    rw [e, Real.norm_eq_abs] at this
    exact this
  calc |movb2_T (movb2_gloc d s) u x + movb2_T (movb2_gfar d s) u x|
      ≤ |movb2_T (movb2_gloc d s) u x| + |movb2_T (movb2_gfar d s) u x| := abs_add_le _ _
    _ ≤ E * L1 + E * (1 + ‖x‖) * A1 := add_le_add hloc hfar
    _ ≤ (L1 + A1) * E * (1 + ‖x‖) := by
        have : E * L1 ≤ E * L1 * (1 + ‖x‖) :=
          le_mul_of_one_le_right (mul_nonneg hE hL10) (by linarith [norm_nonneg x])
        nlinarith [mul_nonneg hE hA10, norm_nonneg x]

end Tg

section Tg2

variable {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

omit hd hs0 hsd in
lemma movc3a_G_abs {u : Euc d → ℝ} (hu : MovcG u) :
    ∃ c E : ℝ, 0 < c ∧ 0 ≤ E ∧ ∀ y, |u y| ≤ E * Real.exp (-c * ‖y‖ ^ 2) := by
  obtain ⟨c, E, hc, hE, hga⟩ := movc1_G_GA hu 0
  refine ⟨c, E, hc, hE, fun y => ?_⟩
  have := hga 0 le_rfl y
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

lemma movc3a_Tg_cont {u : Euc d → ℝ} (hu : MovcG u) : Continuous (movb2_T (rieszKernel d s) u) := by
  obtain ⟨c, E, hc, hE, h0⟩ := movc3a_G_abs hu
  exact movb2_T_continuous hd hs0 hsd (movc3a_g_ker hd hs0 hsd) hc hu.1.continuous h0 hE

/-- `∂_i (g * u) = g * ∂_i u` for a Gaussian-class `u`, with the line derivative statement. -/
lemma movc3a_Tg_hasLineDeriv {u : Euc d → ℝ} (hu : MovcG u) (i : Fin d) (x : Euc d) :
    HasLineDerivAt ℝ (movb2_T (rieszKernel d s) u) (movb2_T (rieszKernel d s) (mova3b1_Dj i u) x) x
      (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
  obtain ⟨c, E, hc, hE, hga⟩ := movc1_G_GA hu 1
  obtain ⟨hF, hL⟩ := movb2_T_fderiv hd hs0 hsd (movc3a_g_ker hd hs0 hsd) hc
    (hu.1.of_le (by exact_mod_cast le_top)) hga x
  have := hF.hasLineDerivAt (EuclideanSpace.single i (1 : ℝ) : Euc d)
  rwa [hL] at this

lemma movc3a_Tg_Dj {u : Euc d → ℝ} (hu : MovcG u) (i : Fin d) :
    mova3b1_Dj i (movb2_T (rieszKernel d s) u) = movb2_T (rieszKernel d s) (mova3b1_Dj i u) := by
  funext x
  obtain ⟨c, E, hc, hE, hga⟩ := movc1_G_GA hu 1
  obtain ⟨hF, hL⟩ := movb2_T_fderiv hd hs0 hsd (movc3a_g_ker hd hs0 hsd) hc
    (hu.1.of_le (by exact_mod_cast le_top)) hga x
  simp only [mova3b1_Dj]
  rw [hF.fderiv, hL]
  rfl

/-- `g * u` has temperate growth (all derivatives of linear growth) for `u` of Gaussian class. -/
theorem movc3a_Tg_tg {u : Euc d → ℝ} (hu : MovcG u) :
    Function.HasTemperateGrowth (movb2_T (rieszKernel d s) u) := by
  have hker := movc3a_g_ker hd hs0 hsd
  have hcd : ∀ k : ℕ, ContDiff ℝ (k : WithTop ℕ∞) (movb2_T (rieszKernel d s) u) := by
    intro k
    obtain ⟨c, E, hc, hE, hga⟩ := movc1_G_GA hu k
    exact movb2_T_contDiff hd hs0 hsd hker hc k (hu.1.of_le (by exact_mod_cast le_top)) hga
  refine ⟨contDiff_infty.2 hcd, fun n => ⟨1, ?_⟩⟩
  obtain ⟨c, E, hc, hE, hga⟩ := movc1_G_GA hu n
  obtain ⟨K, hK0, hK⟩ := movc3a_Tg_bound hd hs0 hsd (d := d) (s := s) hc
  have hwn : ContDiff ℝ (n : WithTop ℕ∞) u := hu.1.of_le (by exact_mod_cast le_top)
  refine ⟨K * E, fun x => ?_⟩
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m => ?_)
  rw [movb2_T_iter hd hs0 hsd hker hc n hwn hga x m]
  have hP : 0 ≤ ∏ i, ‖m i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hcont : Continuous (fun y => iteratedFDeriv ℝ n u y m) :=
    (continuous_eval_const m).comp
      (hwn.continuous_iteratedFDeriv (m := n) le_rfl)
  have := hK (E := E * ∏ i, ‖m i‖) (u := fun y => iteratedFDeriv ℝ n u y m) (mul_nonneg hE hP) hcont
    (fun y => by
      calc |iteratedFDeriv ℝ n u y m| ≤ ‖iteratedFDeriv ℝ n u y‖ * ∏ i, ‖m i‖ := by
            rw [← Real.norm_eq_abs]; exact (iteratedFDeriv ℝ n u y).le_opNorm m
        _ ≤ (E * Real.exp (-c * ‖y‖ ^ 2)) * ∏ i, ‖m i‖ :=
            mul_le_mul_of_nonneg_right (hga n le_rfl y) hP
        _ = E * (∏ i, ‖m i‖) * Real.exp (-c * ‖y‖ ^ 2) := by ring) x
  rw [Real.norm_eq_abs, pow_one]
  calc _ ≤ K * (E * ∏ i, ‖m i‖) * (1 + ‖x‖) := this
    _ = K * E * (1 + ‖x‖) * ∏ i, ‖m i‖ := by ring

end Tg2

/-! ### `P` maps Schwartz functions to Schwartz functions -/

section PSchwartz

variable {s : ℝ} {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d}

/-- `∂_i log ρ` has temperate growth. -/
lemma movc3a_ell_tg (T : MovcTherm d ρ q' B) (i : Fin d) :
    Function.HasTemperateGrowth (fun x => gradient (fun y => Real.log (ρ y)) x i) := by
  have e : (fun x => gradient (fun y => Real.log (ρ y)) x i) = fun x => (-q') * x i + B x i :=
    funext fun x => by rw [T.ell_eq x i]
  rw [e]
  have h1 : Function.HasTemperateGrowth (fun x : Euc d => x i) :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasTemperateGrowth
  exact ((Function.HasTemperateGrowth.const (-q')).mul h1).add (movc1_B_tg (T.B_B i))

lemma movc3a_DD_bound {h : Euc d → ℝ} (hh : ContDiff ℝ ∞ h) {c E : ℝ} (hga : movb2_GA 2 c E h) (i : Fin d)
    (y : Euc d) :
    |mova3b1_Dj i (mova3b1_Dj i h) y| ≤ E * Real.exp (-c * ‖y‖ ^ 2) := by
  have hn : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
  have h2 : ContDiff ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) h := hh.of_le (by norm_cast)
  have g1 := movb2_GA_partial h2 hga (EuclideanSpace.single i (1 : ℝ) : Euc d)
  have h1 : ContDiff ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (fun y => fderiv ℝ h y (EuclideanSpace.single i (1 : ℝ))) :=
    (movb2_partial_contDiff h2 _).of_le (by exact_mod_cast le_refl _)
  have g0 := movb2_GA_partial (k := 0) h1 (by simpa using g1) (EuclideanSpace.single i (1 : ℝ) : Euc d)
  have := g0 0 le_rfl y
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, hn] at this
  simp only [mul_one] at this
  exact this

variable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

/-- `g * Δh = ∑_i g * ∂_i∂_i h` for a Gaussian-class `h`. -/
lemma movc3a_conv_lap {h : Euc d → ℝ} (hh : MovcG h) (x : Euc d) :
    HRS.Whole.convFun (rieszKernel d s) (fun y => Laplacian.laplacian h y) x =
      ∑ i : Fin d, movb2_T (rieszKernel d s) (mova3b1_Dj i (mova3b1_Dj i h)) x := by
  obtain ⟨c, E, hc, hE, hga⟩ := movc1_G_GA hh 2
  have e : (fun y => Laplacian.laplacian h y) = fun y => ∑ i : Fin d, mova3b1_Dj i (mova3b1_Dj i h) y :=
    funext fun y => mv1_laplacian_eq (hh.1.of_le (by norm_cast)) y
  rw [e, mv1_convFun_eq]
  exact movc1_T_sum hd hs0 hsd (Finset.univ : Finset (Fin d)) (movc3a_g_ker hd hs0 hsd) hc
    (f := fun i => mova3b1_Dj i (mova3b1_Dj i h)) (E := fun _ => E) (fun _ => hE)
    (fun i => (movc1_G_Dj (movc1_G_Dj hh i) i).1.continuous)
    (fun i y => movc3a_DD_bound hh.1 hga i y) x

/-- The bracket of the `P` formula: `∑_i g * ∂_i∂_i h + ∑_i ∂_i log ρ · (g * ∂_i h)`. -/
def movc3a_br (d : ℕ) (s : ℝ) (ρ h : Euc d → ℝ) (x : Euc d) : ℝ :=
  (∑ i : Fin d, movb2_T (rieszKernel d s) (mova3b1_Dj i (mova3b1_Dj i h)) x) +
    ∑ i : Fin d, gradient (fun y => Real.log (ρ y)) x i * movb2_T (rieszKernel d s) (mova3b1_Dj i h) x

lemma movc3a_br_tg (T : MovcTherm d ρ q' B) {h : Euc d → ℝ} (hh : MovcG h) :
    Function.HasTemperateGrowth (movc3a_br d s ρ h) :=
  (Function.HasTemperateGrowth.sum (fun i _ => movc3a_Tg_tg hd hs0 hsd (movc1_G_Dj (movc1_G_Dj hh i) i))).add
    (Function.HasTemperateGrowth.sum
      (fun i _ => (movc3a_ell_tg T i).mul (movc3a_Tg_tg hd hs0 hsd (movc1_G_Dj hh i))))

/-- `P v = -(bracket) · ψ` for Schwartz `v`, `h = ψ v`. -/
lemma movc3a_P_eq (T : MovcTherm d ρ q' B) (v : 𝓢R) :
    movP d s ρ v = fun x => (-(movc3a_br d s ρ (fun y => Real.sqrt (ρ y) * v y) x)) * Real.sqrt (ρ x) := by
  have hρd : MovRhoData d ρ := ⟨T.R.pos, T.R.smooth, fun k => by
    obtain ⟨-, c, hc, hk⟩ := T.psi
    obtain ⟨C, hC⟩ := hk k
    exact ⟨C, c, hc, hC⟩⟩
  have hh : MovcG (fun y => Real.sqrt (ρ y) * v y) := movc1_schwartz_G_mul T.psi v
  set h : Euc d → ℝ := fun y => Real.sqrt (ρ y) * v y with hhdef
  funext x
  rw [mv1_P_formula hd hs0 hsd hρd v x, movc3a_conv_lap hd hs0 hsd hh x]
  have e : ∀ i : Fin d, HRS.Whole.convFun (rieszKernel d s)
      (fun y => gradient (fun z => Real.sqrt (ρ z) * v z) y i) x =
      movb2_T (rieszKernel d s) (mova3b1_Dj i h) x := by
    intro i
    have hfun : (fun y => gradient (fun z => Real.sqrt (ρ z) * v z) y i) = mova3b1_Dj i h :=
      funext fun y => movtr_gradient_apply h y i
    rw [hfun]
    exact mv1_convFun_eq _ _ x
  simp only [e, movc3a_br]
  ring

/-- **`P` of a Schwartz function is Schwartz**, general thermal data. -/
theorem movc3a_P_schwartz_gen (T : MovcTherm d ρ q' B) (v : 𝓢R) :
    ∃ φ : 𝓢R, ⇑φ = movP d s ρ v := by
  have hh : MovcG (fun y => Real.sqrt (ρ y) * v y) := movc1_schwartz_G_mul T.psi v
  have htg := movc3a_br_tg hd hs0 hsd T hh
  obtain ⟨ψS, hψS⟩ := movc1_G_schwartz T.psi
  refine ⟨SchwartzMap.smulLeftCLM ℝ (-(movc3a_br d s ρ (fun y => Real.sqrt (ρ y) * v y))) ψS, ?_⟩
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply htg.neg, movc3a_P_eq hd hs0 hsd T v, hψS]
  simp [smul_eq_mul]

end PSchwartz

/-- **`mov_P_schwartz`** (plan row 11, core invariance): for the thermal density `ρ`, `P` maps Schwartz functions to
Schwartz functions: `movP d s ρ v` is (the underlying function of) a `SchwartzMap`. -/
theorem mov_P_schwartz {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β) (hq : 0 < q)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) (v : SchwartzMap (Euc d) ℝ) :
    ∃ φ : SchwartzMap (Euc d) ℝ, ⇑φ = movP d s ρ v := by
  obtain ⟨B, -, hR, -⟩ := mv0_gapref hd hs0 hsd hq hβ hρ
  exact movc3a_P_schwartz_gen (by omega) hs0 hsd ⟨mul_pos hβ hq, hR⟩ v

end HRS.MS.MovC1

end
