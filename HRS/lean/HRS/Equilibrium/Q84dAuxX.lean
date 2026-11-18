/-
# HRS.Equilibrium.Q84dAuxX — packet Q84d: quantitative bound for `h_f` and `a_f`

`|∇f(x) - ∇f(y)| ≤ ‖D²f‖_∞ dist(x,y)` (mean value theorem on the lift) gives
`|h_f(x,y)| ≤ C ‖D²f‖_∞ w(x,y)` and hence `‖a_f‖_∞ ≤ C |f|_K`.
-/
import HRS.Equilibrium.Q84dAuxW

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_fderiv_lift_congr (f : Torus d → ℝ) {u u' : Euc d} (h : Torus.mk u' = Torus.mk u) :
    fderiv ℝ (Torus.lift f) u' = fderiv ℝ (Torus.lift f) u := by
  have hδ : Torus.mk (u' - u) = 0 := by rw [Q84a.q84a_mk_sub, h, sub_self]
  have hshift : (fun z : Euc d => Torus.lift f (z + (u' - u))) = Torus.lift f := by
    funext z
    simp only [Torus.lift, Function.comp, Q84a.q84a_mk_add, hδ, add_zero]
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := Torus.lift f) (u' - u) (x := u)
  rw [hshift] at this
  rw [this]
  congr 1
  abel

/-- `|∇f(x) - ∇f(y)| ≤ D dist(x,y)` when `‖D²f‖ ≤ D`. -/
theorem q84d_grad_lip {f : Torus d → ℝ} (hf : Torus.IsSmooth f) {D : ℝ}
    (hD : ∀ u : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift f) u‖ ≤ D) (x y : Torus d) :
    ‖Torus.grad f x - Torus.grad f y‖ ≤ D * Torus.eucDist x y := by
  obtain ⟨w, hw, hwn⟩ := Q84a.q84a_exists_lift_dist x y
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf
  set F := Torus.lift f with hF
  have h1 : fderiv ℝ F (Torus.rep x) = fderiv ℝ F (Torus.rep y + w) :=
    q84d_fderiv_lift_congr f (by
      rw [Q84a.q84a_mk_add, Torus.mk_rep, hw, Torus.mk_rep]; abel)
  have hdiff : ∀ u ∈ (Set.univ : Set (Euc d)), DifferentiableAt ℝ (fderiv ℝ F) u := fun u _ =>
    ((hc.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)) u
  have hbound : ∀ u ∈ (Set.univ : Set (Euc d)), ‖fderiv ℝ (fderiv ℝ F) u‖ ≤ D := by
    intro u _
    have := hD u
    rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound convex_univ
    (Set.mem_univ (Torus.rep y)) (Set.mem_univ (Torus.rep y + w))
  unfold Torus.grad gradient
  rw [← map_sub, LinearIsometryEquiv.norm_map, h1, ← hwn]
  have : Torus.rep y + w - Torus.rep y = w := by abel
  rw [this] at hmvt
  exact hmvt

section Quant

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
include hd hcrit

theorem q84d_hTransport_quant :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {f : Torus d → ℝ}, Torus.IsSmooth f → ∀ {D : ℝ},
      (∀ u : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift f) u‖ ≤ D) →
      ∀ x y : Torus d, x ≠ y → |hTransport d s f x y| ≤ C₀ * D * wEnv s x y := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hs0 : 0 ≤ s := by linarith
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨Cg, hCg0, hCg⟩ := Q84a.q84a_gg_bound hd hs0 hsd
  refine ⟨2 * Cg * d, by positivity, fun {f} hf {D} hD x y hxy => ?_⟩
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have h1 := q84d_grad_lip hf hD x y
  have h2 := Q84a.q84a_Gb_bound hCg0 (by linarith) hCg hxy
  have hr := PairCorrAux.rTrunc_pos hxy
  have hw1 := PairCorrAux.one_le_wEnv s x y
  have he0 : 0 < Torus.eucDist x y :=
    lt_of_le_of_ne (PairCorrAux.eucDist_nonneg' x y)
      (fun h => hxy ((PairCorrAux.eucDist_eq_zero' x y).1 h.symm))
  have hkey : Torus.eucDist x y * rTrunc x y ^ (-s - 1) ≤ d * wEnv s x y := by
    rcases le_or_gt (Torus.eucDist x y) 1 with h | h
    · have hrt : rTrunc x y = Torus.eucDist x y := by unfold rTrunc; exact min_eq_right h
      have : Torus.eucDist x y * rTrunc x y ^ (-s - 1) = Torus.eucDist x y ^ (-s) := by
        rw [hrt, ← Real.rpow_one_add' he0.le (by linarith)]
        congr 1; ring
      rw [this]
      have h3 := q84d_eucDist_rpow_le_w hs0 hxy
      have hd1 : (1 : ℝ) ≤ d := by linarith
      nlinarith
    · have hrt : rTrunc x y = 1 := by unfold rTrunc; exact min_eq_left h.le
      rw [hrt, Real.one_rpow, mul_one]
      have := Q84a.q84a_eucDist_le (by omega) x y
      nlinarith
  have hn0 := norm_nonneg (periodicRieszGrad d s (x - y))
  calc |hTransport d s f x y|
      = |inner ℝ (Torus.grad f x - Torus.grad f y) (periodicRieszGrad d s (x - y))| := rfl
    _ ≤ ‖Torus.grad f x - Torus.grad f y‖ * ‖periodicRieszGrad d s (x - y)‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ (D * Torus.eucDist x y) * (2 * Cg * rTrunc x y ^ (-s - 1)) :=
        mul_le_mul h1 h2 hn0 (by positivity)
    _ = 2 * Cg * D * (Torus.eucDist x y * rTrunc x y ^ (-s - 1)) := by ring
    _ ≤ 2 * Cg * D * (d * wEnv s x y) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 2 * Cg * d * D * wEnv s x y := by ring

end Quant

theorem q84d_posSeminorm_nonneg (K : ℕ) (f : Torus d → ℝ) : 0 ≤ posSeminorm K f :=
  Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun x => norm_nonneg _

theorem q84d_hess_le_posSeminorm {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (u : Euc d) :
    ‖iteratedFDeriv ℝ 2 (Torus.lift f) u‖ ≤ posSeminorm (8 * d + 80) f := by
  have hc : ContDiff ℝ 2 (Torus.lift f) :=
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from hf).of_le (by norm_cast)
  have hbdd := Torus.bddAbove_norm_iteratedFDeriv_lift 2 f hc
  have h1 : ‖iteratedFDeriv ℝ 2 (Torus.lift f) u‖ ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift f) x‖ :=
    le_ciSup hbdd u
  refine h1.trans ?_
  unfold posSeminorm
  exact Finset.single_le_sum (f := fun j => ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift f) x‖)
    (fun j _ => Real.iSup_nonneg fun x => norm_nonneg _) (by simp)

section ACoef

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
include hd hcrit

/-- **`‖a_f‖_∞ ≤ C |f|_K`.** -/
theorem q84d_aCoef_bound {ρ : Torus d → ℝ} (hρs : SmoothPosDensity ρ) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ {f : Torus d → ℝ}, Torus.IsSmooth f → ∀ x : Torus d,
      |aCoef d s ρ f x| ≤ Ca * posSeminorm (8 * d + 80) f := by
  obtain ⟨C₀, hC₀, hC⟩ := q84d_hTransport_quant hd hcrit (s := s)
  obtain ⟨M₀, hM₀, hM⟩ := q84d_integral_wEnv_mu_le hd hcrit hρs
  refine ⟨C₀ * M₀ / 2, by positivity, fun {f} hf x => ?_⟩
  set D := posSeminorm (8 * d + 80) f with hDdef
  have hD0 : 0 ≤ D := q84d_posSeminorm_nonneg _ f
  have hb := hC hf (q84d_hess_le_posSeminorm hf)
  obtain ⟨hint, hle⟩ := hM x
  have hae : ∀ᵐ y ∂(withDensityReal ρ), ‖hTransport d s f x y‖ ≤ C₀ * D * wEnv s x y := by
    have h0 : ∀ᵐ y ∂(volume : Measure (Torus d)), y ≠ x := by
      rw [ae_iff]; simpa using volume_singleton_torus (by omega) x
    filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le h0] with y hy
    rw [Real.norm_eq_abs]; exact hb x y hy.symm
  have h1 := norm_integral_le_of_norm_le (hint.const_mul (C₀ * D)) hae
  rw [integral_const_mul, Real.norm_eq_abs] at h1
  unfold aCoef
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h2 : C₀ * D * ∫ y, wEnv s x y ∂(withDensityReal ρ) ≤ C₀ * D * M₀ :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  calc 1 / 2 * |∫ y, hTransport d s f x y ∂(withDensityReal ρ)| ≤ 1 / 2 * (C₀ * D * M₀) := by
        gcongr; exact h1.trans h2
    _ = C₀ * M₀ / 2 * D := by ring

omit hd hcrit in
theorem q84d_measurable_aCoef (hsd : s < d) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ)
    {f : Torus d → ℝ} (hf : Torus.IsSmooth f) : Measurable (aCoef d s ρ f) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hhm : Measurable (fun p : Torus d × Torus d => hTransport d s f p.1 p.2) :=
    HRS.LocalDivAux.measurable_hTransport hsd hf
  have : Measurable (fun x : Torus d => ∫ y, hTransport d s f x y ∂(withDensityReal ρ)) :=
    (hhm.stronglyMeasurable.integral_prod_right' (ν := withDensityReal ρ)).measurable
  unfold aCoef
  exact measurable_const.mul this

end ACoef

end HRS.Q84d

end
