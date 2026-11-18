import HRS.MS.WsStatAux7

/-!
# S21 packet E1: the terminal-time derivative of the stationary adjoint orbit

For the stationary coefficient `Cf = fixedViscosityCoeff s (-1) Q nu (s85c s rho) rho` (equal to
`(<s, -1, quadV Q 0, nu>).coeff (fun _ => rho)`, `S85.s85_coeff_fv`) and a Schwartz datum `f`, S5.1 part 2
(`ul_adjoint_orbit_bounds_proof`, with `k = 1`) gives `d/dt U_t L^a f = U_t L^{a+1} f` in `C_b^1` for `a < 3`.  Here:

* `s21_prop_eq_classical`: `propagatorW Cf r t g = u r` for every classical adjoint solution `u` with datum `g`
  (uniqueness, F-CAU through `ulw_unique`);
* `s21_stat_deriv`: for `i : Fin d`, `x`, `t in [0,T]`, `a < 3`: the function
  `tau |-> gradComp i (propagatorW Cf 0 tau (L^a f)) x` has the derivative
  `gradComp i (propagatorW Cf 0 t (L^{a+1} f)) x` within `[0,T]` at `t` (`L = generatorW Cf 0`, iterates `Nat.iterate`).

This is the input of the Duhamel identity of `OscAdjointInput` (packet E3).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S21

open HRS.Whole HRS.MS.Ul HRS.MS.S52B HRS.MS.S85 HRS.MS.UlW
open HRS (Euc)

variable {d : ℕ}

theorem s21_prop_eq_classical (hd : 2 ≤ d) {s ν : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (hν : 0 < ν)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsSymm) {ρ : Euc d → ℝ} (hρ : IsSchwartzDensity ρ)
    (T : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {g : Euc d → ℝ} {u : ℝ → Euc d → ℝ}
    (hu : IsClassicalAdjointW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) t g u) :
    ∀ r ∈ Icc (0 : ℝ) t, propagatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) r t g = u r := by
  rw [← s85_coeff_fv Q hQ ρ] at hu ⊢
  exact ulw_unique hd hs0 hsd (-1) Q hQ 0 hν hρ.1 hρ.2 T ht hu

theorem s21_stat_deriv (hd : 2 ≤ d) {s ν : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (hν : 0 < ν)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsSymm) {ρ : Euc d → ℝ} (hρ : IsSchwartzDensity ρ)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ f : SchwartzMap (Euc d) ℝ, ∀ a : ℕ, a < 3 → ∀ (i : Fin d) (x : Euc d), ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt
        (fun τ => gradComp i (propagatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) 0 τ
          ((fun g y => generatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) 0 g y)^[a] ⇑f)) x)
        (gradComp i (propagatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) 0 t
          ((fun g y => generatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) 0 g y)^[a + 1] ⇑f)) x)
        (Icc 0 T) t := by
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  obtain ⟨k₀, J, H⟩ := ul_adjoint_orbit_bounds_proof hd s hs0 hsd θ hθ 1
  have hk₁ : (1 : ℝ) + (d : ℝ) / 2 < ((k₀ + d + 2 : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg k₀
    have : (d : ℝ) / 2 ≤ d := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    linarith
  obtain ⟨C, hC⟩ := H (k₀ + d + 2) (by omega) (by exact_mod_cast hk₁) T ν Q ρ (s85c s ρ) hT hν hρ
    ⟨fun _ => 0, s85_sigma d, rfl⟩
  intro f a ha3 i x t ht
  obtain ⟨⟨F, hF⟩, hF2⟩ := hC f
  obtain ⟨hbd, hderiv⟩ := hF2 F hF
  set Cf := fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ with hCf
  -- identification of `F b τ` with the propagator
  have eF : ∀ (b : Fin 4), ∀ τ ∈ Icc (0 : ℝ) T,
      F b τ = propagatorW Cf 0 τ ((fun g y => generatorW Cf 0 g y)^[(b : ℕ)] ⇑f) := by
    intro b τ hτ
    obtain ⟨u, hu, hFu⟩ := hF b τ hτ
    have := s21_prop_eq_classical hd hs0 hsd hν Q hQ hρ T hτ hu.classicalSol 0 ⟨le_rfl, hτ.1⟩
    rw [hFu, this]
  have ha4 : a + 1 < 4 := by omega
  have hamem : ∀ τ ∈ Icc (0 : ℝ) T, ∀ b : Fin 4, ContDiff ℝ 1 (F b τ) := by
    intro τ hτ b
    have := (hbd τ hτ).1 b
    exact this.1.of_le (by exact_mod_cast le_rfl)
  -- the derivative of `F a` at `t`
  have key : HasDerivWithinAt (fun τ => gradComp i (F ⟨a, by omega⟩ τ) x)
      (gradComp i (F ⟨a + 1, ha4⟩ t) x) (Icc 0 T) t := by
    rw [hasDerivWithinAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hh⟩ := hderiv ⟨a, by omega⟩ ha3 t ht (ε / 2) (by positivity)
    refine ⟨δ, hδ, fun y hy hyd => ?_⟩
    have hyt : y ≠ t := fun h => hy.2 h
    have hyI : y ∈ Icc (0 : ℝ) T := hy.1
    set h : ℝ := y - t with hhdef
    have hh0 : h ≠ 0 := sub_ne_zero.2 hyt
    have hhabs : |h| < δ := by rw [hhdef]; exact hyd
    have hty : t + h ∈ Icc (0 : ℝ) T := by rw [hhdef]; simpa using hyI
    have hb := hh h hh0 hhabs hty 1 le_rfl x
    set A := F ⟨a, by omega⟩ (t + h) with hA
    set B := F ⟨a, by omega⟩ t with hB
    set Cc := F ⟨a + 1, ha4⟩ t with hCc
    have hAd : Differentiable ℝ A := (hamem (t + h) hty _).differentiable (by norm_num)
    have hBd : Differentiable ℝ B := (hamem t ht _).differentiable (by norm_num)
    have hCd : Differentiable ℝ Cc := (hamem t ht _).differentiable (by norm_num)
    have hD : HasFDerivAt (fun z => h⁻¹ * (A z - B z) - Cc z)
        (h⁻¹ • (fderiv ℝ A x - fderiv ℝ B x) - fderiv ℝ Cc x) x :=
      (((hAd x).hasFDerivAt.sub (hBd x).hasFDerivAt).const_mul h⁻¹).sub (hCd x).hasFDerivAt
    have hnorm : ‖iteratedFDeriv ℝ 1 (fun z => h⁻¹ * (A z - B z) - Cc z) x‖ =
        ‖h⁻¹ • (fderiv ℝ A x - fderiv ℝ B x) - fderiv ℝ Cc x‖ := by
      rw [norm_iteratedFDeriv_one, hD.fderiv]
    set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
    have hne : ‖e‖ ≤ 1 := by simp [he]
    have hcoord : |h⁻¹ * (gradComp i A x - gradComp i B x) - gradComp i Cc x| ≤
        ‖iteratedFDeriv ℝ 1 (fun z => h⁻¹ * (A z - B z) - Cc z) x‖ := by
      have e1 : h⁻¹ * (gradComp i A x - gradComp i B x) - gradComp i Cc x =
          (h⁻¹ • (fderiv ℝ A x - fderiv ℝ B x) - fderiv ℝ Cc x) e := by
        simp only [gradComp, movtr_gradient_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul, ← he]
      rw [e1, hnorm]
      calc |(h⁻¹ • (fderiv ℝ A x - fderiv ℝ B x) - fderiv ℝ Cc x) e|
          = ‖(h⁻¹ • (fderiv ℝ A x - fderiv ℝ B x) - fderiv ℝ Cc x) e‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖h⁻¹ • (fderiv ℝ A x - fderiv ℝ B x) - fderiv ℝ Cc x‖ * ‖e‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖h⁻¹ • (fderiv ℝ A x - fderiv ℝ B x) - fderiv ℝ Cc x‖ * 1 := by
            gcongr
        _ = _ := mul_one _
    have hslope : slope (fun τ => gradComp i (F ⟨a, by omega⟩ τ) x) t y =
        h⁻¹ * (gradComp i A x - gradComp i B x) := by
      rw [slope_def_field]
      simp only [hA, hB, hhdef, add_sub_cancel]
      ring
    rw [Real.dist_eq, hslope]
    calc |h⁻¹ * (gradComp i A x - gradComp i B x) - gradComp i Cc x| ≤
          ‖iteratedFDeriv ℝ 1 (fun z => h⁻¹ * (A z - B z) - Cc z) x‖ := hcoord
      _ ≤ ε / 2 := hb
      _ < ε := by linarith
  -- transfer to the propagator
  have hfun : ∀ τ ∈ Icc (0 : ℝ) T,
      gradComp i (propagatorW Cf 0 τ ((fun g y => generatorW Cf 0 g y)^[a] ⇑f)) x =
        gradComp i (F ⟨a, by omega⟩ τ) x := fun τ hτ => by
    rw [eF ⟨a, by omega⟩ τ hτ]
  have hval : gradComp i (propagatorW Cf 0 t ((fun g y => generatorW Cf 0 g y)^[a + 1] ⇑f)) x =
      gradComp i (F ⟨a + 1, ha4⟩ t) x := by
    rw [eF ⟨a + 1, ha4⟩ t ht]
  rw [hval]
  exact key.congr (fun τ hτ => hfun τ hτ) (hfun t ht)

end HRS.MS.S21
