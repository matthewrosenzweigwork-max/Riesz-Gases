import HRS.Whole.Bias
import HRS.MS.WrStatic
import HRS.MS.WrCavAux2
import HRS.MS.WrPoleAux3
import HRS.MS.WrInsAux2

/-!
# HRS.MS.StaticInput -- assembly of S7.2 `static_input` and `static_input_uniform_beta`

Helper prefix `si_`, namespace `HRS.MS.Wr`.  The statements are exactly the frozen
`HRS.Whole.static_input_uniform_beta` and `HRS.Whole.static_input` (no adjustment).  The constant is the
maximum of the constants of the five conjuncts of `HRS.Whole.StaticInputConclusion`:

* (1) `GibbsWellDefined`: `euclidean_pressure_proof` at `L = 0`, `B = 0`, `θ = 0`, `b⁺ := β⁺ + 1` (no constant);
* (2) `HasMarginalDensityBounds`: `wr13d_marginal_density_bounds`;
* (3) linear variance: `wr14b_linear`;
* (4) pole bundle: `wr13a_pole_bundle` (`β ∈ [0, β⁺]`) for `CavityWellDefined` and the two density bounds,
  `wr13b_pole_variance_clause` (`β ∈ (0, β⁺]`) for the pole variance;
* (5) cavity TV: `wr13c2_cavity_tv` (`β ∈ [β⁻, β⁺]`, `β⁻ > 0`).

`static_input` is the case `β⁻ = β⁺ = β`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.Wr

variable {d : ℕ} {s : ℝ}

/-- **Proposition S7.2, uniform in `β`**. -/
theorem static_input_uniform_beta_proof : type_of% @HRS.Whole.static_input_uniform_beta := by
  intro d s hd hs hsd βm βp M hβm hβ
  have hs0 : 0 < s := by
    have : (1 : ℝ) ≤ (d : ℝ) / 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    linarith
  have hβp0 : 0 ≤ βp := hβm.le.trans hβ
  obtain ⟨C1, h1⟩ := wr14b_linear hd hs0 hsd hβm hβ M
  obtain ⟨C2, h2⟩ := wr13d_marginal_density_bounds hd hs0 hsd hβm hβ M
  obtain ⟨C3, hC31, h3⟩ := wr13a_pole_bundle hd hs0 hsd hβp0 M
  obtain ⟨C4, hC40, h4⟩ := wr13b_pole_variance_clause hd hs0 hsd βp M
  obtain ⟨C5, hC50, h5⟩ := wr13c2_cavity_tv hd hs0 hsd hβm βp M
  obtain ⟨θ0, hθ0, C0, hP⟩ := euclidean_pressure_proof hd hs0.le hsd M 0 βm (βp + 1) 0 hβm
    (by linarith)
  have hB0 : HRS.Whole.IsBoundedPairKernel s 0 (fun _ _ : Euc d => (0 : ℝ)) :=
    ⟨measurable_const, fun _ _ => rfl, fun x y _ => by simp⟩
  set C : ℝ := max C1 (max C2 (max C3 (max C4 C5))) with hCdef
  have hC1 : C1 ≤ C := le_max_left _ _
  have hC2 : C2 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : C3 ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC4 : C4 ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hC5 : C5 ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨C, fun ρ hρ hM β hβmem N hN => ?_⟩
  obtain ⟨hβ1, hβ2⟩ := hβmem
  have hβpos : 0 < β := hβm.trans_le hβ1
  have hδ : 0 ≤ deltaN d s N := HRS.deltaN_nonneg s (by omega)
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hmeas3, hle3, hpole3⟩ := h3 ρ hρ hM β hβpos.le hβ2 N hN
  unfold HRS.Whole.StaticInputConclusion
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := (hP ρ hρ hM (fun h => absurd h hs0.ne') (fun _ _ => 0) hB0 N hN β
      ⟨hβ1, hβ2.trans (by linarith)⟩ 0 (by simpa using hθ0.le)).1
    have e : (fun x y : Euc d => HRS.Whole.rieszKernel d s (x - y) - 0 * (fun _ _ : Euc d => (0 : ℝ)) x y) =
        fun x y => HRS.Whole.rieszKernel d s (x - y) := by
      funext x y
      simp
    rwa [e] at this
  · exact wr14b_hmdb_mono (h2 ρ hρ hM β ⟨hβ1, hβ2⟩ N hN) hC2 (by gcongr)
  · intro f hf
    refine (h1 ρ hρ hM β ⟨hβ1, hβ2⟩ N hN f hf).trans (ENNReal.ofReal_le_ofReal ?_)
    have hI : 0 ≤ ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) := integral_nonneg fun x => sq_nonneg _
    gcongr
  · intro x t ht
    obtain ⟨hcwd, hfirst, hsecond⟩ := hpole3 x t ht
    refine ⟨hcwd, ?_, ?_, ?_⟩
    · refine hfirst.trans (withDensity_mono (Filter.Eventually.of_forall fun y => ?_))
      exact ENNReal.ofReal_le_ofReal (by gcongr)
    · intro h3N
      refine (hsecond h3N).trans (withDensity_mono (Filter.Eventually.of_forall fun yz => ?_))
      exact ENNReal.ofReal_le_ofReal (by gcongr)
    · intro f hf hint
      refine (h4 ρ hρ hM β hβpos hβ2 N hN x t ht f hf hint).trans (ENNReal.ofReal_le_ofReal ?_)
      have hI : 0 ≤ ∫ y, |f y| ^ 2 * Real.exp (-(t * (β / N)) * HRS.Whole.rieszKernel d s (x - y))
          ∂(HRS.Whole.withDensityReal ρ) :=
        integral_nonneg fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
      have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by
        have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
        linarith
      gcongr
  · refine (h5 ρ hρ hM β hβ1 hβ2 N hN).trans ?_
    exact mul_le_mul_of_nonneg_right hC5 (Real.sqrt_nonneg _)

/-- **Proposition S7.2**: the case `β⁻ = β⁺ = β` of the uniform version. -/
theorem static_input_proof : type_of% @HRS.Whole.static_input := by
  intro d s hd hs hsd β M hβ
  obtain ⟨C, hC⟩ := static_input_uniform_beta_proof hd hs hsd β β M hβ le_rfl
  exact ⟨C, fun ρ hρ hM N hN => hC ρ hρ hM β ⟨le_rfl, le_rfl⟩ N hN⟩

end HRS.MS.Wr
