import HRS.Whole.Static
import HRS.MS.WrStaticAux1
import HRS.MS.WrPress
import HRS.MS.WrMargBAux2
import HRS.MS.WrQuadAux3
import HRS.MS.Comm

/-!
# HRS.MS.WrStatic -- assembly of `euc_static` and `euc_static_commutator` (WR-14b)

Packet WR-14b of `docs/WR_B_PLAN.md` (T12), namespace `HRS.MS.Wr`, helper prefix `wr14b_`.  The statements are
exactly the frozen `HRS.Whole.euc_static` and `HRS.Whole.euc_static_commutator` (no adjustment).

* `euc_static_proof : type_of% @HRS.Whole.euc_static`.  The constant is the maximum of the constants of
  - conjunct 1 `GibbsWellDefined`: `euclidean_pressure_proof` at `h = 0`, `B = 0`, `θ = 0`, `b⁺ := β⁺ + 1`
    (no constant);
  - conjunct 2 (linear variance): `wr14b_linear` (`euc_linear_variance` for `N ≥ N₀`, the crude density bound
    `Q ≤ e^{β N M_g} μ^{⊗N}` for `2 ≤ N < N₀`);
  - conjunct 3 (`HasMarginalDensityBounds`): `wr13d_marginal_density_bounds`;
  - conjunct 4 (`QuadraticVarianceBound` for `ν = μ`, `ν = π_N`): `wr14a_quadratic_variance_bound`.
* `euc_static_commutator_proof : type_of% @HRS.Whole.euc_static_commutator`: conjunct 4 with `B = sΛ`,
  `h = commutatorKernel d s v` (`commutatorKernel_isBounded_proof`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.Wr

variable {d : ℕ} {s : ℝ}

/-- Monotonicity of `HasMarginalDensityBounds` in both constants. -/
theorem wr14b_hmdb_mono {π μ : Measure (Euc d)} {C C' r r' : ℝ}
    (H : HRS.Whole.HasMarginalDensityBounds π μ C r) (hC : C ≤ C') (hr : r ≤ r') :
    HRS.Whole.HasMarginalDensityBounds π μ C' r' := by
  obtain ⟨φ, hφm, hφeq, hφb, hφ2, hφn⟩ := H
  exact ⟨φ, hφm, hφeq, fun x => ⟨(hφb x).1, (hφb x).2.trans hC⟩, hφ2, hφn.trans hr⟩

/-- **Proposition S3.3 (`W:prop:euc-static`)**. -/
theorem euc_static_proof : type_of% @HRS.Whole.euc_static := by
  intro d s hd hs0 hsd βm βp M hβm hβ
  obtain ⟨C2, h2⟩ := wr14b_linear hd hs0 hsd hβm hβ M
  obtain ⟨C3, h3⟩ := wr13d_marginal_density_bounds hd hs0 hsd hβm hβ M
  obtain ⟨C4, h4⟩ := wr14a_quadratic_variance_bound hd hs0 hsd hβm hβ M
  obtain ⟨θ0, hθ0, C0, hP⟩ := euclidean_pressure_proof hd hs0.le hsd M 0 βm (βp + 1) 0 hβm
    (by linarith)
  have hB0 : HRS.Whole.IsBoundedPairKernel s 0 (fun _ _ : Euc d => (0 : ℝ)) :=
    ⟨measurable_const, fun _ _ => rfl, fun x y _ => by simp⟩
  refine ⟨max C2 (max C3 C4), fun ρ hρ hM β hβmem N hN => ?_⟩
  have hδ : 0 ≤ deltaN d s N := HRS.deltaN_nonneg s (by omega)
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hC2 : C2 ≤ max C2 (max C3 C4) := le_max_left _ _
  have hC3 : C3 ≤ max C2 (max C3 C4) := (le_max_left _ _).trans (le_max_right _ _)
  have hC4 : C4 ≤ max C2 (max C3 C4) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (hP ρ hρ hM (fun h => absurd h hs0.ne') (fun _ _ => 0) hB0 N hN β
      ⟨hβmem.1, hβmem.2.trans (by linarith)⟩ 0 (by simpa using hθ0.le)).1
    have e : (fun x y : Euc d => HRS.Whole.rieszKernel d s (x - y) - 0 * (fun _ _ : Euc d => (0 : ℝ)) x y) =
        fun x y => HRS.Whole.rieszKernel d s (x - y) := by
      funext x y
      simp
    rwa [e] at this
  · intro f hf
    refine (h2 ρ hρ hM β hβmem N hN f hf).trans (ENNReal.ofReal_le_ofReal ?_)
    have hI : 0 ≤ ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) := integral_nonneg fun x => sq_nonneg _
    gcongr
  · exact wr14b_hmdb_mono (h3 ρ hρ hM β hβmem N hN) hC3 (by gcongr)
  · intro B h hBK
    obtain ⟨h4a, h4b⟩ := h4 hρ hM hβmem hN B h hBK
    exact ⟨wr14a_qvb_mono (by gcongr) h4a, wr14a_qvb_mono (by gcongr) h4b⟩

/-- **Proposition S3.3, commutator clause**. -/
theorem euc_static_commutator_proof : type_of% @HRS.Whole.euc_static_commutator := by
  intro d s hd hs0 hsd βm βp M hβm hβ
  obtain ⟨C4, h4⟩ := wr14a_quadratic_variance_bound hd hs0 hsd hβm hβ M
  refine ⟨C4, fun ρ hρ hM β hβmem N hN Λ v hv => ?_⟩
  exact h4 hρ hM hβmem hN (s * Λ) (HRS.Whole.commutatorKernel d s v)
    (HRS.MS.Comm.commutatorKernel_isBounded_proof hs0 Λ v hv)

end HRS.MS.Wr
