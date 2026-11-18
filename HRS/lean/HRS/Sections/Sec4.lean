import HRS.PDE.MeanFieldDefs
import HRS.Dynamics.Setup
import HRS.Energy.Modulated
import HRS.Energy.Coercivity

/-!
# HRS.Sections.Sec4 — Proposition 4.17 and the remark after Corollary 4.22

Statement drafts (all proofs are `sorry`) for the rows

* `M:Q:prop:integrated` (Proposition 4.17, TeX M L5009-5017);
* `M:@remark:L5566` (the remark after Corollary 4.22, TeX M L5566-5568).

Representation decisions (to be recorded in `docs/ISSUES.md`):

* `𝓡_N(f) = (√N/2){D_μ(h_f) - E[D_μ(h_f)]}` (M L4914-4918, `Q:eq:normal-form`, with
  `D_μ(h) = N⁻²∑_{i≠j}h(x_i,x_j) - 2μ_N(∫h(·,y)μ(dy)) + μ^{⊗2}(h)`, `Q:eq:deleted-D`) equals
  `√N (F_N^{h_{∇f}}(X_N, μ) - E[F_N^{h_{∇f}}])` because `D_μ(h) = 2F_N^h` (`H:eq:modulated-energy`);
  `h_f(x,y) = (∇f(x)-∇f(y))·∇g(x-y)` (`Q:eq:H-source`, M L4720), which is the existing
  `commKernel (periodicRieszGrad d s) (∇f)` (it differs from the TeX kernel only by the value `0` on the
  diagonal, where `v(x) - v(x) = 0` anyway).  The expectation is the actual
  expectation of the particle law at time `r`.
* "The normalized Fourier features `φ_j` for `B_m`" (M L4990) are `φ_k = ⟨k⟩^{-m} e_k`,
  `e_k = realMode k`, `⟨k⟩ = (1+4π²|k|²)^{1/2} = Lattice.jp k`, so that
  `∑_j |Y(φ_j)|² = ‖Y‖²_{H^{-m}}`; `U_v = e^{v𝒜}` is `PDE.equilibriumSemigroup` for the
  gradient model `PDE.mfData`.
* The expectation of the supremum of an `ℓ²`-sum is an `ℝ≥0∞`-valued `lintegral` of
  `⨆_t ∑'_k ofReal(·²)`, so no junk value of a real `tsum`/`iSup`/Bochner integral enters; the
  well-definedness of the integrals (integrability of the centering and of the time integrand) is
  part of the conclusion.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {d : ℕ}

/-- `𝓡_N(f)` of `Q:eq:normal-form` (M L4914-4918) at the configuration `X_N^r(ω)`:
`√N (F_N^{h_{∇f}}(X_N^r, μ) - E[F_N^{h_{∇f}}(X_N^r, μ)])`, the expectation being the actual
expectation under `P`.  The background measure `μ r` may depend on the time `r`. -/
def centeredCommutatorForcing (d : ℕ) (s : ℝ) {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (μ : ℝ → Measure (Torus d)) (X : ℝ≥0 → Ω → Config d N) (f : Torus d → ℝ)
    (r : ℝ) (ω : Ω) : ℝ :=
  Real.sqrt N *
    (modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) (X r.toNNReal ω) (μ r) -
      ∫ ω', modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) (X r.toNNReal ω') (μ r) ∂P)

/-- The time-integrated centered forcing against the `k`-th feature `φ_k = ⟨k⟩^{-m} e_k`:
`∫_0^b 𝓡_N(U_{b-r} φ_k)(X_N^r) dr` (M L5011), `U = PDE.equilibriumSemigroup D ρβ`. -/
def integratedCenteredForcing {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (D : DynData d)
    (ρβ : Torus d → ℝ) (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) (m : ℝ)
    (k : NonzeroLattice d) (b : ℝ) (ω : Ω) : ℝ :=
  ∫ r in (0 : ℝ)..b,
    centeredCommutatorForcing d D.s P (fun _ => withDensityReal ρβ) X
      (PDE.equilibriumSemigroup D ρβ (b - r) (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x))
      r ω

/-- Proposition 4.17 (`M:Q:prop:integrated`, TeX M L5009-5017; the critical case `s = d/2` of
Section 4.8, M L4442-4448, with `m ≥ 24d+240` as in `H:prop:critical`, M L1048-1051 and L5003):
for each fixed `T > 0` the actual stationary particle law (canonical Gibbs initial law, gradient
dynamics with smooth `V`, `μ = μ_β` the smooth positive thermal density) satisfies
`sup_{a ≥ 0} (E[sup_{0≤t≤T} ∑_j |∫_0^{a+t} 𝓡_N(U_{a+t-r}φ_j)(X_N^r) dr|²])^{1/2} ≤ C_T N^{-1/2}`,
with `C_T` independent of `N`, `a` and the probability space (it depends on
`d, s, β, V, m, T`).  The norm is the continuous-path supremum norm (M L5016); the supremum over `t ∈ [0,T]` is written over
rational `t` (a countable supremum, so the lintegral is a genuine expectation), which is the same quantity by
continuity of the path `t ↦ ∫_0^{a+t}…` in `B_m` (asserted by the source, M L5016, L5090).
Technical hypotheses: `N ≥ 2` (M L418), `d ≥ 2` (standing, M L417; also implied by
`s = d/2 ≥ 1` in the critical regime of Section 4.8), `IsProbabilityMeasure P`, the strong
solution is global (`∀ T'`, as the statement concerns all start times `a ≥ 0`), and `X₀` independent
of the Brownian motions.  Conclusion conjuncts besides the bound (well-definedness): the centering
expectation `E[F_N^{h_f}(X_N^r)]` exists for every smooth `f`, and a.s. the time integrands are
interval integrable.

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): the proof (TeX L5019-5052: Itô's formula L5020-5030; Lyons-Zheng decomposition L4979-4984) applies Itô's formula to `Q_N(U_{b-r}f)(X_N^r)` (`Q:eq:normal-form-path`) and the Lyons-Zheng decomposition of the stationary process, which need a Brownian filtration, so `X` is assumed a filtered strong solution (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`, the strong-solution adaptedness of A.1 that `IsStrongSolution` records only as measurability, ISSUES D1).

Statement repair ME-R1 (ISSUES.md, "ME: request" and its independent review): the probability space is in universe 0 (`Ω : Type`, not `Type*`), as in the proof `HRS.ME.integrated_forcing_type_proof`; the TeX claim has no universe, and the constant is chosen before `Ω`. -/
theorem integrated_forcing (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsVectorBrownian P W →
        ProbabilityTheory.IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P →
        P.map X₀ = canonicalGibbs (periodicRiesz d s) V N β →
        (∀ T' : ℝ, 0 ≤ T' → IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) T' X₀ W X) →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        ∀ a : ℝ, 0 ≤ a →
          (∀ f : Torus d → ℝ, Torus.IsSmooth f → ∀ r : ℝ, 0 ≤ r →
            Integrable (fun ω => modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f))
              (X r.toNNReal ω) (withDensityReal ρβ)) P) ∧
          (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d,
            IntervalIntegrable (fun r =>
              centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X
                (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (a + t - r)
                  (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) r ω)
              volume 0 (a + t)) ∧
          ∫⁻ ω, ⨆ t ∈ {t : ℝ | t ∈ Set.Icc (0 : ℝ) T ∧ ∃ q : ℚ, (q : ℝ) = t}, ∑' k : NonzeroLattice d,
              ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m k
                (a + t) ω ^ 2) ∂P ≤
            ENNReal.ofReal (C ^ 2 / N) := by
  sorry

/-! ### The remark after Corollary 4.22 (bounded positive spectral kernels) -/

/-- Remark after Corollary 4.22 (`M:@remark:L5566`, TeX M L5566-5568), first claim: "A bounded
potential need not have a Lipschitz force.  For example, the Fourier regularity supplied by
`O:eq:negative-symbol` does not make `∇γ` bounded for every `-1 < s < 0`": for the bounded kernel
`g = negSpectralKernel d s c` (`ĝ(k) = c(2π|k|)^{s-d}`, `c > 0`) with `-1 < s < 0`, the gradient
is unbounded near the origin: for every `C` there is `x ≠ 0` at which `g` is differentiable and
`‖∇g(x)‖ > C`.  Technical hypothesis: `1 ≤ d` (standing, `O:sec:negative`, M L5501). -/
theorem negSpectral_grad_unbounded (hd : 1 ≤ d) {s c : ℝ} (hs1 : -1 < s) (hs0 : s < 0)
    (hc : 0 < c) :
    ∀ C : ℝ, ∃ x : Torus d, x ≠ 0 ∧
      DifferentiableAt ℝ (Torus.lift (negSpectralKernel d s c)) (Torus.rep x) ∧
      C < ‖Torus.grad (negSpectralKernel d s c) x‖ := by
  sorry

/-! #### Auxiliary lemmas for the Hessian remark after Corollary 4.22 (Q17) -/

namespace NegHess

open MeasureTheory Filter Topology

variable {d : ℕ}

theorem abs_coord_le_enorm (k : Lattice d) (i : Fin d) : |(k i : ℝ)| ≤ Lattice.enorm k := by
  unfold Lattice.enorm
  rw [EuclideanSpace.norm_eq]
  refine Real.abs_le_sqrt ?_
  have h1 : (k i : ℝ) ^ 2 ≤ ∑ j, (k j : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun j => (k j : ℝ) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  simpa [Lattice.toEuc, Real.norm_eq_abs, sq_abs] using h1

theorem summable_coeff_pow {s c : ℝ} (hs : s < -2) (hc : 0 < c) (n : ℕ) (hn : n ≤ 2) :
    Summable (fun k : Lattice d => |negSpectralCoeff d s c k| * (2 * Real.pi * Lattice.enorm k) ^ n) := by
  have hn' : (n : ℝ) ≤ 2 := by exact_mod_cast hn
  have hdn : s - (d : ℝ) + n < -(d : ℝ) := by linarith
  have hnz : Summable (fun k : NonzeroLattice d =>
      |negSpectralCoeff d s c k.1| * (2 * Real.pi * Lattice.enorm k.1) ^ n) := by
    refine ((summable_enorm_rpow_aux (d := d) (s - (d : ℝ) + n) hdn).mul_left
      (c * (2 * Real.pi) ^ (s - (d : ℝ) + n))).congr (fun k => ?_)
    symm
    have hk : k.1 ≠ 0 := k.2
    have hpos : 0 < Lattice.enorm k.1 := lt_of_lt_of_le one_pos (one_le_enorm k.1 hk)
    unfold negSpectralCoeff
    rw [if_neg hk, abs_of_nonneg (mul_nonneg hc.le (Real.rpow_nonneg (by positivity) _))]
    have hX : (0 : ℝ) < 2 * Real.pi * Lattice.enorm k.1 := by positivity
    have e1 : (2 * Real.pi * Lattice.enorm k.1) ^ (s - (d : ℝ)) *
        (2 * Real.pi * Lattice.enorm k.1) ^ n = (2 * Real.pi * Lattice.enorm k.1) ^ (s - (d : ℝ) + n) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hX]
    have e2 : (2 * Real.pi * Lattice.enorm k.1) ^ (s - (d : ℝ) + n) =
        (2 * Real.pi) ^ (s - (d : ℝ) + n) * Lattice.enorm k.1 ^ (s - (d : ℝ) + n) :=
      Real.mul_rpow (by positivity) hpos.le
    calc c * (2 * Real.pi * Lattice.enorm k.1) ^ (s - (d : ℝ)) * (2 * Real.pi * Lattice.enorm k.1) ^ n
        = c * ((2 * Real.pi * Lattice.enorm k.1) ^ (s - (d : ℝ)) *
            (2 * Real.pi * Lattice.enorm k.1) ^ n) := by ring
      _ = c * (2 * Real.pi * Lattice.enorm k.1) ^ (s - (d : ℝ) + n) := by rw [e1]
      _ = c * (2 * Real.pi) ^ (s - (d : ℝ) + n) * Lattice.enorm k.1 ^ (s - (d : ℝ) + n) := by
          rw [e2]; ring
  exact (Function.Injective.summable_iff (g := fun k : NonzeroLattice d => k.1) Subtype.val_injective
    (fun k hk => by
      have : k = 0 := by
        by_contra h
        exact hk ⟨⟨k, h⟩, rfl⟩
      simp [this, negSpectralCoeff])).mp hnz

/-- The gradient of a function on the torus, through the lift (periodicity). -/
theorem grad_mk_aux (φ : Torus d → ℝ) (y : Euc d) :
    Torus.grad φ (Torus.mk y) = gradient (Torus.lift φ) y := by
  obtain ⟨n, hn⟩ := Torus.rep_mk y
  unfold Torus.grad
  rw [hn]
  have hper : (fun x => Torus.lift φ (x + Lattice.toEuc n)) = Torus.lift φ :=
    funext fun x => Torus.lift_periodic φ x n
  unfold gradient
  rw [← fderiv_comp_add_right (Lattice.toEuc n) (f := Torus.lift φ) (x := y), hper]

end NegHess

/-- Remark after Corollary 4.22 (`M:@remark:L5566`, TeX M L5566-5568), second claim: "For
`s < -2`, the Fourier series of `∇²γ` is absolutely summable and the ordinary globally Lipschitz
drift realization is available": for `g = negSpectralKernel d s c` with `s < -2` and `c > 0`, the
Fourier coefficients `-(2π)² k_i k_j ĝ(k)` of `∂_i∂_j g` are absolutely summable, `g` is `C²`, and
`∇g` is globally Lipschitz on the lift `ℝ^d` (the last two conjuncts are the formal content of "the
ordinary globally Lipschitz drift realization is available").  Technical hypothesis: `1 ≤ d`
(`O:sec:negative`, M L5501). -/
theorem negSpectral_hessian_summable (hd : 1 ≤ d) {s c : ℝ} (hs : s < -2) (hc : 0 < c) :
    (∀ i j : Fin d, Summable fun k : NonzeroLattice d =>
      |(2 * Real.pi) ^ 2 * (k.1 i : ℝ) * (k.1 j : ℝ) * negSpectralCoeff d s c k.1|) ∧
    Torus.IsCk 2 (negSpectralKernel d s c) ∧
    ∃ K : ℝ≥0, LipschitzWith K (fun y : Euc d => Torus.grad (negSpectralKernel d s c) (Torus.mk y)) := by
  have hlift : Torus.lift (negSpectralKernel d s c) = fun x : Euc d =>
      ∑' k : Lattice d, negSpectralCoeff d s c k * Torus.cosMode k (Torus.mk x) := rfl
  have hcos : ∀ k : Lattice d, (fun x : Euc d => negSpectralCoeff d s c k * Torus.cosMode k (Torus.mk x)) =
      (fun u : ℝ => negSpectralCoeff d s c k * Real.cos u) ∘ Torus.freqFunctional k := by
    intro k
    funext x
    simp [Torus.cosMode_mk, Torus.freqFunctional_apply]
  have hfc : ∀ k : Lattice d, ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞)
      (fun x : Euc d => negSpectralCoeff d s c k * Torus.cosMode k (Torus.mk x)) := by
    intro k
    rw [hcos k]
    exact (contDiff_const.mul Real.contDiff_cos).comp (Torus.freqFunctional k).contDiff
  have hbound : ∀ n : ℕ, n ≤ 2 → ∀ (k : Lattice d) (x : Euc d),
      ‖iteratedFDeriv ℝ n (fun x : Euc d => negSpectralCoeff d s c k * Torus.cosMode k (Torus.mk x)) x‖ ≤
        |negSpectralCoeff d s c k| * (2 * Real.pi * Lattice.enorm k) ^ n := by
    intro n _ k x
    rw [hcos k]
    have hcd : ContDiff ℝ ⊤ (fun u : ℝ => negSpectralCoeff d s c k * Real.cos u) :=
      contDiff_const.mul Real.contDiff_cos
    refine (Torus.norm_iteratedFDeriv_comp_functional (fun u : ℝ => negSpectralCoeff d s c k * Real.cos u)
      hcd |negSpectralCoeff d s c k| (fun i t => KernelAux.norm_iteratedFDeriv_c_cos _ i t) _ n x).trans ?_
    have h1 : ‖Torus.freqFunctional k‖ ^ n ≤ (2 * Real.pi * Lattice.enorm k) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) (Torus.norm_freqFunctional_le k) n
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hv : ∀ n : ℕ, n ≤ 2 → Summable (fun k : Lattice d =>
      |negSpectralCoeff d s c k| * (2 * Real.pi * Lattice.enorm k) ^ n) :=
    fun n hn => NegHess.summable_coeff_pow hs hc n hn
  have hC2 : Torus.IsCk 2 (negSpectralKernel d s c) := by
    unfold Torus.IsCk
    rw [hlift]
    exact contDiff_tsum (v := fun n k => |negSpectralCoeff d s c k| * (2 * Real.pi * Lattice.enorm k) ^ n)
      (fun k => hfc k) (fun n hn => hv n (by exact_mod_cast hn))
      (fun n k x hn => hbound n (by exact_mod_cast hn) k x)
  refine ⟨?_, hC2, ?_⟩
  · intro i j
    have hsum := (NegHess.summable_coeff_pow hs hc 2 le_rfl).comp_injective
      (Subtype.val_injective (p := fun k : Lattice d => k ≠ 0))
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hsum
    have hk1 := NegHess.abs_coord_le_enorm k.1 i
    have hk2 := NegHess.abs_coord_le_enorm k.1 j
    have hprod : |(k.1 i : ℝ)| * |(k.1 j : ℝ)| ≤ Lattice.enorm k.1 * Lattice.enorm k.1 :=
      mul_le_mul hk1 hk2 (abs_nonneg _) (norm_nonneg _)
    have h2π : |(2 * Real.pi) ^ 2| = (2 * Real.pi) ^ 2 := abs_of_nonneg (by positivity)
    show |(2 * Real.pi) ^ 2 * (k.1 i : ℝ) * (k.1 j : ℝ) * negSpectralCoeff d s c k.1| ≤
      |negSpectralCoeff d s c k.1| * (2 * Real.pi * Lattice.enorm k.1) ^ 2
    rw [abs_mul, abs_mul, abs_mul, h2π]
    calc (2 * Real.pi) ^ 2 * |(k.1 i : ℝ)| * |(k.1 j : ℝ)| * |negSpectralCoeff d s c k.1|
        = ((2 * Real.pi) ^ 2 * (|(k.1 i : ℝ)| * |(k.1 j : ℝ)|)) * |negSpectralCoeff d s c k.1| := by ring
      _ ≤ ((2 * Real.pi) ^ 2 * (Lattice.enorm k.1 * Lattice.enorm k.1)) *
            |negSpectralCoeff d s c k.1| := by gcongr
      _ = |negSpectralCoeff d s c k.1| * (2 * Real.pi * Lattice.enorm k.1) ^ 2 := by ring
  · have hF : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (Torus.lift (negSpectralKernel d s c)) := hC2
    have hfd : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fderiv ℝ (Torus.lift (negSpectralKernel d s c))) :=
      hF.fderiv_right (by norm_num)
    have hfdd : Differentiable ℝ (fderiv ℝ (Torus.lift (negSpectralKernel d s c))) :=
      hfd.differentiable (by norm_num)
    let L : StrongDual ℝ (Euc d) →L[ℝ] Euc d :=
      (InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hL1 : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
      simp [L])
    have hGd : ∀ y : Euc d, HasFDerivAt (fun y => L (fderiv ℝ (Torus.lift (negSpectralKernel d s c)) y))
        (L.comp (fderiv ℝ (fderiv ℝ (Torus.lift (negSpectralKernel d s c))) y)) y :=
      fun y => L.hasFDerivAt.comp y (hfdd y).hasFDerivAt
    have hGdiff : Differentiable ℝ (fun y => L (fderiv ℝ (Torus.lift (negSpectralKernel d s c)) y)) :=
      fun y => (hGd y).differentiableAt
    set B : ℝ := ∑' k : Lattice d, |negSpectralCoeff d s c k| * (2 * Real.pi * Lattice.enorm k) ^ 2
      with hBdef
    have hB0 : 0 ≤ B := tsum_nonneg fun k => mul_nonneg (abs_nonneg _)
      (pow_nonneg (mul_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) (norm_nonneg _)) _)
    have hderiv_le : ∀ y : Euc d,
        ‖fderiv ℝ (fun y => L (fderiv ℝ (Torus.lift (negSpectralKernel d s c)) y)) y‖ ≤ B := by
      intro y
      rw [(hGd y).fderiv]
      have e2 : ‖fderiv ℝ (fderiv ℝ (Torus.lift (negSpectralKernel d s c))) y‖ =
          ‖iteratedFDeriv ℝ 2 (Torus.lift (negSpectralKernel d s c)) y‖ := by
        rw [← norm_iteratedFDeriv_one]
        exact norm_iteratedFDeriv_fderiv
      have hsumn : Summable (fun k : Lattice d =>
          ‖iteratedFDeriv ℝ 2 (fun x : Euc d => negSpectralCoeff d s c k * Torus.cosMode k (Torus.mk x)) y‖) :=
        Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hbound 2 le_rfl k y) (hv 2 le_rfl)
      calc ‖L.comp (fderiv ℝ (fderiv ℝ (Torus.lift (negSpectralKernel d s c))) y)‖
          ≤ ‖L‖ * ‖fderiv ℝ (fderiv ℝ (Torus.lift (negSpectralKernel d s c))) y‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * ‖fderiv ℝ (fderiv ℝ (Torus.lift (negSpectralKernel d s c))) y‖ := by gcongr
        _ = ‖iteratedFDeriv ℝ 2 (Torus.lift (negSpectralKernel d s c)) y‖ := by rw [one_mul, e2]
        _ = ‖∑' k : Lattice d,
              iteratedFDeriv ℝ 2 (fun x : Euc d => negSpectralCoeff d s c k * Torus.cosMode k (Torus.mk x)) y‖ := by
            rw [hlift, iteratedFDeriv_tsum_apply (N := (2 : ℕ∞)) (fun k => hfc k)
              (fun n hn => hv n (by exact_mod_cast hn)) (fun n k x hn => hbound n (by exact_mod_cast hn) k x)
              le_rfl y]
        _ ≤ ∑' k : Lattice d, ‖iteratedFDeriv ℝ 2
              (fun x : Euc d => negSpectralCoeff d s c k * Torus.cosMode k (Torus.mk x)) y‖ :=
            norm_tsum_le_tsum_norm hsumn
        _ ≤ ∑' k : Lattice d, |negSpectralCoeff d s c k| * (2 * Real.pi * Lattice.enorm k) ^ 2 :=
            Summable.tsum_le_tsum (fun k => hbound 2 le_rfl k y) hsumn (hv 2 le_rfl)
        _ = B := rfl
    refine ⟨B.toNNReal, ?_⟩
    have e : (fun y : Euc d => Torus.grad (negSpectralKernel d s c) (Torus.mk y)) =
        fun y => L (fderiv ℝ (Torus.lift (negSpectralKernel d s c)) y) :=
      funext fun y => NegHess.grad_mk_aux _ y
    rw [e]
    refine lipschitzWith_of_nnnorm_fderiv_le hGdiff (fun y => ?_)
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hB0]
    exact hderiv_le y

end HRS
