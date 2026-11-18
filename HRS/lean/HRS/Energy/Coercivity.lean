import HRS.Kernel.GradBasic
import HRS.PDE.Fourier

/-!
# Commutator estimates, coercivity and dynamical modulated-energy bounds (package ENER-02)

Source: HRS periodic main paper, Section 3.5 `B:sec:blackbox` (source lines 2800-3281):
* `B:eq:commutator-quantity` (2815-2820): `Comm_N(v; X_N, μ)`.
* Proposition 3.32 `M:B:prop:commutator` (2824-2836), external: Chodron de Courcel–Rosenzweig–
  Serfaty, Prop. 2.13 (`s ≥ d-2`) and Hess-Childs–Rosenzweig, Thm. 1.1 & Rem. 1.3 (`s < d-2`).
* Proposition 3.33 `M:B:prop:coercivity` (2842-2852).
* Proposition 3.34 `M:B:prop:hrs-periodic-coercivity` (2865-2898).
* Remark 3.35 `M:B:rem:hrs-coercivity-fixed-density` (3056-3066).
* Proposition 3.36 `M:B:prop:gronwall-catalog` (3078-3111).
* Proposition 3.37 `M:B:prop:lowtemp` (3113-3124).
* Proposition 3.38 `M:B:prop:comparison-kernel-identity` (3155-3167).
* Remark 3.39 `M:B:rem:MF-truncated` (3177-3194).
* Proposition 3.41 `M:B:prop:mfe-uniform` (3204-3217).
* Remarks 3.40, 3.42, 3.43, 3.44, 3.45: no formal content (see `coverage.tsv`).
* The transport seminorm `‖v‖_*` is `B:eq:comm-norm` (10163).

## Representation decisions (recorded in `docs/ISSUES.md` §B, ENER-02)

* **Density bounds.** `‖μ‖_∞ ≤ Λ` is stated for the chosen density representative `ρ` as a
  pointwise bound `∀ x, ρ x ≤ Λ` (an `L^∞` bound always has such a representative); `μ = ρ dx`
  through `withDensityReal`.  The smearing scale is `λ = (NΛ)^{-1/d}` (`smearScale`), as in
  Proposition 3.34; the condition `λ < 1` is automatic for `N ≥ 2`, `Λ ≥ 1`.
* **The correction `o_N`.** All statements use the exact correction of Proposition 3.34,
  `o_N(Λ) = 1_{s=0} log(NΛ)/(2dN) + C₀ Λ^{s/d} N^{s/d-1}` (`oNΛ`,
  `B:eq:hrs-coercivity-exact-correction`); Remark 3.35 relates it to `oN` of
  `H:eq:energy-completion` (`HRS.oN`), which has the same logarithmic coefficient and absorbs the
  `Λ`-dependence into `C₀`.
* **`‖∇v‖_{L^∞}` for Lipschitz `v`** is the Lipschitz constant with respect to the torus distance
  (`IsLipschitzVF`), which equals the essential supremum of `|∇v|`; statements quantify over all
  admissible constants.  The fractional part of `‖v‖_*` is represented through a function `w`
  with the Fourier coefficients of `|∇|^{(d+1)/2} v` (`IsFracDeriv`) and its `L^{2d/(d-1)}` norm
  (`eLpNorm`, in `ℝ≥0∞`); `HasTransportBound d s v K` says `‖v‖_* ≤ K`.  This avoids `tsum`
  junk values for non-summable Fourier series.
* **Off-diagonal integrals** against `(μ_N - μ)^{⊗2}` are written out term by term with the
  diagonal deleted explicitly (`if x = y then 0 else …`), as `interactionPairing` does; the
  source asserts absolute convergence (lines 2820-2821), and Proposition 3.32 asserts it in its
  conclusion so that no Bochner integral is a junk value.
* **The modulated free energy `𝖤_N(f,μ)` and the normalised relative entropy `𝖧_N`** are used
  in Propositions 3.36(C2) and 3.41 without a definition in the main paper (see ISSUES §C); they
  are fixed here as `𝖧_N(f|Q) = N⁻¹ H(f|Q)` and
  `𝖤_N(f,μ) = β⁻¹ 𝖧_N(f | μ^{⊗N}) + ∫ F_N(X_N, μ) f(dX_N)`, the only reading consistent with
  lines 3230-3234 and 3102.  Finiteness is a separate predicate (`MFEFinite`), asserted in the
  conclusions.
* **Expectations of energies** are stated as `lintegral`s of `ENNReal.ofReal (F_N + o_N)`
  (nonnegative by coercivity) on the left and Bochner integrals with an explicit integrability
  hypothesis at time `0` on the right, so that finiteness is part of the claim.
* **Proposition 3.38** is stated in integrated form `E F^t - E F^0 = ∫_0^t (…) dr` (the content of
  the `d/dt` identity obtained from Itô's formula), with the integrability of the microscopic
  term as a hypothesis (the source presupposes the displayed expectations exist).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ### Corrections, scales and seminorms -/

/-- The exact correction `o_N(Λ) = 1_{s=0} log(NΛ)/(2dN) + C₀ Λ^{s/d} N^{s/d-1}`
(`B:eq:hrs-coercivity-exact-correction`, source lines 2884-2887). -/
def oNΛ (d : ℕ) (s C₀ Λ : ℝ) (N : ℕ) : ℝ :=
  (if s = 0 then Real.log (N * Λ) / (2 * d * N) else 0) +
    C₀ * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)

/-- `a_N^Λ = Λ^{s/d} N^{s/d-1}` (`B:eq:hrs-coercivity-correction`, line 2881). -/
def aNΛ (d : ℕ) (s Λ : ℝ) (N : ℕ) : ℝ := Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)

/-- `a_N = (1 + 1_{s=0} log N) N^{s/d-1}` (Remark 3.35, line 3060). -/
def aN (d : ℕ) (s : ℝ) (N : ℕ) : ℝ :=
  (1 + if s = 0 then Real.log N else 0) * (N : ℝ) ^ (s / d - 1)

/-- The smearing scale `λ = (NΛ)^{-1/d}` (lines 2826, 2844, 2881). -/
def smearScale (d : ℕ) (N : ℕ) (Λ : ℝ) : ℝ := (N * Λ) ^ (-(1 : ℝ) / d)

/-- A Lipschitz vector field with constant `L` (so `‖∇v‖_{L^∞} ≤ L`), with respect to the
Euclidean torus distance `tdist`. -/
def IsLipschitzVF (L : ℝ) (v : Torus d → Euc d) : Prop :=
  ∀ x y, ‖v x - v y‖ ≤ L * KernelGrad.tdist x y

/-- `w = |∇|^a v` componentwise: `ŵ_j(k) = (2π|k|)^a v̂_j(k)` for all `k ∈ ℤ^d`. -/
def IsFracDeriv (a : ℝ) (v w : Torus d → Euc d) : Prop :=
  ∀ (j : Fin d) (k : Lattice d),
    Torus.fcoef (fun x => w x j) k = ((2 * Real.pi * Lattice.enorm k) ^ a : ℝ) * Torus.fcoef (fun x => v x j) k

/-- `‖v‖_* ≤ K` for the transport seminorm `B:eq:comm-norm` (source line 10163):
`‖v‖_* = ‖∇v‖_{L^∞} + 1_{s<d-2} ‖|∇|^{(d+1)/2} v‖_{L^{2d/(d-1)}}`. -/
def HasTransportBound (d : ℕ) (s : ℝ) (v : Torus d → Euc d) (K : ℝ) : Prop :=
  ∃ L F : ℝ, 0 ≤ L ∧ 0 ≤ F ∧ IsLipschitzVF L v ∧
    (s < d - 2 → ∃ w : Torus d → Euc d, IsFracDeriv (((d : ℝ) + 1) / 2) v w ∧
      eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ≤ ENNReal.ofReal F) ∧
    L + (if s < d - 2 then F else 0) ≤ K

/-- The squared homogeneous Sobolev seminorm `‖ψ‖²_{Ḣ^a(𝕋^d)} = ∑_{k≠0} (2π|k|)^{2a} |ψ̂(k)|²`
(source line 2851 with `a = (d-s)/2`). -/
def homSobolevSq (a : ℝ) (ψ : Torus d → ℝ) : ℝ :=
  ∑' k : NonzeroLattice d, (2 * Real.pi * Lattice.enorm k.1) ^ (2 * a) * ‖Torus.fcoef ψ k.1‖ ^ 2

/-- Finiteness of the homogeneous Sobolev seminorm (summability of its defining series; without
it the real `tsum` is the junk value `0`). -/
def HasFiniteHomSobolev (a : ℝ) (ψ : Torus d → ℝ) : Prop :=
  Summable fun k : NonzeroLattice d =>
    (2 * Real.pi * Lattice.enorm k.1) ^ (2 * a) * ‖Torus.fcoef ψ k.1‖ ^ 2

/-- `‖ψ‖_{Ḣ^a}`. -/
def homSobolev (a : ℝ) (ψ : Torus d → ℝ) : ℝ := Real.sqrt (homSobolevSq a ψ)

/-! ### The commutator quantity -/

/-- The symmetrised commutator kernel `(v(x) - v(y)) · G(x - y)` off the diagonal, `0` on it. -/
def commKernel (G : Torus d → Euc d) (v : Torus d → Euc d) (x y : Torus d) : ℝ :=
  if x = y then 0 else inner ℝ (v x - v y) (G (x - y))

/-- `∬_{𝔻²∖△} k d(μ_N - μ)^{⊗2}` for a symmetric kernel `k`, written out with the particle diagonal
deleted: `N⁻² ∑_{i≠j} k(x_i,x_j) - 2N⁻¹ ∑_i ∫ k(x_i,y) dμ(y) + ∬ k dμ dμ` (the kernel is taken to
vanish on the diagonal, which is `μ ⊗ μ`- and `μ_N ⊗ μ`-null for `μ ≪ dx`). -/
def offDiagPairing (k : Torus d → Torus d → ℝ) (X : Config d N) (μ : Measure (Torus d)) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)
    - (2 / (N : ℝ)) * ∑ i, ∫ y, k (X i) y ∂μ
    + ∫ x, ∫ y, k x y ∂μ ∂μ

/-- `Comm_N^G(v; X_N, μ) = ∬_{𝔻²∖△} (v(x)-v(y)) · G(x-y) d(N⁻¹∑δ_{x_i} - μ)^{⊗2}` for a force field
`G` (`G = ∇g` in `B:eq:commutator-quantity`, `G = ∇h` for the comparison kernel of
Proposition 3.38). -/
def commQuantityWith (G : Torus d → Euc d) (v : Torus d → Euc d) (X : Config d N)
    (μ : Measure (Torus d)) : ℝ :=
  offDiagPairing (commKernel G v) X μ

/-- `Comm_N(v; X_N, μ)` of `B:eq:commutator-quantity` (source lines 2815-2818), for the periodic
Riesz/log kernel. -/
def commQuantity (d : ℕ) (s : ℝ) (v : Torus d → Euc d) (X : Config d N) (μ : Measure (Torus d)) :
    ℝ :=
  commQuantityWith (periodicRieszGrad d s) v X μ

/-- Absolute convergence of the integrals defining `offDiagPairing k X μ` (lines 2820-2821). -/
def OffDiagIntegrable (k : Torus d → Torus d → ℝ) (X : Config d N) (μ : Measure (Torus d)) :
    Prop :=
  (∀ i, Integrable (fun y => k (X i) y) μ) ∧
    Integrable (fun p : Torus d × Torus d => k p.1 p.2) (μ.prod μ)

/-! ### Proposition 3.32: commutator estimate -/

/-- Proposition 3.32 `M:B:prop:commutator` (source lines 2824-2836), item (i) (torus):
there are constants `C₀ = C₀(d,s)` and `C` such that, for every `0 ≤ s < d`, every probability
density `μ` with `‖μ‖_∞ ≤ Λ` (`λ = (NΛ)^{-1/d} < 1`), every pairwise distinct `X_N` and every
Lipschitz vector field `v` with `‖v‖_* ≤ K`, the integrals defining `Comm_N(v; X_N, μ)` converge
absolutely and `|Comm_N(v;X_N,μ)| ≤ C ‖v‖_* (F_N(X_N,μ) + o_N)`, pathwise.

External: for `s ≥ d-2` this is Chodron de Courcel–Rosenzweig–Serfaty, *Sharp commutator
estimates of all order for Coulomb and Riesz modulated energies* (2025), Prop. 2.13; for
`s < d-2` Hess-Childs–Rosenzweig, *Sharp commutator estimates …* (2025), Thm. 1.1 and Rem. 1.3,
with the normalisation translation of `H:subsec:conventions` (lines 417-430; the kernel here is
`periodicRiesz d s`, ISSUES §B K1).  PLAN: the source gives no proof; a Lean proof must follow the
cited papers (periodic Riesz: smearing at scale `λ` with the heat-kernel/Caffarelli–Silvestre
extension, commutator with the stress tensor, the `s<d-2` case through the fractional transport
term of `‖v‖_*`).  The absolute-convergence clause follows from `|commKernel| ≤ C L (|x-y|^{-s} + 1)`
(`periodicRieszGrad` bounds in `HRS/Kernel/GradBasic.lean`/`GradReg.lean`) and `s < d`. -/
theorem commutator_estimate (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ (v : Torus d → Euc d) (K : ℝ), HasTransportBound d s v K →
        OffDiagIntegrable (commKernel (periodicRieszGrad d s) v) X (withDensityReal ρ) ∧
        |commQuantity d s v X (withDensityReal ρ)| ≤
          C * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  -- ENER-02b route decision: this is the external input of Prop. 3.32 (Chodron de Courcel-Rosenzweig-
  -- Serfaty Prop. 2.13; Hess-Childs-Rosenzweig Thm 1.1).  Neither the repository (`HRS/Energy`,
  -- `HRS/Kernel`) nor the vendored `external/dgrhs` (attractive-log partition bounds, CLT; no
  -- commutator layer) contains the smearing/stress-tensor commutator machinery, so it stays an
  -- "external" `sorry` (docs/ISSUES.md Q8).
  sorry

/-! ### Propositions 3.33 and 3.34: coercivity -/

/-! ### Route for `periodic_coercivity` (package ENER-02c; helpers in `HRS.CoercAux`)

With `a = (d-s)/2`, `A = subA d s`, `psiFn x u = ∑_{k≠0} e^{-u|k|²} cos(2π k·x)`:
* `g(x) = A ∫_0^∞ u^{a-1} psiFn x u du` for `x ≠ 0`; split at `u = ε` (`ε = λ²`):
  `g = gT ε + nearF ε` with `gT ε = ∑_k cT ε k cos(2π k·x)`, `cT ε k = A ∫_ε^∞ u^{a-1} e^{-u|k|²} du ≥ 0`
  (`periodicRiesz_decomp`, `gT_eq_integral`), the TeX truncation `g_η`.
* `nearF ≥ -A ε^a/a` (since `psiFn ≥ -1`: positivity of theta, `psi_ge_neg_one`), `∫ nearF = 0`
  (both `g` and `gT` have mean zero); hence `∫ nearF(x-y) dμ(y) ∈ [-B', ΛB']` (`nearF_conv_bounds`).
* `Esq = ∬ gT d(μ_N-μ)^{⊗2} = ∑_k cT |\hat{ρ}(k)|² ≥ 0` (`Q_eq_tsum`, `integral_trigSum_sub`), and
  `F_N ≥ ½ Esq - gT(0)/(2N) - (1+Λ)B'` (`rieszEnergy_ge_aux`); `gT(0) ≲ ε^{-s/2}` (`s>0`) resp.
  `½ log(1/ε) + C` (`s=0`, exact coefficient `subA d 0 · π^{d/2} = ½`: `subA_zero_mul`), via the
  small-time theta bound `one_add_psi_zero_le`.  With `ε = λ²`: `Esq ≤ 2 (F_N + o_N)` (`coercivity_energy`).
* Test bound: mollify `ψ` by the periodic heat kernel `p_ε` (`heatK`, mass one, first moment
  `≲ √ε` from the Gaussian majorant `Gt`; `heat_moment`, `heatP_approx`), and use Fourier
  Cauchy–Schwarz (`fourier_side_bound`) with the lower bound `cT ε k ≳ e^{-2ε|k|²}|k|^{-(d-s)}`
  (`cT_lower`, `intT_lower`).  The case `d = 1` needs `periodicRiesz` facts that the library only
  proves for `2 ≤ d` (`*_one` copies in `CoercCopies`, the proofs never use `2 ≤ d`). -/

namespace CoercAux

section CoercCopies

open KernelAux Complex Set
open scoped Real

variable {d : ℕ} {s : ℝ}

theorem rieszConst_pos_one {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    0 < rieszConst d s := by
  have hd' : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold rieszConst
  split_ifs with h
  · exact mul_pos (mul_pos (by positivity) (by positivity)) (Real.Gamma_pos_of_pos (by positivity))
  · have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
    exact div_pos (mul_pos (mul_pos (by positivity) (by positivity))
      (Real.Gamma_pos_of_pos (by linarith))) (Real.Gamma_pos_of_pos (by linarith))

theorem periodicRiesz_tendsto_one (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (x : Torus d) (hx : x ≠ 0) :
    Tendsto (fun ε => heatRiesz d s ε x) (𝓝[>] 0) (𝓝 (periodicRiesz d s x)) := by
  obtain ⟨L, hL⟩ := heat_limit_exists hsd x hx
  have : periodicRiesz d s x = L := hL.limUnder_eq
  rw [this]; exact hL

theorem integral_periodicRiesz_mode_one {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (k : Lattice d) :
    ∫ x : Torus d, Torus.mode (-k) x * ((periodicRiesz d s x : ℝ) : ℂ) = ((rieszCoeff d s k : ℝ) : ℂ) := by
  have hd0 : 0 < d := by omega
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  obtain ⟨C1, C2, hC1, hC2, hbd⟩ := heat_eps_bound hs0 hsd
  set μ : Measure (Fin d → ℝ) := volume.restrict (Box d) with hμ
  set G : (Fin d → ℝ) → ℝ := fun y => C1 * ‖y‖ ^ (-((s + d)/2)) + C2 with hG
  set Fε : ℝ → (Fin d → ℝ) → ℂ := fun ε y =>
    Torus.mode (-k) (boxPt y) * ((heatRiesz d s ε (boxPt y) : ℝ) : ℂ) with hFε
  set F0 : (Fin d → ℝ) → ℂ := fun y =>
    Torus.mode (-k) (boxPt y) * ((periodicRiesz d s (boxPt y) : ℝ) : ℂ) with hF0
  have hne : ∀ᵐ y ∂μ, y ≠ 0 := by
    have h1 : ∀ᵐ y ∂(volume : Measure (Fin d → ℝ)), y ≠ 0 := by
      rw [ae_iff]; simp
    exact ae_restrict_of_ae h1
  have hmem : ∀ᵐ y ∂μ, y ∈ Box d := ae_restrict_mem (measurableSet_Box d)
  have hdom := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[>] (0:ℝ))
    (F := Fε) (f := F0) G ?_ ?_ ?_ ?_
  · -- identify the limit
    have h1 : ∀ ε : ℝ, 0 < ε → ∫ y, Fε ε y ∂μ =
        ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ) := by
      intro ε hε
      rw [← integral_heat_mode hsd hε k]
      exact (integral_torus_box (fun x : Torus d => Torus.mode (-k) x * ((heatRiesz d s ε x : ℝ) : ℂ))).symm
    have h2 : Tendsto (fun ε : ℝ => ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 ((rieszCoeff d s k : ℝ) : ℂ)) := by
      have : Continuous fun ε : ℝ => ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ) := by
        fun_prop
      have := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
      simpa using this
    have h3 : Tendsto (fun ε : ℝ => ∫ y, Fε ε y ∂μ) (𝓝[>] 0) (𝓝 ((rieszCoeff d s k : ℝ) : ℂ)) :=
      h2.congr' (by filter_upwards [self_mem_nhdsWithin] with ε hε using (h1 ε hε).symm)
    have h4 := tendsto_nhds_unique hdom h3
    rw [← h4]
    exact integral_torus_box (fun x : Torus d => Torus.mode (-k) x * ((periodicRiesz d s x : ℝ) : ℂ))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    refine Continuous.aestronglyMeasurable ?_
    exact ((Torus.continuous_mode _).comp (continuous_boxPt d)).mul
      (Complex.continuous_ofReal.comp ((KernelAux.continuous_heatRiesz hsd hε').comp (continuous_boxPt d)))
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    filter_upwards [hne, hmem] with y hy hyB
    have hy0 : boxPt y ≠ 0 := fun h => hy (boxPt_eq_zero hyB h)
    obtain ⟨j, hj⟩ := exists_argmax hd0 y
    have hyj : y j ≠ 0 := by
      intro h0
      apply hy
      have : ‖y‖ = 0 := by rw [hj, h0, abs_zero]
      exact norm_eq_zero.mp this
    have := hbd y (Box_abs_le hyB) j hyj ε hε.1 hε.2.le
    simp only [hFε, norm_mul, norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs, hG, hj]
    exact this
  · have hI : IntegrableOn (fun y : Fin d → ℝ => ‖y‖ ^ (-((s + d)/2))) (Box d) :=
      integrableOn_Box_rpow hd0 (by linarith)
    exact (hI.const_mul C1).add (integrableOn_const (measure_Box_ne_top d))
  · filter_upwards [hne, hmem] with y hy hyB
    have hy0 : boxPt y ≠ 0 := fun h => hy (boxPt_eq_zero hyB h)
    have := periodicRiesz_tendsto_one hd hs0 hsd (boxPt y) hy0
    exact (Complex.continuous_ofReal.tendsto _ |>.comp this).const_mul _


theorem periodicRiesz_box_bound_one {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ y : Fin d → ℝ, y ∈ Box d → y ≠ 0 →
      |periodicRiesz d s (boxPt y)| ≤ C1 * ‖y‖ ^ (-((s + d)/2)) + C2 := by
  have hd0 : 0 < d := by omega
  obtain ⟨C1, C2, hC1, hC2, hbd⟩ := heat_eps_bound hs0 hsd
  refine ⟨C1, C2, hC1, hC2, fun y hyB hy => ?_⟩
  have hy0 : boxPt y ≠ 0 := fun h => hy (boxPt_eq_zero hyB h)
  obtain ⟨j, hj⟩ := exists_argmax hd0 y
  have hyj : y j ≠ 0 := by
    intro h0
    apply hy
    have : ‖y‖ = 0 := by rw [hj, h0, abs_zero]
    exact norm_eq_zero.mp this
  have hlim := (periodicRiesz_tendsto_one hd hs0 hsd (boxPt y) hy0).abs
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
  have := hbd y (Box_abs_le hyB) j hyj ε hε.1 hε.2.le
  rwa [← hj] at this

theorem aestronglyMeasurable_periodicRiesz_one {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    AEStronglyMeasurable (periodicRiesz d s) (volume : Measure (Torus d)) := by
  have hd0 : 0 < d := by omega
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := fun n : ℕ => heatRiesz d s (1 / ((n:ℝ) + 1)))
    (fun n => (KernelAux.continuous_heatRiesz hsd (by positivity)).aestronglyMeasurable) ?_
  filter_upwards [torus_ae_ne hd0] with x hx
  have h := periodicRiesz_tendsto_one hd hs0 hsd x hx
  refine h.comp ?_
  refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall fun n => ?_⟩
  simp only [mem_Ioi]; positivity

theorem integrable_periodicRiesz_one {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (periodicRiesz d s) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C1, C2, hC1, hC2, hbd⟩ := periodicRiesz_box_bound_one hd hs0 hsd
  refine ⟨aestronglyMeasurable_periodicRiesz_one hd hs0 hsd, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_torus_box (fun x => ‖periodicRiesz d s x‖ₑ)]
  have hI : IntegrableOn (fun y : Fin d → ℝ => C1 * ‖y‖ ^ (-((s + d)/2)) + C2) (Box d) :=
    ((integrableOn_Box_rpow hd0 (by linarith)).const_mul C1).add
      (integrableOn_const (measure_Box_ne_top d))
  have hne : ∀ᵐ y ∂(volume.restrict (Box d)), y ≠ 0 := by
    exact ae_restrict_of_ae (ae_ne_pi hd0)
  calc ∫⁻ y in Box d, ‖periodicRiesz d s (boxPt y)‖ₑ
      ≤ ∫⁻ y in Box d, ENNReal.ofReal (C1 * ‖y‖ ^ (-((s + d)/2)) + C2) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hne, ae_restrict_mem (measurableSet_Box d)] with y hy hyB
        rw [← ofReal_norm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (hbd y hyB hy)
    _ = ∫⁻ y in Box d, ‖C1 * ‖y‖ ^ (-((s + d)/2)) + C2‖ₑ := by
        refine lintegral_congr fun y => ?_
        rw [Real.enorm_of_nonneg (by positivity)]
    _ < ∞ := hI.2

theorem periodicRiesz_eq_integral_one {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (x : Torus d) (hx : x ≠ 0) :
    periodicRiesz d s x = subA d s * ∫ t in Ioi (0:ℝ), t ^ (((d:ℝ) - s) / 2 - 1) * psiFn x t := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  obtain ⟨M, hM0, hM⟩ := psi_bound x hx
  have hcont := psi_continuousOn x
  have hmeas : ∀ ε : ℝ, 0 ≤ ε → AEStronglyMeasurable (fun t : ℝ => t ^ (a - 1) * psiFn x (t + ε))
      (volume.restrict (Ioi 0)) := by
    intro ε hε
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)) ?_
    refine hcont.comp (continuousOn_id.add continuousOn_const) fun t ht => ?_
    simp only [mem_Ioi] at ht ⊢
    linarith
  have hlim : Tendsto (fun ε => ∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x (t + ε)) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x t)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => M * (Real.exp (-t) * t ^ (a - 1))) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε using hmeas ε (le_of_lt hε)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have hε' : 0 < ε := hε
      have ht' : 0 < t := ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
      have h1 := hM (t + ε) (by linarith)
      have h2 : Real.exp (-(t + ε)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
      have h3 := Real.rpow_pos_of_pos ht' (a - 1)
      calc t ^ (a - 1) * |psiFn x (t + ε)| ≤ t ^ (a - 1) * (M * Real.exp (-t)) := by
            gcongr
            exact h1.trans (by gcongr)
        _ = _ := by ring
    · exact (Real.GammaIntegral_convergent ha).const_mul M
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have ht' : 0 < t := ht
      refine Tendsto.const_mul _ ?_
      have h1 : Tendsto (fun ε : ℝ => t + ε) (𝓝[>] 0) (𝓝 t) := by
        have : Tendsto (fun ε : ℝ => t + ε) (𝓝 0) (𝓝 (t + 0)) :=
          (continuous_const.add continuous_id).tendsto 0
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h2 : ContinuousAt (psiFn x) t :=
        (hcont t ht').continuousAt (Ioi_mem_nhds ht')
      exact h2.tendsto.comp h1
  have h2 : Tendsto (fun ε => heatRiesz d s ε x) (𝓝[>] 0)
      (𝓝 (subA d s * ∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x t)) := by
    refine (hlim.const_mul _).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (heatRiesz_eq_integral hsd hε x).symm
  exact tendsto_nhds_unique (periodicRiesz_tendsto_one hd hs0 hsd x hx) h2


theorem subA_nonneg_one {d : ℕ} {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) : 0 ≤ subA d s := by
  unfold subA
  have := rieszConst_pos_one hd hs0 hsd
  have := Real.Gamma_pos_of_pos (show 0 < ((d:ℝ) - s) / 2 by linarith)
  have : 0 < (2 * π) ^ (s - d) := Real.rpow_pos_of_pos (by positivity) _
  positivity

theorem integral_periodicRiesz_one (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (periodicRiesz d s) ∧ ∫ x, periodicRiesz d s x = 0 := by
  refine ⟨integrable_periodicRiesz_one hd hs0 hsd, ?_⟩
  have h := integral_periodicRiesz_mode_one hd hs0 hsd 0
  simp only [neg_zero, Torus.mode_zero, one_mul] at h
  rw [integral_complex_ofReal] at h
  have h0 : rieszCoeff d s 0 = 0 := by simp [rieszCoeff]
  rw [h0] at h
  exact_mod_cast h


end CoercCopies


section CoercTrunc

open KernelAux Set

variable {d : ℕ} {s : ℝ}

/-- The Fourier coefficient of the truncated kernel `g_ε`:
`A ∫_ε^∞ u^{a-1} e^{-u|k|²} du` (`k ≠ 0`), `a = (d-s)/2`, `A = subA d s`. -/
def cT (d : ℕ) (s ε : ℝ) (k : Lattice d) : ℝ :=
  if k = 0 then 0 else
    subA d s * ∫ u in Ioi ε, u ^ (((d : ℝ) - s) / 2 - 1) * Real.exp (-(Lattice.enorm k ^ 2 * u))

/-- The truncated kernel `g_ε = ∑_k ĉ_ε(k) cos(2π k·x)`. -/
def gT (d : ℕ) (s ε : ℝ) (x : Torus d) : ℝ := ∑' k : Lattice d, cT d s ε k * Torus.cosMode k x

theorem integrableOn_T {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) (k : Lattice d) (hk : k ≠ 0) :
    IntegrableOn (fun u : ℝ => u ^ (a - 1) * Real.exp (-(Lattice.enorm k ^ 2 * u))) (Ioi ε) :=
  (integrable_majorant ha k hk).mono_set (Ioi_subset_Ioi hε.le)

theorem integrableOn_half {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => u ^ (a - 1) * Real.exp (-(1 / 2 * u))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := 1 / 2)
    (by linarith) one_pos (by norm_num)
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  ring_nf

/-- the constant `∫_0^∞ u^{a-1} e^{-u/2} du`. -/
def halfInt (a : ℝ) : ℝ := ∫ u in Ioi (0:ℝ), u ^ (a - 1) * Real.exp (-(1 / 2 * u))

theorem intT_le {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) (k : Lattice d) (hk : k ≠ 0) :
    ∫ u in Ioi ε, u ^ (a - 1) * Real.exp (-(Lattice.enorm k ^ 2 * u)) ≤
      Real.exp (-(ε / 2) * Lattice.enorm k ^ 2) * halfInt a := by
  have hm : 1 ≤ Lattice.enorm k := one_le_enorm k hk
  have hm2 : 1 ≤ Lattice.enorm k ^ 2 := by nlinarith
  have hint := ((integrableOn_half ha).mono_set (Ioi_subset_Ioi hε.le)).const_mul
    (Real.exp (-(ε / 2) * Lattice.enorm k ^ 2))
  calc ∫ u in Ioi ε, u ^ (a - 1) * Real.exp (-(Lattice.enorm k ^ 2 * u))
      ≤ ∫ u in Ioi ε, Real.exp (-(ε / 2) * Lattice.enorm k ^ 2) *
          (u ^ (a - 1) * Real.exp (-(1 / 2 * u))) := by
        refine setIntegral_mono_on (integrableOn_T ha hε k hk) hint measurableSet_Ioi ?_
        intro u hu
        have hu' : ε < u := hu
        have hu0 : 0 < u := by linarith
        have h1 : 0 ≤ u ^ (a - 1) := (Real.rpow_pos_of_pos hu0 _).le
        have h2 : Real.exp (-(Lattice.enorm k ^ 2 * u)) ≤
            Real.exp (-(ε / 2) * Lattice.enorm k ^ 2) * Real.exp (-(1 / 2 * u)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith [mul_le_mul_of_nonneg_left hm2 hu0.le]
        calc u ^ (a - 1) * Real.exp (-(Lattice.enorm k ^ 2 * u))
            ≤ u ^ (a - 1) * (Real.exp (-(ε / 2) * Lattice.enorm k ^ 2) * Real.exp (-(1 / 2 * u))) :=
              mul_le_mul_of_nonneg_left h2 h1
          _ = _ := by ring
    _ = Real.exp (-(ε / 2) * Lattice.enorm k ^ 2) *
          ∫ u in Ioi ε, u ^ (a - 1) * Real.exp (-(1 / 2 * u)) := by rw [integral_const_mul]
    _ ≤ _ := by
        unfold halfInt
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine setIntegral_mono_set (integrableOn_half ha) ?_ (Ioi_subset_Ioi hε.le).eventuallyLE
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
        have hu0 : (0:ℝ) < u := hu
        simp only [Pi.zero_apply]
        have := Real.rpow_pos_of_pos hu0 (a - 1)
        positivity




theorem halfInt_nonneg (a : ℝ) : 0 ≤ halfInt a := by
  unfold halfInt
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have hu0 : (0:ℝ) < u := hu
  have := Real.rpow_pos_of_pos hu0 (a - 1)
  positivity

theorem cT_nonneg (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (k : Lattice d) :
    0 ≤ cT d s ε k := by
  unfold cT
  split_ifs with hk
  · exact le_rfl
  · refine mul_nonneg (subA_nonneg_one hd hs0 hsd) ?_
    refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
    have hu0 : (0:ℝ) < u := lt_trans hε hu
    have := Real.rpow_pos_of_pos hu0 (((d : ℝ) - s) / 2 - 1)
    positivity

theorem cT_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (k : Lattice d) :
    cT d s ε k ≤ subA d s * halfInt (((d:ℝ) - s) / 2) * Real.exp (-(ε / 2) * Lattice.enorm k ^ 2) := by
  have ha : 0 < ((d:ℝ) - s) / 2 := by linarith
  have hA := subA_nonneg_one hd hs0 hsd
  have hH := halfInt_nonneg (((d:ℝ) - s) / 2)
  unfold cT
  split_ifs with hk
  · positivity
  · have := intT_le ha hε k hk
    calc subA d s * ∫ u in Ioi ε, u ^ (((d : ℝ) - s) / 2 - 1) * Real.exp (-(Lattice.enorm k ^ 2 * u))
        ≤ subA d s * (Real.exp (-(ε / 2) * Lattice.enorm k ^ 2) * halfInt (((d:ℝ) - s) / 2)) :=
          mul_le_mul_of_nonneg_left this hA
      _ = _ := by ring

theorem summable_cT (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    Summable (cT d s ε) := by
  refine Summable.of_nonneg_of_le (cT_nonneg hd hs0 hsd hε) (cT_le hd hs0 hsd hε)
    ((summable_gauss_lattice d (ε / 2) (by positivity)).mul_left _)

theorem continuous_gT (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    Continuous (gT d s ε) := by
  unfold gT
  refine continuous_tsum (u := cT d s ε) (fun k => continuous_const.mul (Torus.continuous_cosMode k))
    (summable_cT hd hs0 hsd hε) (fun k x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cT_nonneg hd hs0 hsd hε k)]
  calc cT d s ε k * |Torus.cosMode k x| ≤ cT d s ε k * 1 :=
        mul_le_mul_of_nonneg_left (abs_cosMode_le k x) (cT_nonneg hd hs0 hsd hε k)
    _ = _ := mul_one _




/-- The integrand of the `k`-th mode of the truncated representation. -/
def fT (x : Torus d) (a : ℝ) (k : Lattice d) (u : ℝ) : ℝ :=
  u ^ (a - 1) * (if k = 0 then 0 else Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x)

theorem fT_bound (x : Torus d) (a : ℝ) (k : Lattice d) (hk : k ≠ 0) {u : ℝ} (hu : 0 < u) :
    ‖fT x a k u‖ ≤ u ^ (a - 1) * Real.exp (-(Lattice.enorm k ^ 2 * u)) := by
  unfold fT
  simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.rpow_pos_of_pos hu _)]
  have hc := abs_cosMode_le k x
  have hp : 0 ≤ u ^ (a - 1) := (Real.rpow_pos_of_pos hu _).le
  have e : Real.exp (-u * Lattice.enorm k ^ 2) = Real.exp (-(Lattice.enorm k ^ 2 * u)) := by
    congr 1; ring
  rw [e]
  calc u ^ (a - 1) * (Real.exp (-(Lattice.enorm k ^ 2 * u)) * |Torus.cosMode k x|)
      ≤ u ^ (a - 1) * (Real.exp (-(Lattice.enorm k ^ 2 * u)) * 1) := by gcongr
    _ = _ := by ring

theorem fT_integrable {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) (x : Torus d) (k : Lattice d) :
    IntegrableOn (fT x a k) (Ioi ε) := by
  by_cases hk : k = 0
  · have : fT x a k = 0 := by funext u; simp [fT, hk]
    rw [this]; exact integrableOn_zero
  · refine Integrable.mono' (integrableOn_T ha hε k hk) ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      unfold fT
      simp only [hk, ite_false]
      fun_prop
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
      exact fT_bound x a k hk (lt_trans hε hu)

theorem gT_eq_integral (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (x : Torus d) :
    gT d s ε x = subA d s * ∫ u in Ioi ε, u ^ (((d : ℝ) - s) / 2 - 1) * psiFn x u := by
  set a : ℝ := ((d : ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hH := halfInt_nonneg a
  have hFnorm : Summable fun k : Lattice d => ∫ u in Ioi ε, ‖fT x a k u‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun u => norm_nonneg _)
      (fun k => ?_) ((summable_gauss_lattice d (ε / 2) (by positivity)).mul_left (halfInt a))
    by_cases hk : k = 0
    · have : ∀ u, ‖fT x a k u‖ = 0 := fun u => by simp [fT, hk]
      simp only [this, integral_zero]
      exact mul_nonneg hH (Real.exp_pos _).le
    · calc ∫ u in Ioi ε, ‖fT x a k u‖
          ≤ ∫ u in Ioi ε, u ^ (a - 1) * Real.exp (-(Lattice.enorm k ^ 2 * u)) := by
            refine setIntegral_mono_on (fT_integrable ha hε x k).norm (integrableOn_T ha hε k hk)
              measurableSet_Ioi ?_
            intro u hu
            exact fT_bound x a k hk (lt_trans hε hu)
        _ ≤ Real.exp (-(ε / 2) * Lattice.enorm k ^ 2) * halfInt a := intT_le ha hε k hk
        _ = _ := by ring
  have hsw : ∑' k : Lattice d, ∫ u in Ioi ε, fT x a k u =
      ∫ u in Ioi ε, ∑' k : Lattice d, fT x a k u :=
    integral_tsum_of_summable_integral_norm (fT_integrable ha hε x) hFnorm
  have hterm : ∀ k : Lattice d, cT d s ε k * Torus.cosMode k x =
      subA d s * ∫ u in Ioi ε, fT x a k u := by
    intro k
    by_cases hk : k = 0
    · have : fT x a k = 0 := by funext u; simp [fT, hk]
      have h0 : cT d s ε k = 0 := by simp [cT, hk]
      rw [h0, zero_mul, this]
      simp
    · have h1 : (fun u => fT x a k u) = fun u =>
          (u ^ (a - 1) * Real.exp (-(Lattice.enorm k ^ 2 * u))) * Torus.cosMode k x := by
        funext u
        simp only [fT, hk, ite_false]
        have e : Real.exp (-u * Lattice.enorm k ^ 2) = Real.exp (-(Lattice.enorm k ^ 2 * u)) := by
          congr 1; ring
        rw [e]; ring
      rw [h1, integral_mul_const]
      simp only [cT, hk, ite_false]
      ring
  have hpt : ∀ u : ℝ, 0 < u → ∑' k : Lattice d, fT x a k u = u ^ (a - 1) * psiFn x u := by
    intro u hu
    unfold fT psiFn
    rw [tsum_mul_left]
  unfold gT
  simp_rw [hterm]
  rw [tsum_mul_left, hsw]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun u hu => hpt u (lt_trans hε hu)




theorem integral_Ioc_rpow {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∫ u in Ioc 0 ε, u ^ (a - 1) = ε ^ a / a := by
  rw [← intervalIntegral.integral_of_le hε.le, integral_rpow (Or.inl (by linarith))]
  simp [Real.zero_rpow ha.ne']

theorem integrableOn_Ioc_rpow {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun u : ℝ => u ^ (a - 1)) (Ioc 0 ε) := by
  have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ε) (r := a - 1) (by linarith)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hε.le).mp this

theorem psi_ge_neg_one (x : Torus d) {u : ℝ} (hu : 0 < u) : -1 ≤ psiFn x u := by
  have h := theta_nonneg x hu
  rw [psi_eq x hu] at h
  linarith

theorem periodicRiesz_decomp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε)
    (x : Torus d) (hx : x ≠ 0) :
    periodicRiesz d s x = gT d s ε x +
      subA d s * ∫ u in Ioc 0 ε, u ^ (((d : ℝ) - s) / 2 - 1) * psiFn x u := by
  rw [periodicRiesz_eq_integral_one hd hs0 hsd x hx, gT_eq_integral hd hs0 hsd hε x, ← mul_add]
  congr 1
  rw [← Ioc_union_Ioi_eq_Ioi hε.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  · rw [add_comm]
  · exact (integrableOn_psi hsd x hx).mono_set (by
      intro u hu; exact hu.1 |> fun h => (mem_Ioi.mpr h))
  · exact (integrableOn_psi hsd x hx).mono_set (Ioi_subset_Ioi hε.le)

theorem near_ge (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε)
    (x : Torus d) (hx : x ≠ 0) :
    -(subA d s * (ε ^ (((d : ℝ) - s) / 2) / (((d : ℝ) - s) / 2))) ≤
      periodicRiesz d s x - gT d s ε x := by
  have ha : 0 < ((d : ℝ) - s) / 2 := by linarith
  have hA := subA_nonneg_one hd hs0 hsd
  rw [periodicRiesz_decomp hd hs0 hsd hε x hx, add_sub_cancel_left]
  have hint : IntegrableOn (fun u : ℝ => u ^ (((d : ℝ) - s) / 2 - 1) * psiFn x u) (Ioc 0 ε) :=
    (integrableOn_psi hsd x hx).mono_set (fun u hu => mem_Ioi.mpr hu.1)
  have hI : -(ε ^ (((d : ℝ) - s) / 2) / (((d : ℝ) - s) / 2)) ≤
      ∫ u in Ioc 0 ε, u ^ (((d : ℝ) - s) / 2 - 1) * psiFn x u := by
    rw [← integral_Ioc_rpow ha hε, ← integral_neg]
    refine setIntegral_mono_on (integrableOn_Ioc_rpow ha hε).neg hint measurableSet_Ioc ?_
    intro u hu
    have h0 : 0 < u := hu.1
    have h1 := psi_ge_neg_one x h0
    have h2 := Real.rpow_pos_of_pos h0 (((d : ℝ) - s) / 2 - 1)
    nlinarith
  calc -(subA d s * (ε ^ (((d : ℝ) - s) / 2) / (((d : ℝ) - s) / 2)))
      = subA d s * (-(ε ^ (((d : ℝ) - s) / 2) / (((d : ℝ) - s) / 2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hI hA




/-- constant in the theta bound -/
def thT : ℝ := ∑' n : ℤ, Real.exp (-(Real.pi ^ 2 / 2) * (n : ℝ) ^ 2)

theorem thT_nonneg : 0 ≤ thT := tsum_nonneg fun _ => (Real.exp_pos _).le

/-- `S(u) = ∑_n e^{-π² n²/u} ≤ 1 + (2 thT/π²) u` for `0 < u ≤ 1`. -/
theorem theta_zero_one_dim {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    ∑' n : ℤ, Real.exp (-(Real.pi ^ 2 * ((n : ℝ) - 0) ^ 2 / u)) ≤ 1 + (2 * thT / Real.pi ^ 2) * u := by
  set E := Real.exp (-(Real.pi ^ 2 / (2 * u))) with hE
  have hsum : Summable fun n : ℤ => Real.exp (-(Real.pi ^ 2 / 2) * (n : ℝ) ^ 2) :=
    summable_exp_sq _ (by positivity)
  have hb : ∀ n : ℤ, Real.exp (-(Real.pi ^ 2 * ((n : ℝ) - 0) ^ 2 / u)) ≤
      (if n = 0 then 1 else 0) + E * Real.exp (-(Real.pi ^ 2 / 2) * (n : ℝ) ^ 2) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have hE0 : 0 ≤ E := (Real.exp_pos _).le
      simp
      positivity
    · simp only [hn, ite_false, zero_add]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have := Int.one_le_abs hn
        have h2 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast this
        nlinarith [sq_abs (n : ℝ)]
      have hπ : 0 < Real.pi ^ 2 := by positivity
      have h3 : (n : ℝ) ^ 2 / u ≥ 1 / (2 * u) + (n : ℝ) ^ 2 / 2 := by
        rw [ge_iff_le, div_add_div _ _ (by positivity) (by norm_num), div_le_div_iff₀ (by positivity) hu]
        nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hu1), sq_nonneg (n : ℝ), hu.le,
          mul_nonneg hu.le (sub_nonneg.mpr h1)]
      have h4 : Real.pi ^ 2 * ((n : ℝ) - 0) ^ 2 / u = Real.pi ^ 2 * ((n : ℝ) ^ 2 / u) := by ring
      rw [h4]
      have := mul_le_mul_of_nonneg_left h3 hπ.le
      have h5 : Real.pi ^ 2 * (1 / (2 * u) + (n : ℝ) ^ 2 / 2) =
          Real.pi ^ 2 / (2 * u) + Real.pi ^ 2 / 2 * (n : ℝ) ^ 2 := by ring
      rw [h5] at this
      nlinarith
  have hsum1 : Summable fun n : ℤ => Real.exp (-(Real.pi ^ 2 * ((n : ℝ) - 0) ^ 2 / u)) := by
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hb ?_
    exact (summable_of_ne_finset_zero (s := {0}) (by intro n hn; simp at hn; simp [hn])).add
      (hsum.mul_left E)
  calc ∑' n : ℤ, Real.exp (-(Real.pi ^ 2 * ((n : ℝ) - 0) ^ 2 / u))
      ≤ ∑' n : ℤ, ((if n = 0 then 1 else 0) + E * Real.exp (-(Real.pi ^ 2 / 2) * (n : ℝ) ^ 2)) :=
        hsum1.tsum_le_tsum hb ((summable_of_ne_finset_zero (s := {0})
          (by intro n hn; simp at hn; simp [hn])).add (hsum.mul_left E))
    _ = 1 + E * thT := by
        rw [(summable_of_ne_finset_zero (s := {0})
          (by intro n hn; simp at hn; simp [hn])).tsum_add (hsum.mul_left E), tsum_mul_left]
        simp [thT]
    _ ≤ _ := by
        have hv : 0 < Real.pi ^ 2 / (2 * u) := by positivity
        have h1 : E ≤ 2 * u / Real.pi ^ 2 := by
          rw [hE, Real.exp_neg]
          have := Real.add_one_le_exp (Real.pi ^ 2 / (2 * u))
          rw [inv_le_comm₀ (Real.exp_pos _) (by positivity)]
          have h2 : (Real.pi ^ 2 / (2 * u)) ≤ Real.exp (Real.pi ^ 2 / (2 * u)) := by linarith
          calc (2 * u / Real.pi ^ 2)⁻¹ = Real.pi ^ 2 / (2 * u) := by rw [inv_div]
            _ ≤ _ := h2
        have := mul_le_mul_of_nonneg_right h1 thT_nonneg
        calc 1 + E * thT ≤ 1 + 2 * u / Real.pi ^ 2 * thT := by linarith
          _ = _ := by ring




theorem exp_le_one_add_mul (x : ℝ) : Real.exp x ≤ 1 + x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have h2 := mul_le_mul_of_nonneg_left h (Real.exp_pos x).le
  rw [mul_add, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one, mul_neg] at h2
  linarith

/-- the constant `c₂` in `1 + Ψ_0(u) ≤ π^{d/2} u^{-d/2} (1 + c₂ u)` -/
def thC (d : ℕ) : ℝ := d * (2 * thT / Real.pi ^ 2) * Real.exp (d * (2 * thT / Real.pi ^ 2))

theorem thC_nonneg (d : ℕ) : 0 ≤ thC d := by
  unfold thC
  have := thT_nonneg
  positivity

theorem one_add_psi_zero_le (d : ℕ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    1 + psiFn (0 : Torus d) u ≤ Real.sqrt Real.pi ^ d * u ^ (-(d : ℝ) / 2) * (1 + thC d * u) := by
  have h := psi_eq (0 : Torus d) hu
  have hb : (boxPt (0 : Fin d → ℝ) : Torus d) = 0 := by
    funext i; simp [boxPt]
  have h2 := theta_prod (0 : Fin d → ℝ) hu
  rw [hb] at h2
  rw [h2] at h
  simp only [Pi.zero_apply] at h
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  set S := ∑' n : ℤ, Real.exp (-(Real.pi ^ 2 * ((n : ℝ) - 0) ^ 2 / u)) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hS1 := theta_zero_one_dim hu hu1
  rw [← hS] at hS1
  have hc1 : 0 ≤ 2 * thT / Real.pi ^ 2 := by have := thT_nonneg; positivity
  have h3 : (Real.sqrt (Real.pi / u) * S) ^ d ≤ (Real.sqrt (Real.pi / u) * (1 + (2 * thT / Real.pi ^ 2) * u)) ^ d :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hS1 (Real.sqrt_nonneg _)) d
  refine h3.trans ?_
  rw [mul_pow, sqrt_div_pow_eq d hu]
  have h4 : (1 + (2 * thT / Real.pi ^ 2) * u) ^ d ≤ 1 + thC d * u := by
    have e1 : (1 + (2 * thT / Real.pi ^ 2) * u) ≤ Real.exp ((2 * thT / Real.pi ^ 2) * u) := by
      have := Real.add_one_le_exp ((2 * thT / Real.pi ^ 2) * u); linarith
    have e2 : (1 + (2 * thT / Real.pi ^ 2) * u) ^ d ≤ Real.exp (d * ((2 * thT / Real.pi ^ 2) * u)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by positivity) e1 d
    refine e2.trans ?_
    have e3 := exp_le_one_add_mul (d * ((2 * thT / Real.pi ^ 2) * u))
    refine e3.trans ?_
    have e4 : Real.exp (d * ((2 * thT / Real.pi ^ 2) * u)) ≤ Real.exp (d * (2 * thT / Real.pi ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have : (0:ℝ) ≤ d * (2 * thT / Real.pi ^ 2) := by positivity
      nlinarith
    unfold thC
    have : (0:ℝ) ≤ d * ((2 * thT / Real.pi ^ 2) * u) := by positivity
    calc 1 + ↑d * (2 * thT / Real.pi ^ 2 * u) * Real.exp (↑d * (2 * thT / Real.pi ^ 2 * u))
        ≤ 1 + ↑d * (2 * thT / Real.pi ^ 2 * u) * Real.exp (↑d * (2 * thT / Real.pi ^ 2)) := by gcongr
      _ = _ := by ring
  have h5 : 0 ≤ Real.sqrt Real.pi ^ d * u ^ (-(d : ℝ) / 2) := by positivity
  calc Real.sqrt Real.pi ^ d * u ^ (-(d : ℝ) / 2) * (1 + (2 * thT / Real.pi ^ 2) * u) ^ d
      ≤ Real.sqrt Real.pi ^ d * u ^ (-(d : ℝ) / 2) * (1 + thC d * u) := mul_le_mul_of_nonneg_left h4 h5




theorem psi_zero_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ psiFn (0 : Torus d) u := by
  unfold psiFn
  refine tsum_nonneg fun k => ?_
  split_ifs
  · exact le_rfl
  · have : Torus.cosMode k (0 : Torus d) = 1 := by
      simp [Torus.cosMode, Torus.mode, UnitAddTorus.mFourier]
    rw [this, mul_one]
    exact (Real.exp_pos _).le

/-- the constant in the large-`u` bound of `Ψ`. -/
def psiLargeC (d : ℕ) : ℝ := Real.exp 1 * ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2)

theorem psiLargeC_nonneg (d : ℕ) : 0 ≤ psiLargeC d := by
  unfold psiLargeC
  have : 0 ≤ ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2) :=
    tsum_nonneg fun _ => (Real.exp_pos _).le
  positivity

theorem gT_zero_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    gT d s ε 0 ≤ subA d s * (Real.sqrt Real.pi ^ d *
        (∫ u in Ioc ε 1, u ^ (-s / 2 - 1) * (1 + thC d * u)) +
      psiLargeC d * Real.Gamma (((d : ℝ) - s) / 2)) := by
  set a : ℝ := ((d : ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hA := subA_nonneg_one hd hs0 hsd
  rw [gT_eq_integral hd hs0 hsd hε 0]
  refine mul_le_mul_of_nonneg_left ?_ hA
  set f : ℝ → ℝ := fun u => u ^ (a - 1) * psiFn (0 : Torus d) u with hf
  have hcont : ContinuousOn f (Ioi 0) :=
    ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)) (psi_continuousOn _)
  have hint1 : IntegrableOn f (Ioc ε 1) := by
    have : ContinuousOn f (Icc ε 1) := hcont.mono (fun u hu => lt_of_lt_of_le hε hu.1)
    exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hG : IntegrableOn (fun u : ℝ => psiLargeC d * (Real.exp (-u) * u ^ (a - 1))) (Ioi 0) :=
    (Real.GammaIntegral_convergent ha).const_mul (psiLargeC d)
  have hbound : ∀ u ∈ Ioi (1:ℝ), f u ≤ psiLargeC d * (Real.exp (-u) * u ^ (a - 1)) := by
    intro u hu
    have hu1 : (1:ℝ) < u := hu
    have hu0 : 0 < u := by linarith
    have := psi_large (0 : Torus d) hu1.le
    have h2 := (abs_le.mp this).2
    have h3 := Real.rpow_pos_of_pos hu0 (a - 1)
    rw [hf]
    unfold psiLargeC
    calc u ^ (a - 1) * psiFn (0 : Torus d) u
        ≤ u ^ (a - 1) * ((Real.exp 1 * ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2)) *
            Real.exp (-u)) := mul_le_mul_of_nonneg_left h2 h3.le
      _ = _ := by ring
  have hint2 : IntegrableOn f (Ioi 1) := by
    refine Integrable.mono' (hG.mono_set (Ioi_subset_Ioi zero_le_one)) ?_ ?_
    · exact (hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
      have hu1 : (1:ℝ) < u := hu
      have hu0 : 0 < u := by linarith
      have h0 : 0 ≤ f u := by
        rw [hf]
        exact mul_nonneg (Real.rpow_pos_of_pos hu0 _).le (psi_zero_nonneg hu0)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hbound u hu
  have hsplit : ∫ u in Ioi ε, f u = (∫ u in Ioc ε 1, f u) + ∫ u in Ioi 1, f u := by
    rw [← Ioc_union_Ioi_eq_Ioi hε1, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint1 hint2]
  rw [hsplit]
  refine add_le_add ?_ ?_
  · calc ∫ u in Ioc ε 1, f u
        ≤ ∫ u in Ioc ε 1, Real.sqrt Real.pi ^ d * (u ^ (-s / 2 - 1) * (1 + thC d * u)) := by
          refine setIntegral_mono_on hint1 ?_ measurableSet_Ioc ?_
          · refine Integrable.const_mul ?_ _
            have : ContinuousOn (fun u : ℝ => u ^ (-s / 2 - 1) * (1 + thC d * u)) (Icc ε 1) := by
              refine ContinuousOn.mul ?_ (by fun_prop)
              exact continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hε ht.1))
            exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self
          · intro u hu
            have hu0 : 0 < u := lt_of_lt_of_le hε hu.1.le
            have h1 := one_add_psi_zero_le d hu0 hu.2
            have h2 : psiFn (0 : Torus d) u ≤ Real.sqrt Real.pi ^ d * u ^ (-(d : ℝ) / 2) * (1 + thC d * u) := by
              linarith
            have h3 := Real.rpow_pos_of_pos hu0 (a - 1)
            have h4 : u ^ (a - 1) * u ^ (-(d : ℝ) / 2) = u ^ (-s / 2 - 1) := by
              rw [← Real.rpow_add hu0]; congr 1; rw [ha_def]; ring
            rw [hf]
            calc u ^ (a - 1) * psiFn (0 : Torus d) u
                ≤ u ^ (a - 1) * (Real.sqrt Real.pi ^ d * u ^ (-(d : ℝ) / 2) * (1 + thC d * u)) :=
                  mul_le_mul_of_nonneg_left h2 h3.le
              _ = Real.sqrt Real.pi ^ d * (u ^ (a - 1) * u ^ (-(d : ℝ) / 2) * (1 + thC d * u)) := by ring
              _ = _ := by rw [h4]
      _ = _ := by rw [integral_const_mul]
  · calc ∫ u in Ioi 1, f u
        ≤ ∫ u in Ioi (1:ℝ), psiLargeC d * (Real.exp (-u) * u ^ (a - 1)) :=
          setIntegral_mono_on hint2 (hG.mono_set (Ioi_subset_Ioi zero_le_one)) measurableSet_Ioi hbound
      _ ≤ ∫ u in Ioi (0:ℝ), psiLargeC d * (Real.exp (-u) * u ^ (a - 1)) := by
          refine setIntegral_mono_set hG ?_ (Ioi_subset_Ioi zero_le_one).eventuallyLE
          refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
          have hu0 : (0:ℝ) < u := hu
          have := Real.rpow_pos_of_pos hu0 (a - 1)
          have := psiLargeC_nonneg d
          simp only [Pi.zero_apply]
          positivity
      _ = _ := by rw [integral_const_mul, Real.Gamma_eq_integral ha]




theorem subA_zero_mul (hd : 1 ≤ d) : subA d 0 * Real.sqrt Real.pi ^ d = 1 / 2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hΓ : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hπ : 0 < Real.pi := Real.pi_pos
  unfold subA rieszConst
  simp only [if_true, sub_zero]
  have e1 : Real.sqrt Real.pi ^ d = Real.pi ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hπ.le]; congr 1; ring
  have e2 : (2 * Real.pi) ^ (-(d : ℝ)) = (2 : ℝ) ^ (-(d : ℝ)) * Real.pi ^ (-(d : ℝ)) :=
    Real.mul_rpow (by norm_num) hπ.le
  have e3 : (2 : ℝ) ^ ((d : ℝ) - 1) = (2 : ℝ) ^ (d : ℝ) / 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
  have e4 : Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ ((d : ℝ) / 2) = Real.pi ^ (d : ℝ) := by
    rw [← Real.rpow_add hπ]; congr 1; ring
  have e5 : (2 : ℝ) ^ (d : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have e6 : Real.pi ^ (d : ℝ) * Real.pi ^ (-(d : ℝ)) = 1 := by
    rw [← Real.rpow_add hπ]; simp
  rw [e1, show (0:ℝ) - d = -(d : ℝ) by ring, e2, e3]
  field_simp
  have := e4
  have h7 : (2 : ℝ) ^ (d : ℝ) * Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ ((d : ℝ) / 2) *
      ((2 : ℝ) ^ (-(d : ℝ)) * Real.pi ^ (-(d : ℝ))) = 1 := by
    calc _ = ((2 : ℝ) ^ (d : ℝ) * (2 : ℝ) ^ (-(d : ℝ))) *
          (Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ (-(d : ℝ))) := by ring
      _ = 1 := by rw [e5, e4, e6]; ring
  linear_combination h7




theorem int_main_pos (hs : 0 < s) {c : ℝ} (hc : 0 ≤ c) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ u in Ioc ε 1, u ^ (-s / 2 - 1) * (1 + c * u) ≤ (1 + c) * (2 / s) * ε ^ (-s / 2) := by
  have hcont : ContinuousOn (fun u : ℝ => u ^ (-s / 2 - 1)) (Icc ε 1) :=
    continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hε ht.1))
  have hint : IntegrableOn (fun u : ℝ => u ^ (-s / 2 - 1)) (Ioc ε 1) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h1 : ∫ u in Ioc ε 1, u ^ (-s / 2 - 1) * (1 + c * u) ≤ ∫ u in Ioc ε 1, (1 + c) * u ^ (-s / 2 - 1) := by
    refine setIntegral_mono_on ?_ (hint.const_mul _) measurableSet_Ioc ?_
    · have : ContinuousOn (fun u : ℝ => u ^ (-s / 2 - 1) * (1 + c * u)) (Icc ε 1) :=
        hcont.mul (by fun_prop)
      exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le hε hu.1.le
      have h3 := Real.rpow_pos_of_pos hu0 (-s / 2 - 1)
      have : 1 + c * u ≤ 1 + c := by nlinarith [hu.2]
      nlinarith
  refine h1.trans ?_
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hε1, integral_rpow
    (Or.inr ⟨by linarith, by rw [Set.uIcc_of_le hε1]; exact fun h => absurd h.1 (not_le.mpr hε)⟩)]
  have e : (-s / 2 - 1 + 1) = -s / 2 := by ring
  rw [e, Real.one_rpow]
  have hs2 : 0 < s / 2 := by positivity
  have h5 : 0 ≤ ε ^ (-s / 2) := Real.rpow_nonneg hε.le _
  have : (1 - ε ^ (-s / 2)) / (-s / 2) = (ε ^ (-s / 2) - 1) / (s / 2) := by
    field_simp; ring
  rw [this]
  have h6 : (ε ^ (-s / 2) - 1) / (s / 2) ≤ 2 / s * ε ^ (-s / 2) := by
    rw [div_le_iff₀ hs2]
    have : 2 / s * ε ^ (-s / 2) * (s / 2) = ε ^ (-s / 2) := by field_simp
    rw [this]; linarith
  calc (1 + c) * ((ε ^ (-s / 2) - 1) / (s / 2)) ≤ (1 + c) * (2 / s * ε ^ (-s / 2)) :=
        mul_le_mul_of_nonneg_left h6 (by linarith)
    _ = _ := by ring

theorem int_main_zero {c : ℝ} (hc : 0 ≤ c) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ u in Ioc ε 1, u ^ (-(0 : ℝ) / 2 - 1) * (1 + c * u) ≤ Real.log (1 / ε) + c := by
  have e : ∀ u : ℝ, u ^ (-(0 : ℝ) / 2 - 1) = u⁻¹ := by
    intro u; rw [show (-(0 : ℝ) / 2 - 1) = -1 by norm_num, Real.rpow_neg_one]
  simp_rw [e]
  have hform : ∀ u ∈ Ioc ε 1, u⁻¹ * (1 + c * u) = u⁻¹ + c := by
    intro u hu
    have : u ≠ 0 := ne_of_gt (lt_of_lt_of_le hε hu.1.le)
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioc hform, ← intervalIntegral.integral_of_le hε1,
    intervalIntegral.integral_add, integral_inv_of_pos hε one_pos]
  · simp only [intervalIntegral.integral_const, smul_eq_mul]
    have : c * (1 - ε) ≤ c := by nlinarith
    linarith
  · exact intervalIntegral.intervalIntegrable_inv (f := fun u : ℝ => u) (fun u hu => by
      rw [Set.uIcc_of_le hε1] at hu; exact ne_of_gt (lt_of_lt_of_le hε hu.1))
      continuousOn_id
  · exact intervalIntegrable_const




theorem gT_zero_le_pos (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → gT d s ε 0 ≤ C * ε ^ (-s / 2) := by
  have hA := subA_nonneg_one hd hs.le hsd
  have ha : 0 < ((d : ℝ) - s) / 2 := by linarith
  have hΓ := (Real.Gamma_pos_of_pos ha).le
  have hP : 0 ≤ Real.sqrt Real.pi ^ d := by positivity
  have hc := thC_nonneg d
  have hL := psiLargeC_nonneg d
  refine ⟨subA d s * (Real.sqrt Real.pi ^ d * ((1 + thC d) * (2 / s)) +
    psiLargeC d * Real.Gamma (((d : ℝ) - s) / 2)), by positivity, fun ε hε hε1 => ?_⟩
  refine (gT_zero_le hd hs.le hsd hε hε1).trans ?_
  have h1 := int_main_pos hs hc hε hε1
  have h2 : 1 ≤ ε ^ (-s / 2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)
  have h3 : 0 ≤ psiLargeC d * Real.Gamma (((d : ℝ) - s) / 2) := mul_nonneg hL hΓ
  calc subA d s * (Real.sqrt Real.pi ^ d * (∫ u in Ioc ε 1, u ^ (-s / 2 - 1) * (1 + thC d * u)) +
          psiLargeC d * Real.Gamma (((d : ℝ) - s) / 2))
      ≤ subA d s * (Real.sqrt Real.pi ^ d * ((1 + thC d) * (2 / s) * ε ^ (-s / 2)) +
          psiLargeC d * Real.Gamma (((d : ℝ) - s) / 2) * ε ^ (-s / 2)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h1 hP) ?_) hA
        nlinarith
    _ = _ := by ring

theorem gT_zero_le_zero (hd : 1 ≤ d) (hsd : (0 : ℝ) < d) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → gT d 0 ε 0 ≤ 1 / 2 * Real.log (1 / ε) + C := by
  have hA := subA_nonneg_one hd le_rfl hsd
  have ha : 0 < ((d : ℝ) - 0) / 2 := by linarith
  have hΓ := (Real.Gamma_pos_of_pos ha).le
  have hc := thC_nonneg d
  have hL := psiLargeC_nonneg d
  have hAP := subA_zero_mul hd
  refine ⟨1 / 2 * thC d + subA d 0 * (psiLargeC d * Real.Gamma (((d : ℝ) - 0) / 2)), fun ε hε hε1 => ?_⟩
  refine (gT_zero_le hd le_rfl hsd hε hε1).trans ?_
  have h1 := int_main_zero hc hε hε1
  have hP : 0 ≤ Real.sqrt Real.pi ^ d := by positivity
  have h3 : subA d 0 * (Real.sqrt Real.pi ^ d * ∫ u in Ioc ε 1, u ^ (-(0:ℝ) / 2 - 1) * (1 + thC d * u)) ≤
      subA d 0 * (Real.sqrt Real.pi ^ d * (Real.log (1 / ε) + thC d)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hP) hA
  have h4 : subA d 0 * (Real.sqrt Real.pi ^ d * (Real.log (1 / ε) + thC d)) =
      1 / 2 * (Real.log (1 / ε) + thC d) := by
    calc _ = (subA d 0 * Real.sqrt Real.pi ^ d) * (Real.log (1 / ε) + thC d) := by ring
      _ = _ := by rw [hAP]
  calc subA d 0 * (Real.sqrt Real.pi ^ d * (∫ u in Ioc ε 1, u ^ (-(0:ℝ) / 2 - 1) * (1 + thC d * u)) +
        psiLargeC d * Real.Gamma (((d : ℝ) - 0) / 2))
      = subA d 0 * (Real.sqrt Real.pi ^ d * (∫ u in Ioc ε 1, u ^ (-(0:ℝ) / 2 - 1) * (1 + thC d * u))) +
        subA d 0 * (psiLargeC d * Real.Gamma (((d : ℝ) - 0) / 2)) := by ring
    _ ≤ 1 / 2 * (Real.log (1 / ε) + thC d) + subA d 0 * (psiLargeC d * Real.Gamma (((d : ℝ) - 0) / 2)) := by
        rw [← h4]; linarith
    _ = _ := by ring




end CoercTrunc

section CoercFourier

open scoped ComplexConjugate

variable {d : ℕ}

/-- trigonometric sum `∑_k c_k cos(2πk·x)`. -/
def trigSum (c : Lattice d → ℝ) (x : Torus d) : ℝ := ∑' k : Lattice d, c k * Torus.cosMode k x

theorem mode_sub_conj (k : Lattice d) (x y : Torus d) :
    Torus.mode k (x - y) = Torus.mode k x * conj (Torus.mode k y) := by
  have h : Torus.mode k x = Torus.mode k (x - y) * Torus.mode k y := by
    rw [← Torus.mode_add_arg]; simp
  have h1 : Torus.mode k y * conj (Torus.mode k y) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mode]; simp
  calc Torus.mode k (x - y) = Torus.mode k (x - y) * (Torus.mode k y * conj (Torus.mode k y)) := by
        rw [h1, mul_one]
    _ = _ := by rw [h]; ring

theorem cosMode_sub (k : Lattice d) (x y : Torus d) :
    Torus.cosMode k (x - y) = (Torus.mode k x * conj (Torus.mode k y)).re := by
  unfold Torus.cosMode
  rw [mode_sub_conj]

theorem integral_tsum_c {c : Lattice d → ℝ} (hc : Summable fun k => |c k|) (P : Measure (Torus d))
    [IsFiniteMeasure P] (f : Lattice d → Torus d → ℝ) (hf : ∀ k, Continuous (f k)) {B : ℝ}
    (hb : ∀ k x, |f k x| ≤ B) :
    ∫ x, ∑' k, c k * f k x ∂P = ∑' k, c k * ∫ x, f k x ∂P := by
  have hint : ∀ k, Integrable (fun x => c k * f k x) P := fun k =>
    ((hf k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _
  have hnorm : Summable fun k => ∫ x, ‖c k * f k x‖ ∂P := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _)
      (fun k => ?_) (hc.mul_right (B * (P Set.univ).toReal))
    calc ∫ x, ‖c k * f k x‖ ∂P ≤ ∫ x, |c k| * B ∂P := by
          refine integral_mono (hint k).norm (integrable_const _) fun x => ?_
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left (hb k x) (abs_nonneg _)
      _ = |c k| * (B * (P Set.univ).toReal) := by
          rw [integral_const, smul_eq_mul, Measure.real]; ring
  rw [← integral_tsum_of_summable_integral_norm hint hnorm]
  refine tsum_congr fun k => ?_
  rw [integral_const_mul]

theorem integral_trigSum_sub {c : Lattice d → ℝ} (hc : Summable fun k => |c k|) (P Q : Measure (Torus d))
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    ∫ x, ∫ y, trigSum c (x - y) ∂Q ∂P =
      ∑' k, c k * ((∫ x, Torus.mode k x ∂P) * conj (∫ y, Torus.mode k y ∂Q)).re := by
  have hmint : ∀ (k : Lattice d) (R : Measure (Torus d)) [IsFiniteMeasure R],
      Integrable (Torus.mode k) R := fun k R _ =>
    (Torus.continuous_mode k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hinner : ∀ x, ∫ y, trigSum c (x - y) ∂Q =
      ∑' k, c k * (Torus.mode k x * conj (∫ y, Torus.mode k y ∂Q)).re := by
    intro x
    have h1 : ∀ y, trigSum c (x - y) = ∑' k, c k * (Torus.mode k x * conj (Torus.mode k y)).re := by
      intro y; unfold trigSum; simp_rw [cosMode_sub]
    simp_rw [h1]
    rw [integral_tsum_c hc Q (fun k y => (Torus.mode k x * conj (Torus.mode k y)).re)
      (fun k => by
        have := Torus.continuous_mode k
        fun_prop) (B := 1) (fun k y => by
          refine (Complex.abs_re_le_norm _).trans ?_
          rw [norm_mul, Complex.norm_conj, norm_mode, norm_mode]; simp)]
    refine tsum_congr fun k => ?_
    congr 1
    have := integral_re (μ := Q) (f := fun y => Torus.mode k x * conj (Torus.mode k y)) 
      (((Torus.continuous_mode k).comp continuous_id |>.star.const_mul _).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    simp only [RCLike.re_to_complex] at this
    rw [this, integral_const_mul, integral_conj]
  simp_rw [hinner]
  rw [integral_tsum_c hc P (fun k x => (Torus.mode k x * conj (∫ y, Torus.mode k y ∂Q)).re)
    (fun k => by
      have := Torus.continuous_mode k
      fun_prop) (B := (Q Set.univ).toReal) (fun k x => by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, Complex.norm_conj, norm_mode, one_mul]
        refine (norm_integral_le_integral_norm _).trans ?_
        simp [norm_mode, Measure.real])]
  refine tsum_congr fun k => ?_
  congr 1
  have := integral_re (μ := P) (f := fun x => Torus.mode k x * conj (∫ y, Torus.mode k y ∂Q))
    (((Torus.continuous_mode k).mul continuous_const).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  simp only [RCLike.re_to_complex] at this
  rw [this, integral_mul_const]




theorem integral_empirical_mode {N : ℕ} (hN : 0 < N) (X : Config d N) (k : Lattice d) :
    ∫ x, Torus.mode k x ∂(empirical X) = ((N : ℝ)⁻¹ : ℝ) • ∑ i, Torus.mode k (X i) := by
  unfold empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv]
  · intro i _
    exact integrable_dirac (by simp)

theorem integral_empirical_real {N : ℕ} (hN : 0 < N) (X : Config d N) (φ : Torus d → ℝ) :
    ∫ x, φ x ∂(empirical X) = (N : ℝ)⁻¹ * ∑ i, φ (X i) := pair_empirical hN X φ

theorem Q_eq_tsum {N : ℕ} (hN : 0 < N) {c : Lattice d → ℝ} (hc : Summable fun k => |c k|)
    (X : Config d N) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, trigSum c (X i - X j)
      - (2 / (N : ℝ)) * ∑ i, ∫ y, trigSum c (X i - y) ∂μ
      + ∫ x, ∫ y, trigSum c (x - y) ∂μ ∂μ =
    ∑' k, c k * ‖((N : ℝ)⁻¹ : ℝ) • ∑ i, Torus.mode k (X i) - ∫ x, Torus.mode k x ∂μ‖ ^ 2 := by
  haveI := empirical_isProbabilityMeasure hN X
  set ν := empirical X with hν
  have hnu : ∀ k, ∫ x, Torus.mode k x ∂ν = ((N : ℝ)⁻¹ : ℝ) • ∑ i, Torus.mode k (X i) :=
    integral_empirical_mode hN X
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  -- the three bilinear terms
  have hνν := integral_trigSum_sub hc ν ν
  have hνμ := integral_trigSum_sub hc ν μ
  have hμμ := integral_trigSum_sub hc μ μ
  have e1 : ∫ x, ∫ y, trigSum c (x - y) ∂ν ∂ν =
      (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, trigSum c (X i - X j) := by
    rw [integral_empirical_real hN X]
    have : ∀ i, ∫ y, trigSum c (X i - y) ∂ν = (N : ℝ)⁻¹ * ∑ j, trigSum c (X i - X j) := fun i =>
      integral_empirical_real hN X (fun y => trigSum c (X i - y))
    simp_rw [this]
    rw [← Finset.mul_sum, ← mul_assoc]
    congr 1
    field_simp
  have e2 : ∫ x, ∫ y, trigSum c (x - y) ∂μ ∂ν =
      (1 / (N : ℝ)) * ∑ i, ∫ y, trigSum c (X i - y) ∂μ := by
    rw [integral_empirical_real hN X]
    simp
  have e3 : (2 / (N : ℝ)) * ∑ i, ∫ y, trigSum c (X i - y) ∂μ =
      2 * ((1 / (N : ℝ)) * ∑ i, ∫ y, trigSum c (X i - y) ∂μ) := by ring
  rw [← e1, e3, ← e2, hνν, hνμ, hμμ]
  -- pointwise algebra and summability
  set z : Lattice d → ℂ := fun k => ∫ x, Torus.mode k x ∂ν with hz
  set w : Lattice d → ℂ := fun k => ∫ x, Torus.mode k x ∂μ with hw
  have hzn : ∀ k, ‖z k‖ ≤ 1 := fun k => by
    refine (norm_integral_le_integral_norm _).trans ?_
    simp [norm_mode]
  have hwn : ∀ k, ‖w k‖ ≤ 1 := fun k => by
    refine (norm_integral_le_integral_norm _).trans ?_
    simp [norm_mode]
  have hbd : ∀ (p q : ℂ), ‖p‖ ≤ 1 → ‖q‖ ≤ 1 → |(p * (starRingEnd ℂ) q).re| ≤ 1 := by
    intro p q hp hq
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg p, norm_nonneg q]
  have hs : ∀ p q : Lattice d → ℂ, (∀ k, ‖p k‖ ≤ 1) → (∀ k, ‖q k‖ ≤ 1) →
      Summable fun k => c k * (p k * (starRingEnd ℂ) (q k)).re := by
    intro p q hp hq
    refine Summable.of_norm_bounded hc fun k => ?_
    rw [Real.norm_eq_abs, abs_mul]
    calc |c k| * |(p k * (starRingEnd ℂ) (q k)).re| ≤ |c k| * 1 :=
          mul_le_mul_of_nonneg_left (hbd _ _ (hp k) (hq k)) (abs_nonneg _)
      _ = _ := mul_one _
  have h1 := hs z z hzn hzn
  have h2 := hs z w hzn hwn
  have h3 := hs w w hwn hwn
  have hpt : ∀ p q : ℂ, ‖p - q‖ ^ 2 = (p * (starRingEnd ℂ) p).re - 2 * (p * (starRingEnd ℂ) q).re
      + (q * (starRingEnd ℂ) q).re := by
    intro p q
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
    ring
  have hz' : ∀ k, ((N : ℝ)⁻¹ : ℝ) • ∑ i, Torus.mode k (X i) = z k := fun k => (hnu k).symm
  simp_rw [hz']
  have hrw : ∀ k, c k * ‖z k - ∫ x, Torus.mode k x ∂μ‖ ^ 2 =
      c k * (z k * (starRingEnd ℂ) (z k)).re - 2 * (c k * (z k * (starRingEnd ℂ) (w k)).re) +
        c k * (w k * (starRingEnd ℂ) (w k)).re := by
    intro k
    rw [hpt]
    simp only [hw]
    ring
  simp_rw [hrw]
  rw [Summable.tsum_add (h1.sub (h2.mul_left 2)) h3, Summable.tsum_sub h1 (h2.mul_left 2), tsum_mul_left]




section CoercNear

open Set KernelAux

variable {d : ℕ} {s : ℝ}

theorem measurable_periodicRiesz_one (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Measurable (periodicRiesz d s) := by
  let εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεn : Tendsto εn atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall fun n => by simp only [εn, Set.mem_Ioi]; positivity
  let f : ℕ → Torus d → ℝ := fun n x => if x = 0 then 0 else heatRiesz d s (εn n) x
  have hf : ∀ n, Measurable (f n) := fun n =>
    Measurable.ite (measurableSet_singleton (0 : Torus d)) measurable_const
      (_root_.HRS.continuous_heatRiesz hsd (εn n) (by simp only [εn]; positivity)).measurable
  let g' : Torus d → ℝ := fun x => if x = 0 then 0 else periodicRiesz d s x
  have hg' : Measurable g' := by
    refine measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.mpr fun x => ?_)
    by_cases hx : x = 0
    · simp [f, g', hx]
    · simp only [f, g', hx, if_false]
      exact (periodicRiesz_tendsto_one hd hs0 hsd x hx).comp hεn
  have : periodicRiesz d s = fun x => if x = 0 then periodicRiesz d s 0 else g' x := by
    funext x
    by_cases hx : x = 0
    · subst hx; simp
    · simp [g', hx]
  rw [this]
  exact Measurable.ite (measurableSet_singleton (0 : Torus d)) measurable_const hg'

/-- the near part `f_ε = g - g_ε` (with the value `0` at the origin). -/
def nearF (d : ℕ) (s ε : ℝ) (z : Torus d) : ℝ :=
  if z = 0 then 0 else periodicRiesz d s z - gT d s ε z

/-- the lower bound `B' = A ε^a / a` of the near part. -/
def nearB (d : ℕ) (s ε : ℝ) : ℝ :=
  subA d s * (ε ^ (((d : ℝ) - s) / 2) / (((d : ℝ) - s) / 2))

theorem nearB_nonneg (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ nearB d s ε := by
  have ha : 0 < ((d : ℝ) - s) / 2 := by linarith
  have := subA_nonneg_one hd hs0 hsd
  unfold nearB
  positivity

theorem nearF_ge (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (z : Torus d) :
    -nearB d s ε ≤ nearF d s ε z := by
  unfold nearF
  by_cases hz : z = 0
  · simp only [hz, ite_true]
    have := nearB_nonneg hd hs0 hsd hε
    linarith
  · simp only [hz, ite_false]
    exact near_ge hd hs0 hsd hε z hz

theorem periodicRiesz_eq_add {ε : ℝ} (z : Torus d) (hz : z ≠ 0) :
    periodicRiesz d s z = gT d s ε z + nearF d s ε z := by
  simp [nearF, hz]

theorem measurable_nearF (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    Measurable (nearF d s ε) := by
  unfold nearF
  exact Measurable.ite (measurableSet_singleton (0 : Torus d)) measurable_const
    ((measurable_periodicRiesz_one hd hs0 hsd).sub (continuous_gT hd hs0 hsd hε).measurable)

theorem integral_cosMode_of_ne (k : Lattice d) (hk : k ≠ 0) : ∫ x, Torus.cosMode k x = 0 := by
  have h := Torus.integral_mode k
  simp only [hk, if_false] at h
  unfold Torus.cosMode
  have hint : Integrable (Torus.mode k) (volume : Measure (Torus d)) :=
    (Torus.continuous_mode k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have := integral_re (μ := (volume : Measure (Torus d))) hint
  simp only [RCLike.re_to_complex] at this
  rw [this, h]; simp

theorem integral_gT (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    ∫ x, gT d s ε x = 0 := by
  have hc : Summable fun k => |cT d s ε k| := (summable_cT hd hs0 hsd hε).abs
  unfold gT
  rw [integral_tsum_c hc (volume : Measure (Torus d)) (fun k x => Torus.cosMode k x)
    (fun k => Torus.continuous_cosMode k) (B := 1) (fun k x => abs_cosMode_le k x)]
  have : ∀ k, cT d s ε k * ∫ x, Torus.cosMode k x = 0 := by
    intro k; by_cases hk : k = 0
    · simp [cT, hk]
    · rw [integral_cosMode_of_ne k hk, mul_zero]
  simp_rw [this]; exact tsum_zero

theorem integrable_nearF (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    Integrable (nearF d s ε) := by
  have hd0 : 0 < d := by omega
  have h1 := (integrable_periodicRiesz_one hd hs0 hsd).sub
    ((continuous_gT hd hs0 hsd hε).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  refine h1.congr ?_
  filter_upwards [torus_ae_ne hd0] with z hz
  simp [nearF, hz]

theorem integral_nearF (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    ∫ z, nearF d s ε z = 0 := by
  have hd0 : 0 < d := by omega
  have h1 : ∫ z, nearF d s ε z = ∫ z, (periodicRiesz d s z - gT d s ε z) := by
    refine integral_congr_ae ?_
    filter_upwards [torus_ae_ne hd0] with z hz
    simp [nearF, hz]
  rw [h1, integral_sub (integrable_periodicRiesz_one hd hs0 hsd)
    ((continuous_gT hd hs0 hsd hε).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    (integral_periodicRiesz_one hd hs0 hsd).2, integral_gT hd hs0 hsd hε]
  simp

end CoercNear




section CoercConv

open Set KernelAux2

variable {d : ℕ} {s : ℝ}

theorem integrable_conv_density {ρ : Torus d → ℝ} {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ)
    {φ : Torus d → ℝ} (hφm : Measurable φ) (hφ : Integrable φ) (x : Torus d) :
    Integrable (fun y => φ (x - y)) (withDensityReal ρ) := by
  refine ⟨(hφm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable, ?_⟩
  have h1 := lintegral_conv_le ρ Λ hΛ (fun z => ‖φ z‖ₑ) x
  have h2 := hφ.hasFiniteIntegral
  unfold HasFiniteIntegral at h2 ⊢
  exact lt_of_le_of_lt h1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2)

theorem integral_conv_density_le {ρ : Torus d → ℝ} {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ x, ρ x ≤ Λ)
    {φ : Torus d → ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hφm : Measurable φ) (hφ : Integrable φ) (x : Torus d) :
    ∫ y, φ (x - y) ∂(withDensityReal ρ) ≤ Λ * ∫ y, φ y := by
  have hint := integrable_conv_density hΛ hφm hφ x
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => hφ0 (x - y))
    (hφm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hφ0) hφm.aestronglyMeasurable]
  have h1 := lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal (φ z)) x
  have h2 : ∫⁻ y, ENNReal.ofReal (φ y) < ⊤ := hφ.lintegral_lt_top
  calc (∫⁻ y, ENNReal.ofReal (φ (x - y)) ∂(withDensityReal ρ)).toReal
      ≤ (ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal (φ y)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2.ne) h1
    _ = Λ * (∫⁻ y, ENNReal.ofReal (φ y)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hΛ0]

end CoercConv




section CoercEnergy

open Set KernelAux

variable {d : ℕ} {s : ℝ}

theorem nearF_conv_bounds (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ x, ρ x ≤ Λ)
    (x : Torus d) :
    Integrable (fun y => nearF d s ε (x - y)) (withDensityReal ρ) ∧
    -nearB d s ε ≤ ∫ y, nearF d s ε (x - y) ∂(withDensityReal ρ) ∧
    ∫ y, nearF d s ε (x - y) ∂(withDensityReal ρ) ≤ Λ * nearB d s ε := by
  haveI := isProb_withDensityReal hρ
  have hm := measurable_nearF hd hs0 hsd hε
  have hi := integrable_nearF hd hs0 hsd hε
  have hB := nearB_nonneg hd hs0 hsd hε
  have hint := integrable_conv_density hΛ hm hi x
  refine ⟨hint, ?_, ?_⟩
  · have := integral_mono (integrable_const (-nearB d s ε)) hint
      (fun y => nearF_ge hd hs0 hsd hε (x - y))
    simpa using this
  · set H : Torus d → ℝ := fun z => nearF d s ε z + nearB d s ε with hH
    have hH0 : ∀ z, 0 ≤ H z := fun z => by
      have := nearF_ge hd hs0 hsd hε z
      simp only [hH]; linarith
    have hHm : Measurable H := hm.add measurable_const
    have hHi : Integrable H := hi.add (integrable_const _)
    have h1 := integral_conv_density_le hΛ0 hΛ hH0 hHm hHi x
    have h2 : ∫ y, H y = nearB d s ε := by
      simp only [hH]
      rw [integral_add hi (integrable_const _), integral_nearF hd hs0 hsd hε]
      simp
    have h3 : ∫ y, H (x - y) ∂(withDensityReal ρ) =
        ∫ y, nearF d s ε (x - y) ∂(withDensityReal ρ) + nearB d s ε := by
      simp only [hH]
      rw [integral_add hint (integrable_const _)]
      simp
    rw [h2, h3] at h1
    nlinarith

theorem J_bounds (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ x, ρ x ≤ Λ)
    (x : Torus d) :
    Integrable (fun y => periodicRiesz d s (x - y)) (withDensityReal ρ) ∧
    ∫ y, gT d s ε (x - y) ∂(withDensityReal ρ) - nearB d s ε ≤
      ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) ∧
    ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) ≤
      ∫ y, gT d s ε (x - y) ∂(withDensityReal ρ) + Λ * nearB d s ε := by
  haveI := isProb_withDensityReal hρ
  obtain ⟨hint, hlo, hhi⟩ := nearF_conv_bounds hd hs0 hsd hε hρ hΛ0 hΛ x
  have hG : Integrable (fun y => gT d s ε (x - y)) (withDensityReal ρ) :=
    ((continuous_gT hd hs0 hsd hε).comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hae : ∀ᵐ y ∂(withDensityReal ρ), periodicRiesz d s (x - y) =
      gT d s ε (x - y) + nearF d s ε (x - y) := by
    have h0 : ∀ᵐ y ∂(volume : Measure (Torus d)), y ≠ x := by
      rw [ae_iff]
      have := volume_singleton_torus hd x
      simpa using this
    have h1 : ∀ᵐ y ∂(withDensityReal ρ), y ≠ x := withDensity_absolutelyContinuous _ _ h0
    filter_upwards [h1] with y hy
    exact periodicRiesz_eq_add (x - y) (sub_ne_zero.mpr (Ne.symm hy))
  have hI : Integrable (fun y => periodicRiesz d s (x - y)) (withDensityReal ρ) :=
    (hG.add hint).congr (hae.mono fun y hy => hy.symm)
  have heq : ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) =
      ∫ y, gT d s ε (x - y) ∂(withDensityReal ρ) + ∫ y, nearF d s ε (x - y) ∂(withDensityReal ρ) := by
    rw [integral_congr_ae hae, integral_add hG hint]
  refine ⟨hI, ?_, ?_⟩ <;> rw [heq] <;> linarith

end CoercEnergy




section CoercEnergy2

open Set KernelAux

variable {d : ℕ} {s : ℝ}

theorem rieszEnergy_ge_aux (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ x, ρ x ≤ Λ)
    {N : ℕ} (hN : 0 < N) (X : Config d N) (hX : X ∉ collisionSet d N) :
    1 / 2 * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, gT d s ε (X i - X j)
        - (2 / (N : ℝ)) * ∑ i, ∫ y, gT d s ε (X i - y) ∂(withDensityReal ρ)
        + ∫ x, ∫ y, gT d s ε (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ))
      - gT d s ε 0 / (2 * N) - (1 + Λ) * nearB d s ε ≤ rieszEnergy d s X (withDensityReal ρ) := by
  haveI := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  have hB := nearB_nonneg hd hs0 hsd hε
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hdist : ∀ i j : Fin N, i ≠ j → X i - X j ≠ 0 := by
    intro i j hij h
    exact hX ⟨i, j, hij, sub_eq_zero.mp h⟩
  -- the pair term
  have hT1 : ∀ i : Fin N, ∑ j, gT d s ε (X i - X j) - gT d s ε 0 - N * nearB d s ε ≤
      ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (X i - X j) := by
    intro i
    have h1 : ∀ j ∈ Finset.univ.erase i, gT d s ε (X i - X j) - nearB d s ε ≤
        periodicRiesz d s (X i - X j) := by
      intro j hj
      have hij : i ≠ j := fun h => (Finset.ne_of_mem_erase hj) h.symm
      rw [periodicRiesz_eq_add (ε := ε) (X i - X j) (hdist i j hij)]
      have := nearF_ge hd hs0 hsd hε (X i - X j)
      linarith
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_sub_distrib] at h2
    have h3 : ∑ j ∈ Finset.univ.erase i, gT d s ε (X i - X j) =
        ∑ j, gT d s ε (X i - X j) - gT d s ε 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp
    have h4 : ∑ j ∈ Finset.univ.erase i, nearB d s ε = ((N : ℝ) - 1) * nearB d s ε := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_sub hN]; simp
    rw [h3, h4] at h2
    nlinarith
  -- the cross term
  have hJ := fun x => J_bounds hd hs0 hsd hε hρ hΛ0 hΛ x
  have hT2 : ∑ i, ∫ y, periodicRiesz d s (X i - y) ∂μ ≤
      ∑ i, ∫ y, gT d s ε (X i - y) ∂μ + N * (Λ * nearB d s ε) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hJ (X i)).2.2)
    rw [Finset.sum_add_distrib] at this
    simpa using this
  -- the double integral term
  have hGc : Continuous (gT d s ε) := continuous_gT hd hs0 hsd hε
  have hIc : Continuous fun x => ∫ y, gT d s ε (x - y) ∂μ := continuous_conv0 hGc μ
  have hIint : Integrable (fun x => ∫ y, gT d s ε (x - y) ∂μ) μ :=
    hIc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hJm : StronglyMeasurable fun x => ∫ y, periodicRiesz d s (x - y) ∂μ :=
    StronglyMeasurable.integral_prod_right'
      (f := fun p : Torus d × Torus d => periodicRiesz d s (p.1 - p.2))
      ((measurable_periodicRiesz_one hd hs0 hsd).comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
  have hJint : Integrable (fun x => ∫ y, periodicRiesz d s (x - y) ∂μ) μ := by
    refine Integrable.mono' (hIint.norm.add (integrable_const ((1 + Λ) * nearB d s ε)))
      hJm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    obtain ⟨-, h1, h2⟩ := hJ x
    rw [Real.norm_eq_abs, abs_le]
    simp only [Pi.add_apply, Real.norm_eq_abs]
    have := neg_abs_le (∫ y, gT d s ε (x - y) ∂μ)
    have := le_abs_self (∫ y, gT d s ε (x - y) ∂μ)
    have : 0 ≤ Λ * nearB d s ε := mul_nonneg hΛ0 hB
    constructor <;> nlinarith
  have hT3 : ∫ x, ∫ y, gT d s ε (x - y) ∂μ ∂μ - nearB d s ε ≤
      ∫ x, ∫ y, periodicRiesz d s (x - y) ∂μ ∂μ := by
    have := integral_mono (hIint.sub (integrable_const (nearB d s ε))) hJint
      (fun x => (hJ x).2.1)
    simp only [Pi.sub_apply] at this
    rw [integral_sub hIint (integrable_const _)] at this
    simpa using this
  -- assemble
  unfold rieszEnergy modulatedEnergyKernel modulatedEnergy
  have hsum1 : ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (X i - X j) ≥
      ∑ i, ∑ j, gT d s ε (X i - X j) - N * gT d s ε 0 - N * (N * nearB d s ε) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hT1 i)
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at this
    simpa using this
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  show 1 / 2 * (1 / (N : ℝ) ^ 2 * ∑ i, ∑ j, gT d s ε (X i - X j) -
        2 / (N : ℝ) * ∑ i, ∫ y, gT d s ε (X i - y) ∂μ +
        ∫ x, ∫ y, gT d s ε (x - y) ∂μ ∂μ) - gT d s ε 0 / (2 * N) - (1 + Λ) * nearB d s ε ≤
      1 / (2 * (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (X i - X j) -
        1 / (N : ℝ) * ∑ i, ∫ y, periodicRiesz d s (X i - y) ∂μ +
        1 / 2 * ∫ x, ∫ y, periodicRiesz d s (x - y) ∂μ ∂μ
  set SG := ∑ i, ∑ j, gT d s ε (X i - X j)
  set I1 := ∑ i, ∫ y, gT d s ε (X i - y) ∂μ
  set D := ∫ x, ∫ y, gT d s ε (x - y) ∂μ ∂μ
  set G0 := gT d s ε 0
  set B := nearB d s ε
  have a1 : 1 / (2 * (N : ℝ) ^ 2) * (SG - N * G0 - N * (N * B)) ≤
      1 / (2 * (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (X i - X j) :=
    mul_le_mul_of_nonneg_left hsum1 (by positivity)
  have a2 : 1 / (N : ℝ) * ∑ i, ∫ y, periodicRiesz d s (X i - y) ∂μ ≤
      1 / (N : ℝ) * (I1 + N * (Λ * B)) :=
    mul_le_mul_of_nonneg_left hT2 (by positivity)
  have key : 1 / (2 * (N : ℝ) ^ 2) * (SG - N * G0 - N * (N * B)) -
      1 / (N : ℝ) * (I1 + N * (Λ * B)) + 1 / 2 * (D - B) =
      1 / 2 * (1 / (N : ℝ) ^ 2 * SG - 2 / (N : ℝ) * I1 + D) - G0 / (2 * N) - (1 + Λ) * B := by
    field_simp
    ring
  nlinarith [hT3]

end CoercEnergy2




section CoercScale

variable {d : ℕ} {s : ℝ}

theorem smearScale_pos {N : ℕ} {Λ : ℝ} (hN : 1 ≤ N) (hΛ : 0 < Λ) : 0 < smearScale d N Λ := by
  unfold smearScale
  have : (0 : ℝ) < N := by exact_mod_cast hN
  exact Real.rpow_pos_of_pos (by positivity) _

theorem smearScale_lt_one (hd : 1 ≤ d) {N : ℕ} {Λ : ℝ} (hNΛ : 1 < (N : ℝ) * Λ) :
    smearScale d N Λ < 1 := by
  unfold smearScale
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := hd0.ne'
  exact Real.rpow_lt_one_of_one_lt_of_neg hNΛ (by
    have : (0:ℝ) < 1 / d := by positivity
    have e : -(1 : ℝ) / d = -(1 / d) := by ring
    rw [e]; linarith)

theorem smearScale_sq_rpow (hd : 1 ≤ d) {N : ℕ} {Λ : ℝ} (hq : 0 < (N : ℝ) * Λ) (r : ℝ) :
    (smearScale d N Λ ^ 2) ^ r = ((N : ℝ) * Λ) ^ (-2 * r / d) := by
  unfold smearScale
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := hd0.ne'
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le]
  congr 1
  push_cast
  field_simp

theorem smear_a_eq (hd : 1 ≤ d) {N : ℕ} {Λ : ℝ} (hN : 1 ≤ N) (hΛ : 0 < Λ) :
    Λ * (smearScale d N Λ ^ 2) ^ (((d : ℝ) - s) / 2) = Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 < (N : ℝ) * Λ := by positivity
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := hd0.ne'
  rw [smearScale_sq_rpow hd hq]
  have e : -2 * (((d : ℝ) - s) / 2) / d = s / d - 1 := by field_simp; ring
  rw [e, Real.mul_rpow hN0.le hΛ.le]
  have : Λ * Λ ^ (s / d - 1) = Λ ^ (s / d) := by
    calc Λ * Λ ^ (s / d - 1) = Λ ^ (1 : ℝ) * Λ ^ (s / d - 1) := by rw [Real.rpow_one]
      _ = Λ ^ (1 + (s / d - 1)) := (Real.rpow_add hΛ _ _).symm
      _ = _ := by congr 1; ring
  calc Λ * ((N : ℝ) ^ (s / d - 1) * Λ ^ (s / d - 1)) = (Λ * Λ ^ (s / d - 1)) * (N : ℝ) ^ (s / d - 1) := by ring
    _ = _ := by rw [this]

theorem smear_neg_eq (hd : 1 ≤ d) {N : ℕ} {Λ : ℝ} (hN : 1 ≤ N) (hΛ : 0 < Λ) :
    (smearScale d N Λ ^ 2) ^ (-s / 2) / (N : ℝ) = Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 < (N : ℝ) * Λ := by positivity
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := hd0.ne'
  rw [smearScale_sq_rpow hd hq]
  have e : -2 * (-s / 2) / d = s / d := by field_simp
  rw [e, Real.mul_rpow hN0.le hΛ.le, Real.rpow_sub hN0, Real.rpow_one]
  field_simp

theorem smear_log_eq (hd : 1 ≤ d) {N : ℕ} {Λ : ℝ} (hN : 1 ≤ N) (hΛ : 0 < Λ) :
    Real.log (1 / smearScale d N Λ ^ 2) = 2 / d * Real.log ((N : ℝ) * Λ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 < (N : ℝ) * Λ := by positivity
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := hd0.ne'
  have hl := smearScale_pos (d := d) hN hΛ
  unfold smearScale
  rw [one_div, Real.log_inv, Real.log_pow, Real.log_rpow hq]
  push_cast
  field_simp

end CoercScale



section CoercConst

open Set KernelAux

variable {d : ℕ} {s : ℝ}

theorem diag_const (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      gT d s (smearScale d N Λ ^ 2) 0 / (2 * N) + (1 + Λ) * nearB d s (smearScale d N Λ ^ 2) ≤
        oNΛ d s C₀ Λ N := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 0 < ((d : ℝ) - s) / 2 := by linarith
  have hA := subA_nonneg_one hd hs0 hsd
  -- the `nearB` part
  have hnear : ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      (1 + Λ) * nearB d s (smearScale d N Λ ^ 2) ≤
        (2 * subA d s / (((d : ℝ) - s) / 2)) * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) := by
    intro Λ hΛ N hN
    have hN1 : 1 ≤ N := by omega
    have hΛ0 : 0 < Λ := by linarith
    have hB := nearB_nonneg hd hs0 hsd (ε := smearScale d N Λ ^ 2)
      (by have := smearScale_pos (d := d) hN1 hΛ0; positivity)
    rw [← smear_a_eq (s := s) hd hN1 hΛ0]
    unfold nearB at hB ⊢
    have : (1 + Λ) * (subA d s * ((smearScale d N Λ ^ 2) ^ (((d : ℝ) - s) / 2) / (((d : ℝ) - s) / 2))) ≤
        (2 * Λ) * (subA d s * ((smearScale d N Λ ^ 2) ^ (((d : ℝ) - s) / 2) / (((d : ℝ) - s) / 2))) :=
      mul_le_mul_of_nonneg_right (by linarith) hB
    refine this.trans (le_of_eq ?_)
    field_simp
  have hq : ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      0 < smearScale d N Λ ^ 2 ∧ smearScale d N Λ ^ 2 ≤ 1 := by
    intro Λ hΛ N hN
    have hN1 : 1 ≤ N := by omega
    have hΛ0 : 0 < Λ := by linarith
    have hNΛ : 1 < (N : ℝ) * Λ := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    have h1 := smearScale_pos (d := d) hN1 hΛ0
    have h2 := smearScale_lt_one hd hNΛ
    exact ⟨by positivity, by nlinarith⟩
  by_cases hs : s = 0
  · subst hs
    obtain ⟨C, hC⟩ := gT_zero_le_zero (d := d) hd hd0
    refine ⟨max C 0 / 2 + 2 * subA d 0 / (((d : ℝ) - 0) / 2), by positivity, fun Λ hΛ N hN => ?_⟩
    have hN1 : 1 ≤ N := by omega
    have hΛ0 : 0 < Λ := by linarith
    obtain ⟨hq0, hq1⟩ := hq Λ hΛ N hN
    have h1 := hC _ hq0 hq1
    rw [smear_log_eq hd hN1 hΛ0] at h1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have h2 := hnear Λ hΛ N hN
    have hone : Λ ^ ((0 : ℝ) / d) = 1 := by rw [zero_div, Real.rpow_zero]
    have e : (N : ℝ) ^ ((0 : ℝ) / d - 1) = (N : ℝ)⁻¹ := by
      rw [zero_div, zero_sub, Real.rpow_neg_one]
    rw [hone, e] at h2
    have h3 : gT d 0 (smearScale d N Λ ^ 2) 0 / (2 * N) ≤
        Real.log (N * Λ) / (2 * d * N) + max C 0 / 2 * (N : ℝ)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      have : Real.log (N * Λ) / (2 * d * N) * (2 * N) = 1 / d * Real.log (N * Λ) := by
        field_simp
      have h4 : C ≤ max C 0 := le_max_left _ _
      have h5 : max C 0 / 2 * (N : ℝ)⁻¹ * (2 * N) = max C 0 := by field_simp
      calc gT d 0 (smearScale d N Λ ^ 2) 0 ≤ 1 / 2 * (2 / d * Real.log (N * Λ)) + C := h1
        _ ≤ 1 / d * Real.log (N * Λ) + max C 0 := by
            have : 1 / 2 * (2 / (d : ℝ) * Real.log (N * Λ)) = 1 / d * Real.log (N * Λ) := by ring
            rw [this]; linarith
        _ = _ := by rw [add_mul, this, h5]
    unfold oNΛ
    rw [if_pos rfl, hone, e]
    have h6 : (max C 0 / 2 + 2 * subA d 0 / (((d : ℝ) - 0) / 2)) * 1 * (N : ℝ)⁻¹ =
        max C 0 / 2 * (N : ℝ)⁻¹ + 2 * subA d 0 / (((d : ℝ) - 0) / 2) * (1 * (N : ℝ)⁻¹) := by ring
    rw [h6]
    linarith
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    obtain ⟨C, hC0, hC⟩ := gT_zero_le_pos hd hspos hsd
    refine ⟨C / 2 + 2 * subA d s / (((d : ℝ) - s) / 2), by positivity, fun Λ hΛ N hN => ?_⟩
    have hN1 : 1 ≤ N := by omega
    have hΛ0 : 0 < Λ := by linarith
    obtain ⟨hq0, hq1⟩ := hq Λ hΛ N hN
    have h1 := hC _ hq0 hq1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have h2 := hnear Λ hΛ N hN
    have h3 : gT d s (smearScale d N Λ ^ 2) 0 / (2 * N) ≤
        C / 2 * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) := by
      rw [div_le_iff₀ (by positivity)]
      have h5 := smear_neg_eq (s := s) hd hN1 hΛ0
      have h6 : (smearScale d N Λ ^ 2) ^ (-s / 2) = (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) * N := by
        rw [← h5]; field_simp
      calc gT d s (smearScale d N Λ ^ 2) 0 ≤ C * (smearScale d N Λ ^ 2) ^ (-s / 2) := h1
        _ = C / 2 * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) * (2 * N) := by rw [h6]; ring
    unfold oNΛ
    rw [if_neg hs, zero_add]
    have h7 : (C / 2 + 2 * subA d s / (((d : ℝ) - s) / 2)) * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) =
        C / 2 * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) +
          2 * subA d s / (((d : ℝ) - s) / 2) * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) := by ring
    rw [h7]
    linarith

end CoercConst


section CoercMain

open Set KernelAux

variable {d : ℕ} {s : ℝ}

/-- the Fourier form `E_ε(ρ) = ∑_k ĝ_ε(k) |ρ̂(k)|²` of the signed measure `μ_N - μ`. -/
def Esq (d : ℕ) (s ε : ℝ) {N : ℕ} (X : Config d N) (μ : Measure (Torus d)) : ℝ :=
  ∑' k : Lattice d, cT d s ε k *
    ‖((N : ℝ)⁻¹ : ℝ) • ∑ i, Torus.mode k (X i) - ∫ x, Torus.mode k x ∂μ‖ ^ 2

theorem Esq_nonneg (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (X : Config d N) (μ : Measure (Torus d)) : 0 ≤ Esq d s ε X μ :=
  tsum_nonneg fun k => mul_nonneg (cT_nonneg hd hs0 hsd hε k) (sq_nonneg _)

theorem coercivity_energy (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ Esq d s (smearScale d N Λ ^ 2) X (withDensityReal ρ) ∧
        Esq d s (smearScale d N Λ ^ 2) X (withDensityReal ρ) ≤
          2 * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  obtain ⟨C₀, hC₀, hconst⟩ := diag_const hd hs0 hsd
  refine ⟨C₀, hC₀, fun Λ hΛ N hN ρ hρ hρΛ X hX => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hΛ0 : 0 < Λ := by linarith
  have hε : 0 < smearScale d N Λ ^ 2 := by
    have := smearScale_pos (d := d) hN1 hΛ0; positivity
  haveI := isProb_withDensityReal hρ
  have hQ := Q_eq_tsum (c := cT d s (smearScale d N Λ ^ 2)) (by omega) 
    ((summable_cT hd hs0 hsd hε).abs) X (withDensityReal ρ)
  have hge := rieszEnergy_ge_aux hd hs0 hsd hε hρ hΛ0.le hρΛ (by omega) X hX
  have hc := hconst Λ hΛ N hN
  have hQ' : Esq d s (smearScale d N Λ ^ 2) X (withDensityReal ρ) =
      (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, gT d s (smearScale d N Λ ^ 2) (X i - X j)
        - (2 / (N : ℝ)) * ∑ i, ∫ y, gT d s (smearScale d N Λ ^ 2) (X i - y) ∂(withDensityReal ρ)
        + ∫ x, ∫ y, gT d s (smearScale d N Λ ^ 2) (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) :=
    hQ.symm
  refine ⟨Esq_nonneg hd hs0 hsd hε X _, ?_⟩
  rw [hQ']
  linarith

end CoercMain


section CoercHeat

open Set KernelAux

variable {d : ℕ} {s : ℝ}

/-- the periodic heat kernel `p_t(y) = ∑_k e^{-t|k|²} cos(2π k·y)`. -/
def heatK (d : ℕ) (t : ℝ) (y : Torus d) : ℝ :=
  ∑' k : Lattice d, Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k y

theorem summable_heatK_coef {t : ℝ} (ht : 0 < t) :
    Summable fun k : Lattice d => |Real.exp (-t * Lattice.enorm k ^ 2)| := by
  refine (summable_gauss_lattice d t ht).congr fun k => ?_
  rw [abs_of_pos (Real.exp_pos _)]

theorem continuous_heatK {t : ℝ} (ht : 0 < t) : Continuous (heatK d t) := by
  unfold heatK
  refine continuous_tsum (u := fun k : Lattice d => Real.exp (-t * Lattice.enorm k ^ 2))
    (fun k => continuous_const.mul (Torus.continuous_cosMode k)) (summable_gauss_lattice d t ht)
    (fun k x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-t * Lattice.enorm k ^ 2) * |Torus.cosMode k x|
      ≤ Real.exp (-t * Lattice.enorm k ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (abs_cosMode_le k x) (Real.exp_pos _).le
    _ = _ := mul_one _

theorem heatK_nonneg {t : ℝ} (ht : 0 < t) (y : Torus d) : 0 ≤ heatK d t y :=
  theta_nonneg y ht

theorem integral_heatK {t : ℝ} (ht : 0 < t) : ∫ y, heatK d t y = 1 := by
  unfold heatK
  rw [integral_tsum_c (summable_heatK_coef ht) (volume : Measure (Torus d))
    (fun k x => Torus.cosMode k x) (fun k => Torus.continuous_cosMode k) (B := 1)
    (fun k x => abs_cosMode_le k x)]
  have : ∀ k : Lattice d, Real.exp (-t * Lattice.enorm k ^ 2) * ∫ x, Torus.cosMode k x =
      if k = 0 then 1 else 0 := by
    intro k
    by_cases hk : k = 0
    · subst hk
      have h1 : ∫ x : Torus d, Torus.cosMode (0 : Lattice d) x = 1 := by simp [cosMode_zero]
      have h0 : Lattice.enorm (0 : Lattice d) = 0 := by
        simp [Lattice.enorm, Lattice.toEuc]; rfl
      simp [h1, h0]
    · simp [hk, integral_cosMode_of_ne k hk]
  simp_rw [this]
  rw [tsum_ite_eq]



theorem integral_Box_prod (f : Fin d → ℝ → ℝ) :
    ∫ y in Box d, ∏ i, f i (y i) = ∏ i, ∫ x in Ioc (-1 / 2 : ℝ) (-1 / 2 + 1), f i x := by
  have h : Box d = Set.univ.pi fun _ => Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) := by
    ext y; simp [Box]
  rw [h, volume_pi, Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod (fun i x => f i x)

theorem integral_gauss' (b : ℝ) :
    ∫ x : ℝ, Real.exp (-(b * x ^ 2)) = Real.sqrt (Real.pi / b) := by
  have := integral_gaussian b
  simpa only [neg_mul] using this

theorem gauss_int_le {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioc (-1 / 2 : ℝ) (-1 / 2 + 1), Real.exp (-(b * x ^ 2)) ≤ Real.sqrt (Real.pi / b) := by
  have hi : Integrable (fun x : ℝ => Real.exp (-(b * x ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq hb
  have := setIntegral_le_integral (μ := (volume : Measure ℝ)) (s := Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)) hi
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
  rw [integral_gauss'] at this
  exact this

theorem abs_mul_exp_le' {b : ℝ} (hb : 0 < b) (x : ℝ) :
    |x| * Real.exp (-(b / 2 * x ^ 2)) ≤ 1 / Real.sqrt b := by
  set y := Real.sqrt b * |x| with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : y ≤ Real.exp (y ^ 2 / 2) := by
    have := Real.add_one_le_exp (y ^ 2 / 2)
    nlinarith [sq_nonneg (y - 1)]
  have h2 : y ^ 2 = b * x ^ 2 := by
    rw [hy, mul_pow, Real.sq_sqrt hb.le, sq_abs]
  have h3 : y * Real.exp (-(y ^ 2 / 2)) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact h1
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  rw [h2] at h3
  have e : -(b * x ^ 2 / 2) = -(b / 2 * x ^ 2) := by ring
  rw [e] at h3
  rw [le_div_iff₀ hs]
  calc |x| * Real.exp (-(b / 2 * x ^ 2)) * Real.sqrt b = (Real.sqrt b * |x|) * Real.exp (-(b / 2 * x ^ 2)) := by ring
    _ = y * Real.exp (-(b / 2 * x ^ 2)) := rfl
    _ ≤ 1 := h3

theorem gauss_mom_le {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioc (-1 / 2 : ℝ) (-1 / 2 + 1), |x| * Real.exp (-(b * x ^ 2)) ≤
      Real.sqrt (2 * Real.pi) / b := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hi : Integrable (fun x : ℝ => Real.exp (-(b / 2 * x ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (show 0 < b / 2 by positivity)
  have hcont : Continuous fun x : ℝ => |x| * Real.exp (-(b * x ^ 2)) := by fun_prop
  calc ∫ x in Ioc (-1 / 2 : ℝ) (-1 / 2 + 1), |x| * Real.exp (-(b * x ^ 2))
      ≤ ∫ x in Ioc (-1 / 2 : ℝ) (-1 / 2 + 1), (1 / Real.sqrt b) * Real.exp (-(b / 2 * x ^ 2)) := by
        refine setIntegral_mono_on (hcont.integrableOn_Ioc) (hi.const_mul _).integrableOn
          measurableSet_Ioc fun x _ => ?_
        have h1 := abs_mul_exp_le' hb x
        have h2 : Real.exp (-(b * x ^ 2)) = Real.exp (-(b / 2 * x ^ 2)) * Real.exp (-(b / 2 * x ^ 2)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [h2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ ∫ x : ℝ, (1 / Real.sqrt b) * Real.exp (-(b / 2 * x ^ 2)) :=
        setIntegral_le_integral (hi.const_mul _)
          (Filter.Eventually.of_forall fun x => by positivity)
    _ = Real.sqrt (2 * Real.pi) / b := by
        rw [integral_const_mul, integral_gauss']
        have : Real.sqrt (Real.pi / (b / 2)) = Real.sqrt (2 * Real.pi) / Real.sqrt b := by
          rw [← Real.sqrt_div (by positivity)]; congr 1; field_simp
        rw [this]
        have hbb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
        field_simp
        nlinarith



/-- constant `B = ∑_n e^{-π² n²/8}` -/
def thetaB : ℝ := ∑' n : ℤ, Real.exp (-(Real.pi ^ 2 / 8) * (n : ℝ) ^ 2)

theorem thetaB_nonneg : 0 ≤ thetaB := tsum_nonneg fun _ => (Real.exp_pos _).le

/-- Gaussian majorant of the one-dimensional theta factor -/
def Gt (t y : ℝ) : ℝ :=
  Real.sqrt (Real.pi / t) * thetaB * Real.exp (-(Real.pi ^ 2 / (2 * t) * y ^ 2))

theorem Gt_nonneg (t y : ℝ) : 0 ≤ Gt t y := by
  unfold Gt
  have := thetaB_nonneg
  positivity

theorem heatK_boxPt_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) {y : Fin d → ℝ} (hy : ∀ i, |y i| ≤ 1 / 2) :
    0 ≤ heatK d t (boxPt y) ∧ heatK d t (boxPt y) ≤ ∏ i, Gt t (y i) := by
  have h := theta_prod y ht
  unfold heatK
  rw [h]
  have hb := fun i => theta_factor_bound (y i) (hy i) ht ht1
  refine ⟨Finset.prod_nonneg fun i _ => (hb i).1, Finset.prod_le_prod₀ (fun i _ => (hb i).1)
    (fun i _ => ?_)⟩
  refine (hb i).2.trans (le_of_eq ?_)
  unfold Gt thetaB
  congr 2
  congr 1
  ring

theorem Gt_int_le {t : ℝ} (ht : 0 < t) :
    ∫ y in Ioc (-1 / 2 : ℝ) (-1 / 2 + 1), Gt t y ≤ Real.sqrt 2 * thetaB := by
  have hb : 0 < Real.pi ^ 2 / (2 * t) := by positivity
  have h := gauss_int_le hb
  have hK : 0 ≤ Real.sqrt (Real.pi / t) * thetaB := by have := thetaB_nonneg; positivity
  have e : ∀ y : ℝ, Gt t y = (Real.sqrt (Real.pi / t) * thetaB) *
      Real.exp (-(Real.pi ^ 2 / (2 * t) * y ^ 2)) := fun y => rfl
  simp_rw [e]
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left h hK).trans (le_of_eq ?_)
  have h1 : Real.pi / (Real.pi ^ 2 / (2 * t)) = 2 * t / Real.pi := by
    field_simp
  rw [h1, mul_comm (Real.sqrt (Real.pi / t)), mul_assoc, ← Real.sqrt_mul (by positivity)]
  have h2 : Real.pi / t * (2 * t / Real.pi) = 2 := by field_simp
  rw [h2]; ring

theorem Gt_mom_le {t : ℝ} (ht : 0 < t) :
    ∫ y in Ioc (-1 / 2 : ℝ) (-1 / 2 + 1), |y| * Gt t y ≤
      (2 * Real.sqrt 2 / Real.pi * thetaB) * Real.sqrt t := by
  have hb : 0 < Real.pi ^ 2 / (2 * t) := by positivity
  have h := gauss_mom_le hb
  have hK : 0 ≤ Real.sqrt (Real.pi / t) * thetaB := by have := thetaB_nonneg; positivity
  have e : ∀ y : ℝ, |y| * Gt t y = (Real.sqrt (Real.pi / t) * thetaB) *
      (|y| * Real.exp (-(Real.pi ^ 2 / (2 * t) * y ^ 2))) := fun y => by unfold Gt; ring
  simp_rw [e]
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left h hK).trans (le_of_eq ?_)
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hπ : 0 < Real.pi := Real.pi_pos
  have e1 : Real.sqrt (Real.pi / t) = Real.sqrt Real.pi / Real.sqrt t := Real.sqrt_div hπ.le t
  have e2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := Real.sqrt_mul (by norm_num) _
  have e3 : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt hπ.le
  have e4 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  rw [e1, e2]
  field_simp
  rw [Real.sq_sqrt hπ.le, Real.sq_sqrt ht.le]
  ring



theorem norm_toLp_le_sum_abs (y : Fin d → ℝ) : ‖(WithLp.toLp 2 y : Euc d)‖ ≤ ∑ i, |y i| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |y i|)
    (fun i _ => abs_nonneg _)
  simpa [sq_abs] using this

theorem Box_subset_Icc (d : ℕ) :
    Box d ⊆ Set.Icc (fun _ : Fin d => (-1 / 2 : ℝ)) (fun _ => 1 / 2) := by
  intro y hy
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> have := Box_abs_le hy i <;> rw [abs_le] at this <;> linarith [this.1, this.2]

theorem centeredRep_boxPt {y : Fin d → ℝ} (hy : ∀ i, |y i| ≤ 1 / 2) :
    ‖KernelGrad.centeredRep (boxPt y)‖ = ‖(WithLp.toLp 2 y : Euc d)‖ := by
  have h := KernelGrad.tdist_mk (d := d) (y := (WithLp.toLp 2 y : Euc d)) hy
  rw [KernelGrad.tdist_zero_right] at h
  exact h

/-- the factors of the first-moment majorant -/
def gMom (t : ℝ) (j i : Fin d) (y : ℝ) : ℝ := Gt t y * (if i = j then |y| else 1)

theorem gMom_nonneg (t : ℝ) (j i : Fin d) (y : ℝ) : 0 ≤ gMom t j i y := by
  unfold gMom
  have := Gt_nonneg t y
  split_ifs <;> positivity

theorem continuous_Gt (t : ℝ) : Continuous (Gt t) := by
  unfold Gt; fun_prop

theorem continuous_gMom (t : ℝ) (j i : Fin d) : Continuous (gMom t j i) := by
  unfold gMom
  by_cases h : i = j
  · simp only [h, ite_true]; have := continuous_Gt t; fun_prop
  · simp only [h, ite_false]; have := continuous_Gt t; fun_prop

theorem gMom_int_le {t : ℝ} (ht : 0 < t) (j i : Fin d) :
    ∫ y in Ioc (-1 / 2 : ℝ) (-1 / 2 + 1), gMom t j i y ≤
      if i = j then (2 * Real.sqrt 2 / Real.pi * thetaB) * Real.sqrt t else Real.sqrt 2 * thetaB := by
  by_cases h : i = j
  · simp only [h, ite_true]
    refine le_trans (le_of_eq ?_) (Gt_mom_le ht)
    refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
    simp only [gMom, ite_true]; ring
  · simp only [h, ite_false]
    refine le_trans (le_of_eq ?_) (Gt_int_le ht)
    refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
    simp only [gMom, h, ite_false, mul_one]

theorem heat_moment (hd : 1 ≤ d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∫ y : Torus d, heatK d t y * ‖KernelGrad.centeredRep y‖ ≤ M * Real.sqrt t := by
  have hB := thetaB_nonneg
  refine ⟨d * (Real.sqrt 2 * thetaB) ^ (d - 1) * (2 * Real.sqrt 2 / Real.pi * thetaB), by positivity,
    fun t ht ht1 => ?_⟩
  rw [integral_torus_box]
  set M₁ := Real.sqrt 2 * thetaB with hM₁
  set M₂ := (2 * Real.sqrt 2 / Real.pi * thetaB) * Real.sqrt t with hM₂
  have hpt : ∀ y ∈ Box d, heatK d t (boxPt y) * ‖KernelGrad.centeredRep (boxPt y)‖ ≤
      ∑ j, ∏ i, gMom t j i (y i) := by
    intro y hy
    have hy' := Box_abs_le hy
    obtain ⟨h0, h1⟩ := heatK_boxPt_le ht ht1 hy'
    rw [centeredRep_boxPt hy']
    have hn : ‖(WithLp.toLp 2 y : Euc d)‖ ≤ ∑ i, |y i| := norm_toLp_le_sum_abs y
    have hprod0 : 0 ≤ ∏ i, Gt t (y i) := Finset.prod_nonneg fun i _ => Gt_nonneg t _
    have e : ∑ j, ∏ i, gMom t j i (y i) = (∏ i, Gt t (y i)) * ∑ j, |y j| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [gMom]
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [← Finset.mul_prod_erase Finset.univ (fun i => if i = j then |y i| else 1) (Finset.mem_univ j)]
      simp only [ite_true]
      rw [Finset.prod_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi))]
      simp
    rw [e]
    calc heatK d t (boxPt y) * ‖(WithLp.toLp 2 y : Euc d)‖
        ≤ (∏ i, Gt t (y i)) * ‖(WithLp.toLp 2 y : Euc d)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hn hprod0
  have hcontj : ∀ j, Continuous fun y : Fin d → ℝ => ∏ i, gMom t j i (y i) := fun j =>
    continuous_finset_prod _ fun i _ => (continuous_gMom t j i).comp (continuous_apply i)
  have hIcc : ∀ {f : (Fin d → ℝ) → ℝ}, Continuous f → IntegrableOn f (Box d) := fun hf =>
    (hf.integrableOn_Icc (a := fun _ : Fin d => (-1 / 2 : ℝ)) (b := fun _ => 1 / 2)).mono_set
      (Box_subset_Icc d)
  have hfint : IntegrableOn (fun y : Fin d → ℝ =>
      heatK d t (boxPt y) * ‖KernelGrad.centeredRep (boxPt y)‖) (Box d) := by
    have hc : Continuous fun y : Fin d → ℝ => heatK d t (boxPt y) * ‖(WithLp.toLp 2 y : Euc d)‖ :=
      ((continuous_heatK ht).comp (continuous_boxPt d)).mul
        (continuous_norm.comp (by fun_prop))
    refine (hIcc hc).congr_fun (fun y hy => ?_) (measurableSet_Box d)
    simp only
    rw [centeredRep_boxPt (Box_abs_le hy)]
  calc ∫ y in Box d, heatK d t (boxPt y) * ‖KernelGrad.centeredRep (boxPt y)‖
      ≤ ∫ y in Box d, ∑ j, ∏ i, gMom t j i (y i) :=
        setIntegral_mono_on hfint (integrable_finset_sum _ fun j _ => hIcc (hcontj j))
          (measurableSet_Box d) hpt
    _ = ∑ j, ∫ y in Box d, ∏ i, gMom t j i (y i) :=
        integral_finset_sum _ fun j _ => hIcc (hcontj j)
    _ = ∑ j : Fin d, ∏ i, ∫ x in Ioc (-1 / 2 : ℝ) (-1 / 2 + 1), gMom t j i x := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact integral_Box_prod (fun i x => gMom t j i x)
    _ ≤ ∑ j : Fin d, M₂ * M₁ ^ (d - 1) := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc ∏ i, ∫ x in Ioc (-1 / 2 : ℝ) (-1 / 2 + 1), gMom t j i x
            ≤ ∏ i : Fin d, (if i = j then M₂ else M₁) :=
              Finset.prod_le_prod₀ (fun i _ => setIntegral_nonneg measurableSet_Ioc
                fun x _ => gMom_nonneg t j i x) (fun i _ => gMom_int_le ht j i)
          _ = M₂ * M₁ ^ (d - 1) := by
              rw [← Finset.mul_prod_erase Finset.univ (fun i => if i = j then M₂ else M₁)
                (Finset.mem_univ j)]
              simp only [ite_true]
              rw [Finset.prod_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi)),
                Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
                Fintype.card_fin]
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hM₂]; ring



theorem tdist_eq_sqrt (x y : Torus d) :
    KernelGrad.tdist x y = Real.sqrt (∑ i, ‖(x - y) i‖ ^ 2) := by
  unfold KernelGrad.tdist
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs, KernelGrad.norm_apply_eq, sq_abs]

theorem continuous_tdist_left (y : Torus d) : Continuous fun x : Torus d => KernelGrad.tdist x y := by
  simp_rw [tdist_eq_sqrt]
  fun_prop

theorem continuous_tdist_zero : Continuous fun x : Torus d => KernelGrad.tdist x 0 :=
  continuous_tdist_left 0

theorem tdist_self (x : Torus d) : KernelGrad.tdist x x = 0 := by
  rw [tdist_eq_sqrt]; simp

theorem continuous_of_isLipschitz_aux {L : ℝ} {ψ : Torus d → ℝ} (h : KernelGrad.IsLipschitz L ψ) :
    Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun y => dist_nonneg) (fun y => ?_)
    (g := fun y => |L| * KernelGrad.tdist y x) ?_
  · rw [Real.dist_eq]
    calc |ψ y - ψ x| ≤ L * KernelGrad.tdist y x := h y x
      _ ≤ |L| * KernelGrad.tdist y x :=
          mul_le_mul_of_nonneg_right (le_abs_self L) (KernelGrad.tdist_nonneg _ _)
  · have := ((continuous_tdist_left x).const_mul |L|).tendsto x
    simpa [tdist_self] using this

/-- the heat mollification `P_t ψ (x) = ∫ p_t(y) ψ(x - y) dy` -/
def heatP (d : ℕ) (t : ℝ) (ψ : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ y, heatK d t y * ψ (x - y)

theorem heatP_approx (hd : 1 ≤ d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ (L : ℝ) (ψ : Torus d → ℝ), 0 ≤ L →
      KernelGrad.IsLipschitz L ψ → ∀ x : Torus d, |ψ x - heatP d t ψ x| ≤ L * (M * Real.sqrt t) := by
  obtain ⟨M, hM0, hM⟩ := heat_moment hd
  refine ⟨M, hM0, fun t ht ht1 L ψ hL hψ x => ?_⟩
  have hc := continuous_of_isLipschitz_aux hψ
  have hK := continuous_heatK (d := d) ht
  have hint1 : Integrable (fun y => heatK d t y * ψ (x - y)) :=
    (hK.mul (hc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun y : Torus d => heatK d t y * KernelGrad.tdist y 0) :=
    (hK.mul continuous_tdist_zero).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint0 : Integrable (fun y : Torus d => heatK d t y * ψ x) :=
    (hK.mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h2 : ψ x - heatP d t ψ x = ∫ y, heatK d t y * (ψ x - ψ (x - y)) := by
    have e : ∫ y, heatK d t y * (ψ x - ψ (x - y)) =
        (∫ y, heatK d t y * ψ x) - ∫ y, heatK d t y * ψ (x - y) := by
      simp_rw [mul_sub]; exact integral_sub hint0 hint1
    rw [e, integral_mul_const, integral_heatK ht, one_mul]
    rfl
  rw [h2, ← Real.norm_eq_abs]
  calc ‖∫ y, heatK d t y * (ψ x - ψ (x - y))‖
      ≤ ∫ y, L * (heatK d t y * KernelGrad.tdist y 0) :=
        norm_integral_le_of_norm_le (hint2.const_mul L) (Filter.Eventually.of_forall fun y => ?_)
    _ = L * ∫ y, heatK d t y * KernelGrad.tdist y 0 := integral_const_mul _ _
    _ ≤ L * (M * Real.sqrt t) := by
        refine mul_le_mul_of_nonneg_left ?_ hL
        have := hM t ht ht1
        simpa [KernelGrad.tdist_zero_right] using this
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatK_nonneg ht y)]
  have h3 := hψ x (x - y)
  have h4 : KernelGrad.tdist x (x - y) = KernelGrad.tdist y 0 := by
    unfold KernelGrad.tdist; simp
  rw [h4] at h3
  calc heatK d t y * |ψ x - ψ (x - y)| ≤ heatK d t y * (L * KernelGrad.tdist y 0) :=
        mul_le_mul_of_nonneg_left h3 (heatK_nonneg ht y)
    _ = _ := by ring



theorem fcoef_norm_le {ψ : Torus d → ℝ} {M : ℝ} (hM : ∀ x, |ψ x| ≤ M) (k : Lattice d) :
    ‖Torus.fcoef ψ k‖ ≤ M := by
  unfold Torus.fcoef
  have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus d)))
    (f := fun x => Torus.mode (-k) x * (ψ x : ℂ)) (C := M) (Filter.Eventually.of_forall fun x => by
      rw [norm_mul, norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs]; exact hM x)
  simpa using h

theorem integral_cos_mul_shift {ψ : Torus d → ℝ} (hc : Continuous ψ) (k : Lattice d) (x : Torus d) :
    ∫ y, Torus.cosMode k y * ψ (x - y) = (Torus.mode k x * Torus.fcoef ψ k).re := by
  have h1 : ∀ y, Torus.cosMode k y * ψ (x - y) = ((Torus.mode k y) * ((ψ (x - y) : ℝ) : ℂ)).re := by
    intro y
    unfold Torus.cosMode
    rw [Complex.re_mul_ofReal]
  simp_rw [h1]
  have hc' : Continuous fun y => Torus.mode k y * ((ψ (x - y) : ℝ) : ℂ) :=
    (Torus.continuous_mode k).mul
      (Complex.continuous_ofReal.comp (hc.comp (continuous_const.sub continuous_id)))
  have hint : Integrable (fun y => Torus.mode k y * ((ψ (x - y) : ℝ) : ℂ)) :=
    hc'.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have := integral_re hint
  simp only [RCLike.re_to_complex] at this
  rw [this]
  congr 1
  have h2 : ∫ y, Torus.mode k y * ((ψ (x - y) : ℝ) : ℂ) =
      ∫ z, Torus.mode k (x - z) * ((ψ z : ℝ) : ℂ) := by
    haveI : (volume : Measure (Torus d)).IsNegInvariant :=
      MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
    rw [← integral_sub_left_eq_self (fun z => Torus.mode k (x - z) * ((ψ z : ℝ) : ℂ)) volume x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp
  rw [h2]
  have h3 : ∀ z, Torus.mode k (x - z) * ((ψ z : ℝ) : ℂ) =
      Torus.mode k x * (Torus.mode (-k) z * ((ψ z : ℝ) : ℂ)) := by
    intro z; rw [mode_sub_conj, ← Torus.mode_neg]; ring
  simp_rw [h3]
  rw [integral_const_mul]
  rfl



theorem heatP_series {ψ : Torus d → ℝ} (hc : Continuous ψ) {t : ℝ} (ht : 0 < t) (x : Torus d) :
    heatP d t ψ x = ∑' k : Lattice d,
      Real.exp (-t * Lattice.enorm k ^ 2) * (Torus.mode k x * Torus.fcoef ψ k).re := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound hc
  unfold heatP heatK
  have e : ∀ y : Torus d, (∑' k : Lattice d, Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k y) *
      ψ (x - y) = ∑' k : Lattice d, Real.exp (-t * Lattice.enorm k ^ 2) *
        (Torus.cosMode k y * ψ (x - y)) := by
    intro y; rw [← tsum_mul_right]; congr 1; funext k; ring
  simp_rw [e]
  rw [integral_tsum_c (summable_heatK_coef ht) (volume : Measure (Torus d))
    (fun k y => Torus.cosMode k y * ψ (x - y))
    (fun k => (Torus.continuous_cosMode k).mul (hc.comp (continuous_const.sub continuous_id)))
    (B := M) (fun k y => by
      rw [abs_mul]
      calc |Torus.cosMode k y| * |ψ (x - y)| ≤ 1 * M :=
            mul_le_mul (abs_cosMode_le k y) (hM _) (abs_nonneg _) zero_le_one
        _ = M := one_mul _)]
  refine tsum_congr fun k => ?_
  rw [integral_cos_mul_shift hc k x]

theorem integral_heatP_eq {ψ : Torus d → ℝ} (hc : Continuous ψ) {t : ℝ} (ht : 0 < t)
    (Qm : Measure (Torus d)) [IsFiniteMeasure Qm] :
    ∫ x, heatP d t ψ x ∂Qm = ∑' k : Lattice d,
      Real.exp (-t * Lattice.enorm k ^ 2) * ((∫ x, Torus.mode k x ∂Qm) * Torus.fcoef ψ k).re := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound hc
  simp_rw [heatP_series hc ht]
  rw [integral_tsum_c (summable_heatK_coef ht) Qm (fun k x => (Torus.mode k x * Torus.fcoef ψ k).re)
    (fun k => Complex.continuous_re.comp ((Torus.continuous_mode k).mul continuous_const))
    (B := M) (fun k x => by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_mode, one_mul]
      exact fcoef_norm_le hM k)]
  refine tsum_congr fun k => ?_
  congr 1
  have hint : Integrable (fun x => Torus.mode k x * Torus.fcoef ψ k) Qm :=
    ((Torus.continuous_mode k).mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have := integral_re hint
  simp only [RCLike.re_to_complex] at this
  rw [this, integral_mul_const]



theorem integrableOn_gam {a : ℝ} (ha : 0 < a) {m : ℝ} (hm : 0 < m) :
    IntegrableOn (fun u : ℝ => u ^ (a - 1) * Real.exp (-(m * u))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := m)
    (by linarith) one_pos hm
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  ring_nf

theorem one_add_rpow_ge {x b : ℝ} (hx : 0 ≤ x) (hb0 : -1 ≤ b) (hb1 : b ≤ 0) :
    Real.exp (-x) ≤ (1 + x) ^ b := by
  have h1 : (0:ℝ) < 1 + x := by linarith
  have h2 : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos h1; linarith
  have h3 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  rw [Real.rpow_def_of_pos h1]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem intT_lower {a : ℝ} (ha : 0 < a) : ∃ c : ℝ, 0 < c ∧ ∀ {ε m : ℝ}, 0 < ε → 1 ≤ m →
    c * (Real.exp (-(2 * ε * m)) * m ^ (-a)) ≤ ∫ u in Ioi ε, u ^ (a - 1) * Real.exp (-(m * u)) := by
  refine ⟨Real.exp (-2) * min 1 ((2 : ℝ) ^ (a - 1)), by positivity, fun {ε m} hε hm => ?_⟩
  have hm0 : 0 < m := by linarith
  set J : Set ℝ := Ioc (ε + 1 / m) (ε + 2 / m) with hJ
  have hint : IntegrableOn (fun u : ℝ => u ^ (a - 1) * Real.exp (-(m * u))) (Ioi ε) :=
    (integrableOn_gam ha hm0).mono_set (Ioi_subset_Ioi hε.le)
  have hJsub : J ⊆ Ioi ε := fun u hu => by
    have : 0 < 1 / m := by positivity
    exact lt_trans (by linarith) hu.1
  have hnn : ∀ u ∈ Ioi ε, 0 ≤ u ^ (a - 1) * Real.exp (-(m * u)) := fun u hu => by
    have hu0 : 0 < u := lt_trans hε hu
    have := Real.rpow_pos_of_pos hu0 (a - 1)
    positivity
  have h1 : ∫ u in J, u ^ (a - 1) * Real.exp (-(m * u)) ≤
      ∫ u in Ioi ε, u ^ (a - 1) * Real.exp (-(m * u)) :=
    setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall hnn)) hJsub.eventuallyLE
  refine le_trans ?_ h1
  -- lower bound on `J`
  have hpos : 0 < 1 / m := by positivity
  have hlen : ε + 2 / m - (ε + 1 / m) = 1 / m := by ring
  have hvol : (volume J).toReal = 1 / m := by
    rw [hJ, Real.volume_Ioc, hlen, ENNReal.toReal_ofReal hpos.le]
  have hfin : volume J ≠ ⊤ := by
    rw [hJ, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  set low : ℝ := if 1 ≤ a then (1 / m) ^ (a - 1) else (2 / m) ^ (a - 1) * Real.exp (-(ε * m / 2)) with hlow
  have hpt : ∀ u ∈ J, low * Real.exp (-(m * ε + 2)) ≤ u ^ (a - 1) * Real.exp (-(m * u)) := by
    intro u hu
    have hu0 : 0 < u := lt_trans hε (hJsub hu)
    have hexp : Real.exp (-(m * ε + 2)) ≤ Real.exp (-(m * u)) := by
      apply Real.exp_le_exp.mpr
      have : m * u ≤ m * ε + 2 := by
        have h2 : u ≤ ε + 2 / m := hu.2
        calc m * u ≤ m * (ε + 2 / m) := mul_le_mul_of_nonneg_left h2 hm0.le
          _ = m * ε + 2 := by field_simp
      linarith
    have hlow0 : 0 ≤ low := by
      rw [hlow]; split_ifs <;> positivity
    have hlowle : low ≤ u ^ (a - 1) := by
      rw [hlow]
      split_ifs with ha1
      · have : 1 / m ≤ u := by
          have : 0 < ε := hε
          linarith [hu.1]
        exact Real.rpow_le_rpow (by positivity) this (by linarith)
      · push Not at ha1
        have hu2 : u ≤ ε + 2 / m := hu.2
        have h3 : (ε + 2 / m) ^ (a - 1) ≤ u ^ (a - 1) :=
          Real.rpow_le_rpow_of_nonpos hu0 hu2 (by linarith)
        refine le_trans ?_ h3
        have h4 : ε + 2 / m = (2 / m) * (1 + ε * m / 2) := by field_simp; ring
        rw [h4, Real.mul_rpow (by positivity) (by positivity)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := one_add_rpow_ge (x := ε * m / 2) (b := a - 1) (by positivity) (by linarith) (by linarith)
        exact this
    exact mul_le_mul hlowle hexp (Real.exp_pos _).le (Real.rpow_pos_of_pos hu0 _).le
  have h2 : (low * Real.exp (-(m * ε + 2))) * (1 / m) ≤
      ∫ u in J, u ^ (a - 1) * Real.exp (-(m * u)) := by
    have hc : IntegrableOn (fun _ : ℝ => low * Real.exp (-(m * ε + 2))) J := integrableOn_const hfin
    have := setIntegral_mono_on hc (hint.mono_set hJsub) measurableSet_Ioc hpt
    rw [setIntegral_const, Measure.real, hvol, smul_eq_mul] at this
    linarith
  refine le_trans ?_ h2
  have e1 : m ^ (-a) = m ^ (-(a - 1)) * (1 / m) := by
    rw [show -a = -(a - 1) + (-1) by ring, Real.rpow_add hm0, Real.rpow_neg_one]; field_simp
  have hexp1 : Real.exp (-(2 * ε * m)) ≤ Real.exp (-(m * ε)) := by
    apply Real.exp_le_exp.mpr; nlinarith [mul_pos hε hm0]
  have hmin1 : min 1 ((2 : ℝ) ^ (a - 1)) ≤ 1 := min_le_left _ _
  have hmin2 : min 1 ((2 : ℝ) ^ (a - 1)) ≤ (2 : ℝ) ^ (a - 1) := min_le_right _ _
  have hmP : 0 < m ^ (-a) := Real.rpow_pos_of_pos hm0 _
  have hmin0 : 0 < min 1 ((2 : ℝ) ^ (a - 1)) := by positivity
  rw [hlow]
  split_ifs with ha1
  · have e2 : (1 / m) ^ (a - 1) = m ^ (-(a - 1)) := by
      rw [one_div, Real.inv_rpow hm0.le, Real.rpow_neg hm0.le]
    rw [e2]
    have e3 : Real.exp (-(m * ε + 2)) = Real.exp (-2) * Real.exp (-(m * ε)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e3]
    have : m ^ (-(a - 1)) * (Real.exp (-2) * Real.exp (-(m * ε))) * (1 / m) =
        Real.exp (-2) * Real.exp (-(m * ε)) * m ^ (-a) := by rw [e1]; ring
    rw [this]
    have h5 : 0 < Real.exp (-2) := Real.exp_pos _
    have h6 : 0 ≤ Real.exp (-(2 * ε * m)) * m ^ (-a) := by positivity
    calc Real.exp (-2) * min 1 ((2 : ℝ) ^ (a - 1)) * (Real.exp (-(2 * ε * m)) * m ^ (-a))
        ≤ Real.exp (-2) * 1 * (Real.exp (-(m * ε)) * m ^ (-a)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hmin1 h5.le)
            (mul_le_mul_of_nonneg_right hexp1 hmP.le) h6 (by positivity)
      _ = _ := by ring
  · push Not at ha1
    have e2 : (2 / m) ^ (a - 1) = (2 : ℝ) ^ (a - 1) * m ^ (-(a - 1)) := by
      rw [Real.div_rpow (by norm_num) hm0.le, Real.rpow_neg hm0.le, div_eq_mul_inv]
    rw [e2]
    have e3 : Real.exp (-(m * ε + 2)) = Real.exp (-2) * Real.exp (-(m * ε)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e3]
    have hexp2 : Real.exp (-(2 * ε * m)) ≤ Real.exp (-(ε * m / 2)) * Real.exp (-(m * ε)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [mul_pos hε hm0]
    have : (2 : ℝ) ^ (a - 1) * m ^ (-(a - 1)) * Real.exp (-(ε * m / 2)) *
        (Real.exp (-2) * Real.exp (-(m * ε))) * (1 / m) =
        (2 : ℝ) ^ (a - 1) * Real.exp (-2) * (Real.exp (-(ε * m / 2)) * Real.exp (-(m * ε)) * m ^ (-a)) := by
      rw [e1]; ring
    rw [this]
    have h5 : 0 < Real.exp (-2) := Real.exp_pos _
    have h6 : 0 ≤ Real.exp (-(2 * ε * m)) * m ^ (-a) := by positivity
    have h7 : 0 < (2 : ℝ) ^ (a - 1) := by positivity
    calc Real.exp (-2) * min 1 ((2 : ℝ) ^ (a - 1)) * (Real.exp (-(2 * ε * m)) * m ^ (-a))
        ≤ Real.exp (-2) * (2 : ℝ) ^ (a - 1) * (Real.exp (-(ε * m / 2)) * Real.exp (-(m * ε)) * m ^ (-a)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hmin2 h5.le)
            (mul_le_mul_of_nonneg_right hexp2 hmP.le) h6 (by positivity)
      _ = _ := by ring



theorem subA_pos_one (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) : 0 < subA d s := by
  have ha : 0 < ((d : ℝ) - s) / 2 := by
    have : (s : ℝ) < d := hsd
    linarith
  unfold subA
  have := rieszConst_pos_one hd hs0 hsd
  have := Real.Gamma_pos_of_pos ha
  positivity

theorem cT_lower (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ {ε : ℝ}, 0 < ε → ∀ k : Lattice d, k ≠ 0 →
      c * (Real.exp (-(2 * ε * Lattice.enorm k ^ 2)) * (Lattice.enorm k ^ 2) ^ (-(((d : ℝ) - s) / 2))) ≤
        cT d s ε k := by
  have ha : 0 < ((d : ℝ) - s) / 2 := by
    have : (s : ℝ) < d := hsd
    linarith
  have hA := subA_pos_one hd hs0 hsd
  obtain ⟨c₁, hc₁, h₁⟩ := intT_lower ha
  refine ⟨subA d s * c₁, by positivity, fun {ε} hε k hk => ?_⟩
  have hm : 1 ≤ Lattice.enorm k ^ 2 := by
    have := one_le_enorm k hk; nlinarith
  have := h₁ hε hm
  unfold cT
  rw [if_neg hk]
  calc subA d s * c₁ * (Real.exp (-(2 * ε * Lattice.enorm k ^ 2)) * (Lattice.enorm k ^ 2) ^ (-(((d : ℝ) - s) / 2)))
      = subA d s * (c₁ * (Real.exp (-(2 * ε * Lattice.enorm k ^ 2)) *
          (Lattice.enorm k ^ 2) ^ (-(((d : ℝ) - s) / 2)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hA.le



theorem heatP_continuous {ψ : Torus d → ℝ} (hc : Continuous ψ) {t : ℝ} (ht : 0 < t) :
    Continuous (heatP d t ψ) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound hc
  have : heatP d t ψ = fun x => ∑' k : Lattice d,
      Real.exp (-t * Lattice.enorm k ^ 2) * (Torus.mode k x * Torus.fcoef ψ k).re :=
    funext (heatP_series hc ht)
  rw [this]
  refine continuous_tsum (u := fun k : Lattice d => Real.exp (-t * Lattice.enorm k ^ 2) * M)
    (fun k => continuous_const.mul (Complex.continuous_re.comp
      ((Torus.continuous_mode k).mul continuous_const)))
    ((summable_gauss_lattice d t ht).mul_right M) (fun k x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_mode, one_mul]
  exact fcoef_norm_le hM k

/-- the terms of the homogeneous Sobolev series, extended by `0` at the origin -/
def homTerm (d : ℕ) (a : ℝ) (ψ : Torus d → ℝ) (k : Lattice d) : ℝ :=
  if k = 0 then 0 else (2 * Real.pi * Lattice.enorm k) ^ (2 * a) * ‖Torus.fcoef ψ k‖ ^ 2

theorem homSobolevSq_eq_tsum (a : ℝ) (ψ : Torus d → ℝ) :
    homSobolevSq a ψ = ∑' k : Lattice d, homTerm d a ψ k := by
  unfold homSobolevSq
  have h := tsum_subtype ({k : Lattice d | k ≠ 0}) (fun k : Lattice d =>
    (2 * Real.pi * Lattice.enorm k) ^ (2 * a) * ‖Torus.fcoef ψ k‖ ^ 2)
  refine h.trans (tsum_congr fun k => ?_)
  unfold homTerm
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  by_cases hk : k = 0 <;> simp [hk]

theorem summable_homTerm {a : ℝ} {ψ : Torus d → ℝ} (h : HasFiniteHomSobolev a ψ) :
    Summable (homTerm d a ψ) := by
  have h' := (summable_subtype_iff_indicator (s := {k : Lattice d | k ≠ 0})
    (f := fun k : Lattice d => (2 * Real.pi * Lattice.enorm k) ^ (2 * a) * ‖Torus.fcoef ψ k‖ ^ 2)).mp h
  refine h'.congr fun k => ?_
  unfold homTerm
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  by_cases hk : k = 0 <;> simp [hk]



theorem tsum_mul_le_sqrt {ι : Type*} {f g : ι → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ i, 0 ≤ g i)
    (hf : Summable fun i => f i ^ 2) (hg : Summable fun i => g i ^ 2) :
    Summable (fun i => f i * g i) ∧
      ∑' i, f i * g i ≤ Real.sqrt (∑' i, f i ^ 2) * Real.sqrt (∑' i, g i ^ 2) := by
  have hf' : Summable fun i => f i ^ (2 : ℝ) := by simpa [Real.rpow_two] using hf
  have hg' : Summable fun i => g i ^ (2 : ℝ) := by simpa [Real.rpow_two] using hg
  obtain ⟨h1, h2⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two hf0 hg0 hf' hg'
  refine ⟨h1, ?_⟩
  simp only [Real.rpow_two] at h2
  simpa [Real.sqrt_eq_rpow] using h2



theorem weight_sq (a : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ((x * y) ^ (-a)) ^ 2 = x ^ (-(2 * a)) * (y ^ 2) ^ (-a) := by
  have h1 : ((x * y) ^ (-a)) ^ 2 = (x * y) ^ (-a * 2) := by
    rw [Real.rpow_mul (by positivity), Real.rpow_two]
  have h2 : (y ^ 2) ^ (-a) = y ^ (2 * (-a)) := by
    rw [show (y ^ 2 : ℝ) = y ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast], ← Real.rpow_mul hy]
    norm_num
  rw [h1, h2, Real.mul_rpow hx hy]
  congr 2 <;> ring

theorem rpow_sq_eq (a : ℝ) {z : ℝ} (hz : 0 ≤ z) : (z ^ a) ^ 2 = z ^ (2 * a) := by
  rw [← Real.rpow_two, ← Real.rpow_mul hz]
  congr 1; ring

theorem delta_zero {N : ℕ} (hN : 0 < N) (X : Config d N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] :
    ((N : ℝ)⁻¹ : ℝ) • ∑ i, Torus.mode (0 : Lattice d) (X i) - ∫ x, Torus.mode (0 : Lattice d) x ∂μ = 0 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [Torus.mode_zero]
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  rw [inv_mul_cancel₀ hNC, sub_self]

theorem delta_norm_le {N : ℕ} (hN : 0 < N) (X : Config d N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (k : Lattice d) :
    ‖((N : ℝ)⁻¹ : ℝ) • ∑ i, Torus.mode k (X i) - ∫ x, Torus.mode k x ∂μ‖ ≤ 2 := by
  have := empirical_isProbabilityMeasure hN X
  rw [← integral_empirical_mode hN X k]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ∀ (Qm : Measure (Torus d)) [IsProbabilityMeasure Qm], ‖∫ x, Torus.mode k x ∂Qm‖ ≤ 1 := by
    intro Qm _
    refine (norm_integral_le_of_norm_le_const (C := 1) (Filter.Eventually.of_forall fun x => ?_)).trans ?_
    · rw [norm_mode]
    · simp
  linarith [h1 (empirical X), h1 μ]



/-- the Fourier coefficients of the signed measure `μ_N - μ` (conjugated convention: `∫ e_k d(μ_N-μ)`). -/
def deltaF {N : ℕ} (X : Config d N) (μ : Measure (Torus d)) (k : Lattice d) : ℂ :=
  ((N : ℝ)⁻¹ : ℝ) • ∑ i, Torus.mode k (X i) - ∫ x, Torus.mode k x ∂μ

theorem Esq_eq_tsum {N : ℕ} (ε : ℝ) (X : Config d N) (μ : Measure (Torus d)) :
    Esq d s ε X μ = ∑' k : Lattice d, cT d s ε k * ‖deltaF X μ k‖ ^ 2 := rfl

theorem fourier_side_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ {ε : ℝ}, 0 < ε → ∀ {N : ℕ}, 0 < N → ∀ (X : Config d N)
      (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {ψ : Torus d → ℝ}, Continuous ψ →
      HasFiniteHomSobolev (((d : ℝ) - s) / 2) ψ →
      |∫ x, heatP d ε ψ x ∂(empirical X) - ∫ x, heatP d ε ψ x ∂μ| ≤
        Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) ψ) * Real.sqrt (Cl * Esq d s ε X μ) := by
  have ha : 0 < ((d : ℝ) - s) / 2 := by
    have : (s : ℝ) < d := hsd
    linarith
  obtain ⟨c, hc, hcl⟩ := cT_lower hd hs0 hsd
  refine ⟨(2 * Real.pi) ^ (-(2 * (((d : ℝ) - s) / 2))) / c, by positivity,
    fun {ε} hε {N} hN X μ _ {ψ} hψ hhom => ?_⟩
  haveI := empirical_isProbabilityMeasure hN X
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound hψ
  -- Step (i): the Fourier expression of the difference
  have hsum : ∀ (z : Lattice d → ℂ), (∀ k, ‖z k‖ ≤ 1) →
      Summable fun k : Lattice d => Real.exp (-ε * Lattice.enorm k ^ 2) * (z k * Torus.fcoef ψ k).re := by
    intro z hz
    refine Summable.of_norm_bounded ((summable_gauss_lattice d ε hε).mul_right M) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    calc ‖z k‖ * ‖Torus.fcoef ψ k‖ ≤ 1 * M :=
          mul_le_mul (hz k) (fcoef_norm_le hM k) (norm_nonneg _) zero_le_one
      _ = M := one_mul _
  have hnorm1 : ∀ (Qm : Measure (Torus d)) [IsProbabilityMeasure Qm] (k : Lattice d),
      ‖∫ x, Torus.mode k x ∂Qm‖ ≤ 1 := by
    intro Qm _ k
    refine (norm_integral_le_of_norm_le_const (C := 1) (Filter.Eventually.of_forall fun x => ?_)).trans ?_
    · rw [norm_mode]
    · simp
  have hstep1 : ∫ x, heatP d ε ψ x ∂(empirical X) - ∫ x, heatP d ε ψ x ∂μ =
      ∑' k : Lattice d, Real.exp (-ε * Lattice.enorm k ^ 2) * (deltaF X μ k * Torus.fcoef ψ k).re := by
    rw [integral_heatP_eq hψ hε (empirical X), integral_heatP_eq hψ hε μ,
      ← Summable.tsum_sub (hsum _ (hnorm1 (empirical X))) (hsum _ (hnorm1 μ))]
    refine tsum_congr fun k => ?_
    unfold deltaF
    rw [← integral_empirical_mode hN X k, ← mul_sub, ← Complex.sub_re, ← sub_mul]
  -- Step (ii): Cauchy-Schwarz
  set a : ℝ := ((d : ℝ) - s) / 2 with ha_def
  set Cl : ℝ := (2 * Real.pi) ^ (-(2 * a)) / c with hCl
  have hCl0 : 0 ≤ Cl := by positivity
  let f : Lattice d → ℝ := fun k => if k = 0 then 0 else
    (2 * Real.pi * Lattice.enorm k) ^ a * ‖Torus.fcoef ψ k‖
  let g : Lattice d → ℝ := fun k => if k = 0 then 0 else
    Real.exp (-ε * Lattice.enorm k ^ 2) * (2 * Real.pi * Lattice.enorm k) ^ (-a) * ‖deltaF X μ k‖
  have hf0 : ∀ k, 0 ≤ f k := fun k => by
    simp only [f]; split_ifs
    · exact le_rfl
    · have : 0 ≤ 2 * Real.pi * Lattice.enorm k := mul_nonneg (by positivity) (norm_nonneg _)
      exact mul_nonneg (Real.rpow_nonneg this _) (norm_nonneg _)
  have hg0 : ∀ k, 0 ≤ g k := fun k => by
    simp only [g]; split_ifs
    · exact le_rfl
    · have : 0 ≤ 2 * Real.pi * Lattice.enorm k := mul_nonneg (by positivity) (norm_nonneg _)
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg this _)) (norm_nonneg _)
  have hf2 : ∀ k, f k ^ 2 = homTerm d a ψ k := fun k => by
    simp only [f, homTerm]
    split_ifs with hk
    · simp
    · rw [mul_pow, rpow_sq_eq a (z := 2 * Real.pi * Lattice.enorm k)
        (mul_nonneg (by positivity) (norm_nonneg _))]
  have hfs : Summable fun k => f k ^ 2 := (summable_homTerm hhom).congr (fun k => (hf2 k).symm)
  have hcT0 : cT d s ε 0 = 0 := by simp [cT]
  have hg2 : ∀ k, g k ^ 2 ≤ Cl * (cT d s ε k * ‖deltaF X μ k‖ ^ 2) := fun k => by
    by_cases hk : k = 0
    · subst hk
      simp [g, hcT0]
    · simp only [g, hk, ite_false]
      have hm : 0 ≤ Lattice.enorm k := norm_nonneg _
      have h1 := hcl hε k hk
      have h2 : (Real.exp (-ε * Lattice.enorm k ^ 2)) ^ 2 =
          Real.exp (-(2 * ε * Lattice.enorm k ^ 2)) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have h3 := weight_sq a (x := 2 * Real.pi) (y := Lattice.enorm k) (by positivity) hm
      rw [mul_pow, mul_pow, h2, h3]
      have h4 : Real.exp (-(2 * ε * Lattice.enorm k ^ 2)) * (Lattice.enorm k ^ 2) ^ (-a) ≤
          cT d s ε k / c := by
        rw [le_div_iff₀ hc]; linarith
      have h5 : 0 ≤ ‖deltaF X μ k‖ ^ 2 := sq_nonneg _
      calc Real.exp (-(2 * ε * Lattice.enorm k ^ 2)) * ((2 * Real.pi) ^ (-(2 * a)) *
              (Lattice.enorm k ^ 2) ^ (-a)) * ‖deltaF X μ k‖ ^ 2
          = (2 * Real.pi) ^ (-(2 * a)) * (Real.exp (-(2 * ε * Lattice.enorm k ^ 2)) *
              (Lattice.enorm k ^ 2) ^ (-a)) * ‖deltaF X μ k‖ ^ 2 := by ring
        _ ≤ (2 * Real.pi) ^ (-(2 * a)) * (cT d s ε k / c) * ‖deltaF X μ k‖ ^ 2 := by
            gcongr
        _ = Cl * (cT d s ε k * ‖deltaF X μ k‖ ^ 2) := by rw [hCl]; ring
  have hcTs := summable_cT hd hs0 hsd hε
  have hcTn := cT_nonneg hd hs0 hsd hε
  have hRHS : Summable fun k : Lattice d => Cl * (cT d s ε k * ‖deltaF X μ k‖ ^ 2) := by
    refine (Summable.of_nonneg_of_le (fun k => mul_nonneg (hcTn k) (sq_nonneg _)) (fun k => ?_)
      (hcTs.mul_right 4)).mul_left Cl
    refine mul_le_mul_of_nonneg_left ?_ (hcTn k)
    have h2 : ‖deltaF X μ k‖ ≤ 2 := delta_norm_le hN X μ k
    have h3 := norm_nonneg (deltaF X μ k)
    nlinarith
  have hgs : Summable fun k => g k ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hg2 hRHS
  obtain ⟨hfgs, hfg⟩ := tsum_mul_le_sqrt hf0 hg0 hfs hgs
  have hbound : ∀ k : Lattice d, |Real.exp (-ε * Lattice.enorm k ^ 2) *
      (deltaF X μ k * Torus.fcoef ψ k).re| ≤ f k * g k := fun k => by
    by_cases hk : k = 0
    · subst hk
      have : deltaF X μ 0 = 0 := delta_zero hN X μ
      simp [this, f]
    · simp only [f, g, hk, ite_false]
      have hx : 0 < 2 * Real.pi * Lattice.enorm k := by
        have := one_le_enorm k hk
        have := Real.pi_pos
        positivity
      have e1 : (2 * Real.pi * Lattice.enorm k) ^ a * (2 * Real.pi * Lattice.enorm k) ^ (-a) = 1 := by
        rw [← Real.rpow_add hx, add_neg_cancel, Real.rpow_zero]
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 : |(deltaF X μ k * Torus.fcoef ψ k).re| ≤ ‖deltaF X μ k‖ * ‖Torus.fcoef ψ k‖ :=
        (Complex.abs_re_le_norm _).trans (norm_mul _ _).le
      calc Real.exp (-ε * Lattice.enorm k ^ 2) * |(deltaF X μ k * Torus.fcoef ψ k).re|
          ≤ Real.exp (-ε * Lattice.enorm k ^ 2) * (‖deltaF X μ k‖ * ‖Torus.fcoef ψ k‖) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = ((2 * Real.pi * Lattice.enorm k) ^ a * (2 * Real.pi * Lattice.enorm k) ^ (-a)) *
              (Real.exp (-ε * Lattice.enorm k ^ 2) * (‖deltaF X μ k‖ * ‖Torus.fcoef ψ k‖)) := by
            rw [e1]; ring
        _ = _ := by ring
  have hu_sum : Summable fun k : Lattice d => ‖Real.exp (-ε * Lattice.enorm k ^ 2) *
      (deltaF X μ k * Torus.fcoef ψ k).re‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
      rw [Real.norm_eq_abs]; exact hbound k) hfgs
  rw [hstep1]
  have hfs2 : ∑' k, f k ^ 2 = homSobolevSq a ψ := by
    rw [homSobolevSq_eq_tsum]; exact tsum_congr hf2
  have hgs2 : ∑' k, g k ^ 2 ≤ Cl * Esq d s ε X μ := by
    calc ∑' k, g k ^ 2 ≤ ∑' k : Lattice d, Cl * (cT d s ε k * ‖deltaF X μ k‖ ^ 2) :=
          hgs.tsum_le_tsum hg2 hRHS
      _ = Cl * Esq d s ε X μ := by rw [tsum_mul_left]; rfl
  calc |∑' k : Lattice d, Real.exp (-ε * Lattice.enorm k ^ 2) * (deltaF X μ k * Torus.fcoef ψ k).re|
      = ‖∑' k : Lattice d, Real.exp (-ε * Lattice.enorm k ^ 2) *
          (deltaF X μ k * Torus.fcoef ψ k).re‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' k : Lattice d, ‖Real.exp (-ε * Lattice.enorm k ^ 2) *
          (deltaF X μ k * Torus.fcoef ψ k).re‖ := norm_tsum_le_tsum_norm hu_sum
    _ ≤ ∑' k, f k * g k := hu_sum.tsum_le_tsum (fun k => by rw [Real.norm_eq_abs]; exact hbound k) hfgs
    _ ≤ Real.sqrt (∑' k, f k ^ 2) * Real.sqrt (∑' k, g k ^ 2) := hfg
    _ ≤ Real.sqrt (homSobolevSq a ψ) * Real.sqrt (Cl * Esq d s ε X μ) := by
        rw [hfs2]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hgs2) (Real.sqrt_nonneg _)



theorem abs_integral_sub_le {Pm : Measure (Torus d)} [IsProbabilityMeasure Pm] {f g : Torus d → ℝ}
    (hf : Continuous f) (hg : Continuous g) {δ : ℝ} (h : ∀ x, |f x - g x| ≤ δ) :
    |∫ x, f x ∂Pm - ∫ x, g x ∂Pm| ≤ δ := by
  have hfi : Integrable f Pm := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgi : Integrable g Pm := hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub hfi hgi, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := δ) (Filter.Eventually.of_forall fun x => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact h x
  · simp

theorem coercivity_core (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N ∧
        ∀ (ψ : Torus d → ℝ) (L : ℝ), 0 ≤ L → KernelGrad.IsLipschitz L ψ →
          HasFiniteHomSobolev (((d : ℝ) - s) / 2) ψ →
          |∫ x, ψ x ∂(empirical X) - ∫ x, ψ x ∂(withDensityReal ρ)| ≤
            C * smearScale d N Λ * L +
              C * homSobolev (((d : ℝ) - s) / 2) ψ *
                Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  obtain ⟨C₀, hC₀, hE⟩ := coercivity_energy hd hs0 hsd
  obtain ⟨M, hM0, hM⟩ := heatP_approx hd
  obtain ⟨Cl, hCl0, hCl⟩ := fourier_side_bound hd hs0 hsd
  refine ⟨C₀, 2 * M + Real.sqrt (2 * Cl) + 1, hC₀, by positivity, ?_⟩
  intro Λ hΛ N hN ρ hρ hρΛ X hX
  have hN1 : 1 ≤ N := by omega
  have hΛ0 : 0 < Λ := by linarith
  have hNΛ : 1 < (N : ℝ) * Λ := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  obtain ⟨hE0, hE1⟩ := hE Λ hΛ N hN ρ hρ hρΛ X hX
  set lam := smearScale d N Λ with hlam
  have hlam0 : 0 < lam := smearScale_pos (d := d) hN1 hΛ0
  have hlam1 : lam < 1 := smearScale_lt_one hd hNΛ
  have hε : 0 < lam ^ 2 := by positivity
  have hε1 : lam ^ 2 ≤ 1 := by nlinarith
  set S := rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N with hS
  have hS0 : 0 ≤ S := by linarith
  refine ⟨hS0, fun ψ L hL hψ hhom => ?_⟩
  haveI := isProb_withDensityReal hρ
  haveI := empirical_isProbabilityMeasure (d := d) (by omega : 0 < N) X
  set μ := withDensityReal ρ with hμ
  have hc := continuous_of_isLipschitz_aux hψ
  have hcP := heatP_continuous hc hε
  have hδ : ∀ x, |ψ x - heatP d (lam ^ 2) ψ x| ≤ L * (M * lam) := by
    intro x
    have := hM (lam ^ 2) hε hε1 L ψ hL hψ x
    rwa [Real.sqrt_sq hlam0.le] at this
  have h1 := abs_integral_sub_le (Pm := empirical X) hc hcP hδ
  have h2 := abs_integral_sub_le (Pm := μ) hc hcP hδ
  have h3 := hCl hε (by omega : 0 < N) X μ hc hhom
  have h4 : Real.sqrt (Cl * Esq d s (lam ^ 2) X μ) ≤ Real.sqrt (2 * Cl) * Real.sqrt S := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hhom0 : 0 ≤ Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) ψ) := Real.sqrt_nonneg _
  have h5 : Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) ψ) * Real.sqrt (Cl * Esq d s (lam ^ 2) X μ) ≤
      Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) ψ) * (Real.sqrt (2 * Cl) * Real.sqrt S) :=
    mul_le_mul_of_nonneg_left h4 hhom0
  -- decomposition
  have hdec : ∫ x, ψ x ∂(empirical X) - ∫ x, ψ x ∂μ =
      (∫ x, ψ x ∂(empirical X) - ∫ x, heatP d (lam ^ 2) ψ x ∂(empirical X)) -
        (∫ x, ψ x ∂μ - ∫ x, heatP d (lam ^ 2) ψ x ∂μ) +
        (∫ x, heatP d (lam ^ 2) ψ x ∂(empirical X) - ∫ x, heatP d (lam ^ 2) ψ x ∂μ) := by ring
  rw [hdec]
  have hhomS : homSobolev (((d : ℝ) - s) / 2) ψ = Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) ψ) := rfl
  rw [hhomS]
  have hLM : 0 ≤ L * (M * lam) := by positivity
  have hsq0 : 0 ≤ Real.sqrt (2 * Cl) := Real.sqrt_nonneg _
  have hS' : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  have hAbs : |(∫ x, ψ x ∂(empirical X) - ∫ x, heatP d (lam ^ 2) ψ x ∂(empirical X)) -
        (∫ x, ψ x ∂μ - ∫ x, heatP d (lam ^ 2) ψ x ∂μ) +
        (∫ x, heatP d (lam ^ 2) ψ x ∂(empirical X) - ∫ x, heatP d (lam ^ 2) ψ x ∂μ)| ≤
      L * (M * lam) + L * (M * lam) +
        Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) ψ) * (Real.sqrt (2 * Cl) * Real.sqrt S) := by
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_sub _ _).trans (add_le_add h1 h2)) (h3.trans h5)
  refine hAbs.trans ?_
  have hmid : 0 ≤ Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) ψ) * Real.sqrt S := mul_nonneg hhom0 hS'
  have hmid2 : Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) ψ) * (Real.sqrt (2 * Cl) * Real.sqrt S) ≤
      (2 * M + Real.sqrt (2 * Cl) + 1) * Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) ψ) * Real.sqrt S := by
    have : Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) ψ) * (Real.sqrt (2 * Cl) * Real.sqrt S) =
        Real.sqrt (2 * Cl) * (Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) ψ) * Real.sqrt S) := by ring
    rw [this]
    have h6 : (2 * M + Real.sqrt (2 * Cl) + 1) * Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) ψ) * Real.sqrt S =
        (2 * M + Real.sqrt (2 * Cl) + 1) * (Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) ψ) * Real.sqrt S) := by ring
    rw [h6]
    exact mul_le_mul_of_nonneg_right (by linarith) hmid
  have hlin : L * (M * lam) + L * (M * lam) ≤ (2 * M + Real.sqrt (2 * Cl) + 1) * lam * L := by
    have : 0 ≤ (Real.sqrt (2 * Cl) + 1) * lam * L := by positivity
    nlinarith
  linarith

end CoercHeat


end CoercFourier


end CoercAux

/-- Proposition 3.34 `M:B:prop:hrs-periodic-coercivity` (source lines 2865-2898).  Let `d ≥ 1`,
`0 ≤ s < d`, and the zero-mean periodic kernel `ĝ(k) = c_{d,s}(2π|k|)^{s-d}` (`k ≠ 0`),
`c_{d,s} > 0` (this is `periodicRiesz d s`, with the normalisation `g = -log|x| + O(1)` when
`s = 0`, ISSUES §B K1).  Let `μ = ρ dx` be a probability density with `‖μ‖_∞ ≤ Λ`, `Λ ≥ 1`,
`X_N` pairwise distinct, `N ≥ 2`, `λ = (NΛ)^{-1/d}`, `a_N^Λ = Λ^{s/d} N^{s/d-1}`.  There are
constants `C₀, C` depending only on `d, s` (and the kernel normalisation) such that, with
`o_N(Λ) = 1_{s=0} log(NΛ)/(2dN) + C₀ a_N^Λ`:
`F_N(X_N,μ) + o_N(Λ) ≥ 0` (`B:eq:hrs-periodic-coercivity-lower`), and for every Lipschitz real
`ψ` (constant `L ≥ 0`) with finite `Ḣ^{(d-s)/2}` seminorm,
`|∫ ψ dρ_N| ≤ C λ ‖∇ψ‖_∞ + C ‖ψ‖_{Ḣ^{(d-s)/2}} (F_N + o_N(Λ))^{1/2}`
(`B:eq:hrs-periodic-coercivity-test`), `ρ_N = N⁻¹∑δ_{x_i} - μ`.  The constants are independent
of the configuration (including its smallest pair distance); "increasing `C₀` preserves both
statements" is `periodic_coercivity_mono`.

PLAN (source proof 2900-3054): truncate the heat-kernel representation of `g`
(`heatRiesz d s ε`, `HRS/Kernel/Riesz.lean`; `heatRiesz_ge`, `periodicRiesz_ge`,
`theta_nonneg`, `psi_ge` in `HRS/Energy/Modulated.lean` are the positivity inputs) at scale
`λ`, keep the smooth positive quadratic form `∬ g_λ d(ρ_N)^{⊗2} ≥ 0`, and estimate the difference
with `F_N` explicitly including the deleted empirical diagonal (this produces `o_N(Λ)`:
the diagonal term `N⁻¹ g_λ(0) ≍ N⁻¹λ^{-s}` for `s>0`, `N⁻¹ log(1/λ)` for `s = 0`, and the
`λ^{2}` Lipschitz/`λ^{d-s}` smearing errors bounded by `Λ`-weighted integrals); for the test bound,
split `ψ = ψ * φ_λ + (ψ - ψ*φ_λ)` and use Cauchy–Schwarz in Fourier against the positive form
(`B:eq:hrs-heat-sharp-control` with `η = λ`) and the Lipschitz cutoff bound
`B:eq:hrs-cutoff-lipschitz`. -/
theorem periodic_coercivity (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N ∧
        ∀ (ψ : Torus d → ℝ) (L : ℝ), 0 ≤ L → KernelGrad.IsLipschitz L ψ →
          HasFiniteHomSobolev (((d : ℝ) - s) / 2) ψ →
          |∫ x, ψ x ∂(empirical X) - ∫ x, ψ x ∂(withDensityReal ρ)| ≤
            C * smearScale d N Λ * L +
              C * homSobolev (((d : ℝ) - s) / 2) ψ *
                Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  obtain ⟨C₀, C, hC₀, hC, h⟩ := CoercAux.coercivity_core hd hs0 hsd
  exact ⟨C₀, C, hC₀, hC, h⟩

/-- Proposition 3.34, last sentence (line 2897): "increasing `C₀` preserves both statements" —
the correction `o_N(Λ)` is monotone in `C₀` (`Λ ≥ 1`), and both the lower bound and the test bound
are monotone in the correction.  PLAN: `Real.rpow_nonneg`, `Real.sqrt_le_sqrt`, `mul_le_mul`. -/
theorem periodic_coercivity_mono {s C₀ C₀' Λ : ℝ} (hC : C₀ ≤ C₀') (hΛ : 0 ≤ Λ) (N : ℕ)
    (F a b c : ℝ) (hc : 0 ≤ c) :
    oNΛ d s C₀ Λ N ≤ oNΛ d s C₀' Λ N ∧
    (0 ≤ F + oNΛ d s C₀ Λ N → 0 ≤ F + oNΛ d s C₀' Λ N) ∧
    (0 ≤ F + oNΛ d s C₀ Λ N → a ≤ b + c * Real.sqrt (F + oNΛ d s C₀ Λ N) →
      a ≤ b + c * Real.sqrt (F + oNΛ d s C₀' Λ N)) := by
  have hmono : oNΛ d s C₀ Λ N ≤ oNΛ d s C₀' Λ N := by
    unfold oNΛ
    have ha : 0 ≤ Λ ^ (s / d) := Real.rpow_nonneg hΛ _
    have hb : 0 ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have h1 : C₀ * Λ ^ (s / d) ≤ C₀' * Λ ^ (s / d) := mul_le_mul_of_nonneg_right hC ha
    have h2 : C₀ * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) ≤
        C₀' * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) := mul_le_mul_of_nonneg_right h1 hb
    linarith
  refine ⟨hmono, fun h => by linarith, fun h1 h2 => ?_⟩
  have hs : Real.sqrt (F + oNΛ d s C₀ Λ N) ≤ Real.sqrt (F + oNΛ d s C₀' Λ N) :=
    Real.sqrt_le_sqrt (by linarith)
  have := mul_le_mul_of_nonneg_left hs hc
  linarith

/-- Proposition 3.33 `M:B:prop:coercivity` (source lines 2842-2852), item (i) (lower bound), on
the torus: with `C₀` as in Proposition 3.32, for all pairwise distinct `X_N`, all admissible `μ`
(probability densities with `‖μ‖_∞ ≤ Λ`) and `λ = (NΛ)^{-1/d} < 1`, `F_N(X_N,μ) + o_N ≥ 0`.
On `𝕋^d` this is the first clause of Proposition 3.34 ("the direct heat-kernel argument proves the
full range, with the same correction", line 2846).  PLAN: `periodic_coercivity`. -/
theorem coercivity_lower (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N := by
  obtain ⟨C₀, hC₀, h⟩ := CoercAux.coercivity_energy hd hs0 hsd
  refine ⟨C₀, hC₀, fun Λ hΛ N hN ρ hρ hρΛ X hX => ?_⟩
  obtain ⟨h1, h2⟩ := h Λ hΛ N hN ρ hρ hρΛ X hX
  linarith

/-- Proposition 3.33, item (ii) (control of linear statistics, `B:eq:coercivity-test`, lines
2847-2850), on the torus: for every Lipschitz `ψ` with `‖ψ‖_{Ḣ^{(d-s)/2}} < ∞`,
`|∫ ψ d(N⁻¹∑δ_{x_i} - μ)| ≤ C ‖∇ψ‖_{L^∞} λ + C ‖ψ‖_{Ḣ^{(d-s)/2}} (F_N(X_N,μ) + o_N)^{1/2}`,
`C = C(d,s)`, `Ḣ^{(d-s)/2}(𝕋^d)` defined by `∑_{k≠0}(2π|k|)^{d-s}|ψ̂(k)|²` (line 2851).
PLAN: the second clause of `periodic_coercivity`. -/
theorem coercivity_test (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ (ψ : Torus d → ℝ) (L : ℝ), 0 ≤ L → KernelGrad.IsLipschitz L ψ →
        HasFiniteHomSobolev (((d : ℝ) - s) / 2) ψ →
        |∫ x, ψ x ∂(empirical X) - ∫ x, ψ x ∂(withDensityReal ρ)| ≤
          C * L * smearScale d N Λ +
            C * homSobolev (((d : ℝ) - s) / 2) ψ *
              Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  obtain ⟨C₀, C, hC₀, hC, h⟩ := CoercAux.coercivity_core hd hs0 hsd
  refine ⟨C₀, C, hC₀, hC, fun Λ hΛ N hN ρ hρ hρΛ X hX ψ L hL hψ hhom => ?_⟩
  have := (h Λ hΛ N hN ρ hρ hρΛ X hX).2 ψ L hL hψ hhom
  calc _ ≤ _ := this
    _ = _ := by ring

/-- `o_N(Λ)` is monotone in `C₀` (for `Λ ≥ 0`). -/
theorem oNΛ_mono_C₀ {s C₀ C₀' Λ : ℝ} (hC : C₀ ≤ C₀') (hΛ : 0 ≤ Λ) (N : ℕ) :
    oNΛ d s C₀ Λ N ≤ oNΛ d s C₀' Λ N := by
  unfold oNΛ
  have h1 : 0 ≤ Λ ^ (s / d) := Real.rpow_nonneg hΛ _
  have h2 : 0 ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h3 : 0 ≤ Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) := mul_nonneg h1 h2
  have : C₀ * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) ≤ C₀' * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hC h3
  linarith

theorem HasTransportBound.nonneg {s : ℝ} {v : Torus d → Euc d} {K : ℝ}
    (h : HasTransportBound d s v K) : 0 ≤ K := by
  obtain ⟨L, F, hL, hF, -, -, hK⟩ := h
  split_ifs at hK <;> linarith

/-- Propositions 3.32 and 3.33 with a common `C₀` ("with `C₀` as fixed above", line 2843): the
commutator bound, the lower bound and the test bound hold simultaneously for one `C₀ = C₀(d,s)`.
PLAN: take the maximum of the two `C₀`'s from `commutator_estimate` and `periodic_coercivity`
and use `periodic_coercivity_mono` (the commutator bound is monotone in `C₀` as well since
`C K ≥ 0`). -/
theorem commutator_coercivity_common (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N ∧
        (∀ (v : Torus d → Euc d) (K : ℝ), HasTransportBound d s v K →
          |commQuantity d s v X (withDensityReal ρ)| ≤
            C * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)) ∧
        (∀ (ψ : Torus d → ℝ) (L : ℝ), 0 ≤ L → KernelGrad.IsLipschitz L ψ →
          HasFiniteHomSobolev (((d : ℝ) - s) / 2) ψ →
          |∫ x, ψ x ∂(empirical X) - ∫ x, ψ x ∂(withDensityReal ρ)| ≤
            C * L * smearScale d N Λ +
              C * homSobolev (((d : ℝ) - s) / 2) ψ *
                Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)) := by
  obtain ⟨A₀, A, hA₀, hA, hcomm⟩ := commutator_estimate hd hs0 hsd
  obtain ⟨B₀, B, hB₀, hB, hcoer⟩ := periodic_coercivity hd hs0 hsd
  refine ⟨max A₀ B₀, max A B, le_max_of_le_left hA₀, lt_max_of_lt_left hA, ?_⟩
  intro Λ hΛ N hN ρ hρ hρΛ X hX
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨hlow, htest⟩ := hcoer Λ hΛ N hN ρ hρ hρΛ X hX
  have hoB : oNΛ d s B₀ Λ N ≤ oNΛ d s (max A₀ B₀) Λ N :=
    oNΛ_mono_C₀ (le_max_right _ _) hΛ0 N
  have hoA : oNΛ d s A₀ Λ N ≤ oNΛ d s (max A₀ B₀) Λ N :=
    oNΛ_mono_C₀ (le_max_left _ _) hΛ0 N
  have hlow' : 0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max A₀ B₀) Λ N := by
    linarith
  refine ⟨hlow', ?_, ?_⟩
  · intro v K hK
    have hK0 := hK.nonneg
    have h1 := (hcomm Λ hΛ N hN ρ hρ hρΛ X hX v K hK).2
    refine h1.trans ?_
    have hAK : 0 ≤ A * K := mul_nonneg hA.le hK0
    calc A * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s A₀ Λ N)
        ≤ A * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max A₀ B₀) Λ N) :=
          mul_le_mul_of_nonneg_left (by linarith) hAK
      _ ≤ max A B * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max A₀ B₀) Λ N) := by
          apply mul_le_mul_of_nonneg_right _ hlow'
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hK0
  · intro ψ L hL hψ hfin
    refine (htest ψ L hL hψ hfin).trans ?_
    have hsm : 0 ≤ smearScale d N Λ :=
      Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg N) hΛ0) _
    have hhs : 0 ≤ homSobolev (((d : ℝ) - s) / 2) ψ := Real.sqrt_nonneg _
    have hsq : Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s B₀ Λ N) ≤
        Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max A₀ B₀) Λ N) :=
      Real.sqrt_le_sqrt (by linarith)
    have hAB : B ≤ max A B := le_max_right _ _
    have hsq0 := Real.sqrt_nonneg (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s B₀ Λ N)
    have e1 : B * smearScale d N Λ * L ≤ max A B * L * smearScale d N Λ := by
      nlinarith [mul_nonneg hsm hL]
    have e2 : B * homSobolev (((d : ℝ) - s) / 2) ψ *
        Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s B₀ Λ N) ≤
        max A B * homSobolev (((d : ℝ) - s) / 2) ψ *
        Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max A₀ B₀) Λ N) := by
      apply mul_le_mul _ hsq hsq0 (mul_nonneg (hA.le.trans (le_max_left _ _)) hhs)
      exact mul_le_mul_of_nonneg_right hAB hhs
    linarith

/-! ### Remark 3.35: use with a fixed density bound -/

/-- Remark 3.35 `M:B:rem:hrs-coercivity-fixed-density` (source lines 3056-3066), first claim:
for a fixed `Λ`, `o_N(Λ) ≤ C₀' a_N` with `a_N = (1 + 1_{s=0} log N) N^{s/d-1}` and a constant `C₀'`
depending on `Λ` (and `C₀, d, s`); thus a single corrected energy `F_N + C₀' a_N` can be used
throughout any trajectory with this density bound (by `periodic_coercivity_mono`).
PLAN: `log(NΛ) = log N + log Λ`, `log Λ/(2dN) ≤ log Λ · N^{s/d-1}` since `s/d - 1 ≥ -1`,
`Λ^{s/d} ≤ Λ`. -/
theorem oNΛ_le_aN (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C₀' : ℝ, 0 ≤ C₀' ∧ ∀ N : ℕ, 2 ≤ N → oNΛ d s C₀ Λ N ≤ C₀' * aN d s N := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hlΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hpos : 0 ≤ (1 + Real.log Λ) / (2 * d) := div_nonneg (by linarith) (by positivity)
  have hCΛ : 0 ≤ C₀ * Λ := mul_nonneg hC₀ hΛ0.le
  refine ⟨C₀ * Λ + (1 + Real.log Λ) / (2 * d), by linarith, ?_⟩
  intro N hN
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hx : 0 ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg hN0.le _
  have hlN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  by_cases hs : s = 0
  · subst hs
    have hxN : (N : ℝ) ^ ((0 : ℝ) / d - 1) = (N : ℝ)⁻¹ := by
      rw [zero_div, zero_sub, Real.rpow_neg_one]
    have hinv : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hN0.le
    unfold oNΛ aN
    rw [hxN, Real.log_mul hN0.ne' hΛ0.ne']
    simp only [if_true, zero_div, Real.rpow_zero, one_mul, mul_one, add_zero]
    have hA : 0 ≤ C₀ * (Λ * (1 + Real.log N) - 1) := by
      apply mul_nonneg hC₀
      nlinarith
    have hB : 0 ≤ (1 / (2 * d)) * (1 + Real.log Λ * Real.log N) := by
      apply mul_nonneg (by positivity)
      have := mul_nonneg hlΛ hlN
      linarith
    have key : (C₀ * Λ + (1 + Real.log Λ) / (2 * d)) * ((1 + Real.log N) * (N : ℝ)⁻¹)
        - ((Real.log N + Real.log Λ) / (2 * d * N) + C₀ * (N : ℝ)⁻¹)
        = (N : ℝ)⁻¹ * (C₀ * (Λ * (1 + Real.log N) - 1) + (1 / (2 * d)) * (1 + Real.log Λ * Real.log N)) := by
      field_simp
      ring
    nlinarith [mul_nonneg hinv (add_nonneg hA hB)]
  · have hsd1 : s / d ≤ 1 := (div_le_one hd').mpr hsd.le
    have ha : Λ ^ (s / d) ≤ Λ := by
      calc Λ ^ (s / d) ≤ Λ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hsd1
        _ = Λ := Real.rpow_one Λ
    unfold oNΛ aN
    simp only [if_neg hs, zero_add, add_zero, one_mul]
    have h1 : C₀ * Λ ^ (s / d) ≤ C₀ * Λ := mul_le_mul_of_nonneg_left ha hC₀
    have h2 : C₀ * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) ≤ C₀ * Λ * (N : ℝ) ^ (s / d - 1) :=
      mul_le_mul_of_nonneg_right h1 hx
    have h3 : 0 ≤ (1 + Real.log Λ) / (2 * d) * (N : ℝ) ^ (s / d - 1) := mul_nonneg hpos hx
    nlinarith

/-- Remark 3.35, second claim (lines 3062-3066): the correction `o_N(Λ)` has the same logarithmic
coefficient `1_{s=0} log N/(2dN)` as `o_N` of `H:eq:energy-completion` (`HRS.oN`), and only the
fixed constant `C₀` of the nonlogarithmic part may need to be enlarged: for fixed `Λ ≥ 1` there is
`C₀'` with `o_N(Λ) ≤ o_N(C₀')` for all `N ≥ 2`; at `Λ = 1` the two agree.
PLAN: as `oNΛ_le_aN`; `oNΛ_one` is `Real.rpow` of `1` and `mul_one`. -/
theorem oNΛ_le_oN (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    (∀ N : ℕ, oNΛ d s C₀ 1 N = oN d s C₀ N) ∧
    ∃ C₀' : ℝ, 0 ≤ C₀' ∧ ∀ N : ℕ, 2 ≤ N → oNΛ d s C₀ Λ N ≤ oN d s C₀' N := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hlΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hpos : 0 ≤ Real.log Λ / (2 * d) := div_nonneg hlΛ (by positivity)
  have hCΛ : 0 ≤ C₀ * Λ := mul_nonneg hC₀ hΛ0.le
  refine ⟨fun N => ?_, C₀ * Λ + Real.log Λ / (2 * d), by linarith, ?_⟩
  · unfold oNΛ oN
    simp only [Real.one_rpow, mul_one, one_mul]
    ring
  intro N hN
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hx : 0 ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg hN0.le _
  by_cases hs : s = 0
  · subst hs
    have hxN : (N : ℝ) ^ ((0 : ℝ) / d - 1) = (N : ℝ)⁻¹ := by
      rw [zero_div, zero_sub, Real.rpow_neg_one]
    have hinv : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hN0.le
    unfold oNΛ oN
    rw [hxN, Real.log_mul hN0.ne' hΛ0.ne']
    simp only [if_true, zero_div, Real.rpow_zero, one_mul, mul_one]
    have hC : 0 ≤ C₀ * (Λ - 1) := mul_nonneg hC₀ (by linarith)
    have e : (Real.log N + Real.log Λ) / (2 * d * N) =
        Real.log N / (2 * d * N) + Real.log Λ / (2 * d) * (N : ℝ)⁻¹ := by ring
    rw [e]
    nlinarith [mul_nonneg hinv hC]
  · have hsd1 : s / d ≤ 1 := (div_le_one hd').mpr hsd.le
    have ha : Λ ^ (s / d) ≤ Λ := by
      calc Λ ^ (s / d) ≤ Λ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hsd1
        _ = Λ := Real.rpow_one Λ
    unfold oNΛ oN
    simp only [if_neg hs, zero_add, add_zero]
    have h1 : C₀ * Λ ^ (s / d) ≤ C₀ * Λ := mul_le_mul_of_nonneg_left ha hC₀
    have h2 : C₀ * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) ≤ C₀ * Λ * (N : ℝ) ^ (s / d - 1) :=
      mul_le_mul_of_nonneg_right h1 hx
    have h3 : 0 ≤ Real.log Λ / (2 * d) * (N : ℝ) ^ (s / d - 1) := mul_nonneg hpos hx
    nlinarith

/-! ### Energies along the particle dynamics -/

/-- `F_N(X_N^t, μ^t) + o_N(Λ)` along a particle path and a mean-field density. -/
def correctedEnergy (D : DynData d) (C₀ Λ : ℝ) (ρ : ℝ → Torus d → ℝ) (X : Config d N) (t : ℝ) :
    ℝ :=
  rieszEnergy d D.s X (withDensityReal (ρ t)) + oNΛ d D.s C₀ Λ N

/-- The self-force `(∇k * ρ_N)°(x_i) = N⁻¹ ∑_{j≠i} ∇k(x_i - x_j) - ∇k*μ(x_i)` (Proposition 3.38,
line 3158; `a_i` in the proof of Proposition 3.37, line 3129) for a force field `G = ∇k`, with
`∇k*μ` by the convention convolution `convGradConv` (ISSUES §B K3; for bounded `G` it is the plain
convolution). -/
def selfForce (G : Torus d → Euc d) (ρ : Torus d → ℝ) (X : Config d N) (i : Fin N) : Euc d :=
  (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, G (X i - X j) - convGradConv G ρ (X i)

/-- The off-diagonal pairing `∬_{𝔻²∖△} k(x-y) d(ρ_N)^{⊗2}` of a difference kernel. -/
def offDiagDiffPairing (k : Torus d → ℝ) (X : Config d N) (μ : Measure (Torus d)) : ℝ :=
  offDiagPairing (fun x y => if x = y then 0 else k (x - y)) X μ

/-- Normalised relative entropy `𝖧_N(f | Q) = N⁻¹ H(f | Q)` (used at line 3102; see ISSUES §C). -/
def normRelEntropy (N : ℕ) (f Q : Measure (Config d N)) : ℝ≥0∞ := relEntropy f Q / N

/-- The modulated free energy `𝖤_N(f, μ) = β⁻¹ 𝖧_N(f | μ^{⊗N}) + ∫ F_N(X_N, μ) f(dX_N)` (used
in Propositions 3.36(C2) and 3.41 without a definition in the main paper; see ISSUES §C), with
`β⁻¹ = invβ`; a real number meaningful under `MFEFinite`. -/
def modulatedFreeEnergy (d : ℕ) (s invβ : ℝ) {N : ℕ} (f : Measure (Config d N))
    (μ : Measure (Torus d)) : ℝ :=
  invβ * (normRelEntropy N f (Measure.pi fun _ : Fin N => μ)).toReal +
    ∫ X, rieszEnergy d s X μ ∂f

/-- `𝖤_N(f, μ) < ∞`: finite relative entropy and integrable interaction energy. -/
def MFEFinite (d : ℕ) (s : ℝ) {N : ℕ} (f : Measure (Config d N)) (μ : Measure (Torus d)) :
    Prop :=
  relEntropy f (Measure.pi fun _ : Fin N => μ) ≠ ∞ ∧ Integrable (fun X => rieszEnergy d s X μ) f

/-- The transport field `u_V^t = β⁻¹ ∇ log μ^t + ∇g*μ^t + ∇V` of `B:eq:uV-periodic` (line 3208). -/
def mfeTransport (D : DynData d) (ρ : Torus d → ℝ) (x : Torus d) : Euc d :=
  D.invβ • Torus.grad (fun y => Real.log (ρ y)) x +
    convGradConv (periodicRieszGrad d D.s) ρ x + Torus.grad D.V x

/-- The standing hypotheses of Proposition 3.41 `M:B:prop:mfe-uniform` (source lines 3204-3210):
`𝕋^d`, `0 ≤ s < d` (in `DynData`), `M = -I`, `β_N < ∞` (`invβ > 0`), `V ∈ C^{m_*+2}`, the selected
initial law has finite Gibbs entropy `B:eq:selected-initial-gibbs-entropy` (relative entropy with
respect to the normalised Gibbs measure `G_{N,β_N,V}`, `B:eq:gibbs-entropy-measure-convention`,
line 12014) and `𝖤_N(f_N^0, μ°) < ∞`; `μ_{β_N}` is an `(m_*+2, Λ)`-regular mean-field solution on
`[0,T]` with datum `μ° = ρ 0` and `inf μ_{β_N} ≥ lam₀ > 0`; `X` is the selected particle process
(`B:ass:sde`(a): the collision-free strong solution, with `X_0` independent of the noise).  The field `filtered` (statement
repair, ISSUES.md, entry "Filtered strong solutions: follow-up repairs") is the strong-solution
adaptedness of `B:ass:sde` (a Brownian filtration carrying `W` to which `X` is adapted) that Proposition B.15
`sde_entropy_law` (the first input of `mfe_uniform`) takes and `IsStrongSolution` (measurability only, ISSUES D1) does
not record. -/
structure MFEHyp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : DynData d) (N : ℕ) (T Λ lam₀ : ℝ)
    (ρ : ℝ → Torus d → ℝ) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) : Prop where
  gradient : D.M = -1
  pos_temp : 0 < D.invβ
  V_reg : Torus.IsCk (PDE.mStar d + 2) D.V
  mf : IsMeanFieldSolution D T ρ
  mf_reg : IsRegularMF (PDE.mStar d + 2) Λ T ρ
  Λ_ge : 1 ≤ Λ
  pos_density : 0 < lam₀ ∧ ∀ t ∈ Set.Icc 0 T, ∀ x, lam₀ ≤ ρ t x
  gibbs_entropy : relEntropy (P.map X₀) (canonicalGibbs (periodicRiesz d D.s) D.V N (1 / D.invβ)) ≠ ∞
  mfe_init : MFEFinite d D.s (P.map X₀) (withDensityReal (ρ 0))
  brownian : IsVectorBrownian P W
  indep : ProbabilityTheory.IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P
  sol : IsStrongSolution P D T X₀ W X
  filtered : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X

/-! ### Proposition 3.36: dynamical modulated-energy bounds -/

/-- Proposition 3.36 `M:B:prop:gronwall-catalog` (source lines 3078-3111), item (C1) *zero
temperature* (lines 3082-3094): `β_N = ∞` (`invβ = 0`), `𝖲 = ½(M + Mᵀ) ≤ 0`, `μ_{β_N}` an
`(r,Λ)`-regular mean-field solution, `r ≥ 3`, and the effective transport
`u^t = M ∇g*μ^t - ∇V` with transport seminorm `‖u^t‖_* ≤ Λ'` uniformly on `[0,T]` (the
hypothesis of the applicable commutator estimate; for Coulomb and super-Coulomb the seminorm is
`‖∇u^t‖_∞`, in the strict sub-Coulomb case it includes the fractional term, which is what
`HasTransportBound` encodes).  Then, pathwise,
`F_N(X_N^t, μ^t) + o_N ≤ e^{CTΛ'} (F_N(X_N^0, μ^0) + o_N)` for `0 ≤ t ≤ T`
(`B:eq:zero-temperature-energy-bound`), with `C₀, C` depending on `d, s` only.

PLAN: at zero temperature the particle system is a pathwise ODE (`IsStrongSolution.lift` with
`invβ = 0`); `t ↦ F_N(X^t, μ^t)` is absolutely continuous with derivative
`½ Comm_N(u^t; X^t, μ^t) + N⁻¹ ∑_i a_iᵀ 𝖲 a_i` (the deterministic case of
`B:eq:coulomb-energy-identity`/`comparison_kernel_identity`: differentiate the three terms of
`F_N` along the flow using the mean-field weak formulation `IsMeanFieldSolution.weak` for the
`μ`-terms, `convGradConv` for the force and the symmetrisation of `interactionPairing`), the second
term is `≤ 0` by `SymNonpos`, the first is `≤ ½ C Λ' (F_N + o_N)` by `commutator_estimate`
(`IsRegularMF` gives `‖μ^t‖_∞ ≤ Λ`), and Grönwall (`gronwall_bound`/`norm_le_gronwallBound_of_norm_deriv_right_le`
in Mathlib) closes. 

Statement repair 2026-10-17 (ISSUES "G336"): added `Torus.IsCk 2 D.V` (V otherwise enters only through the junk
`Torus.grad D.V`; the proof uses Prop 3.38, which needs it; TeX standing assumption V ∈ C^{m_V}; same as SPEC-C0 Defect 2). -/
theorem gronwall_zero_temperature (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : DynData d), D.s = s → D.invβ = 0 → Torus.SymNonpos D.M → Torus.IsCk 2 D.V →
      ∀ (N : ℕ), 2 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (ρ : ℝ → Torus d → ℝ) (r : ℕ) (Λ : ℝ), 3 ≤ r → 1 ≤ Λ →
        IsMeanFieldSolution D T ρ → IsRegularMF r Λ T ρ →
      ∀ Λ' : ℝ, (∀ t ∈ Set.Icc 0 T, HasTransportBound d s (meanFieldDrift D (ρ t)) Λ') →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P D T X₀ W X →
        ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T,
          correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t ≤
            Real.exp (C * T * Λ') * correctedEnergy D C₀ Λ ρ (X 0 ω) 0 := by
  sorry

/-- Proposition 3.36 (C1), consequence (line 3091): "`𝔈_N = e^{CTΛ'} 𝓔_N^0` is admissible", i.e.
`sup_{t≤T} E[F_N(X^t,μ^t) + o_N] ≤ e^{CTΛ'} E[F_N(X^0,μ^0) + o_N]` (the energy smallness
`B:ass:MF` then holds whenever `σ_N 𝔈_N → 0`).  PLAN: integrate `gronwall_zero_temperature`
(`lintegral_mono_ae`, `ofReal_integral_eq_lintegral_ofReal` with the nonnegativity of
`coercivity_lower`). 

Statement repair 2026-10-17 (ISSUES "G336"): added `Torus.IsCk 2 D.V` (V otherwise enters only through the junk
`Torus.grad D.V`; the proof uses Prop 3.38, which needs it; TeX standing assumption V ∈ C^{m_V}; same as SPEC-C0 Defect 2). -/
theorem gronwall_zero_temperature_moment (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : DynData d), D.s = s → D.invβ = 0 → Torus.SymNonpos D.M → Torus.IsCk 2 D.V →
      ∀ (N : ℕ), 2 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (ρ : ℝ → Torus d → ℝ) (r : ℕ) (Λ : ℝ), 3 ≤ r → 1 ≤ Λ →
        IsMeanFieldSolution D T ρ → IsRegularMF r Λ T ρ →
      ∀ Λ' : ℝ, (∀ t ∈ Set.Icc 0 T, HasTransportBound d s (meanFieldDrift D (ρ t)) Λ') →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P D T X₀ W X →
        Integrable (fun ω => correctedEnergy D C₀ Λ ρ (X 0 ω) 0) P →
        ∀ t ∈ Set.Icc 0 T,
          ∫⁻ ω, ENNReal.ofReal (correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t) ∂P ≤
            ENNReal.ofReal (Real.exp (C * T * Λ') *
              ∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P) := by
  sorry

/-- Proposition 3.36, item (C2) *periodic gradient flow at positive temperature, uniformly down to
zero* (lines 3095-3103): if `M = -I`, `𝔻 = 𝕋^d`, `0 ≤ s < d`, `β_N < ∞`, the selected initial law
satisfies `B:eq:selected-initial-gibbs-entropy` and the positive-density hypotheses of
Proposition 3.41 hold (`MFEHyp`), then
`𝔈_N = C (β_N⁻¹ 𝖧_N(f_N^0 | (μ°)^{⊗N}) + 𝓔_N^0)` is admissible:
`sup_{t≤T} E[F_N(X^t,μ^t) + o_N] ≤ C (β_N⁻¹ 𝖧_N(f_N^0 | (μ°)^{⊗N}) + E[F_N(X^0,μ°) + o_N])`,
with `C` chosen before `N` and before `β_N⁻¹ ∈ (0, σ₀]` (uniformity as `β_N⁻¹ ↓ 0`; `C` may
depend on `d, s, T, Λ, lam₀, σ₀` and the `C^{m_*+2}` bound `Λ_V` of `V`).  The statement applies
to the law of the canonical particle process, includes smooth periodic confinement, and is
uniform as `β_N⁻¹ ↓ 0` (the exactly zero-temperature case is (C1)).  The one-dimensional
collisional logarithmic flow (`B:ass:sde`(b)) is not covered by `IsStrongSolution`
(PART-01, Prop. B.2) and is left to that package.

PLAN: `mfe_uniform` gives `𝖤_N(f^t,μ^t) + o_N ≤ e^{C L_T^*}(𝖤_N(f^0,μ°) + o_N)`,
`transport_bound_uniform` gives `L_T^* ≤ C T`; `E[F_N(X^t,μ^t)] ≤ 𝖤_N(f^t, μ^t)` since the
normalised relative entropy is nonnegative (`klDiv` nonnegative), lines 3230-3234.

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): `MFEHyp` now includes the filtered strong solution (`filtered`, `IsFilteredSolution`) that Proposition B.15 `sde_entropy_law`, the first input of `mfe_uniform`, takes. -/
theorem gronwall_gradient_flow (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (T Λ lam₀ ΛV σ₀ : ℝ) (hT : 0 ≤ T) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : DynData d), D.s = s → D.invβ ≤ σ₀ → Torus.cbNorm (PDE.mStar d + 2) D.V ≤ ΛV →
      ∀ (N : ℕ), 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Torus d → ℝ) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Config d N),
        MFEHyp P D N T Λ lam₀ ρ X₀ W X →
        ∀ t ∈ Set.Icc 0 T,
          ∫⁻ ω, ENNReal.ofReal (correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t) ∂P ≤
            ENNReal.ofReal (C * (D.invβ *
              (normRelEntropy N (P.map X₀) (Measure.pi fun _ : Fin N => withDensityReal (ρ 0))).toReal +
              ∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P)) := by
  sorry

/-- The standing hypotheses of Proposition 3.37 `M:B:prop:lowtemp` (source lines 3113-3116):
`d ≥ 2`, `s = d-2`, `𝔻 = 𝕋^d`, `𝖲 ≤ 0`, `B:ass:sde` (a collision-free strong solution driven by
independent Brownian motions, `X_0` independent of the noise), `V` as in
`B:sec:conv-confinement` (periodic `C^2` with bounded norm, the index needed for the Lipschitz
transport), `μ_{β_N}` a `(3,Λ)`-regular mean-field solution on `[0,T]`.  The field `filtered` (statement
repair, ISSUES.md entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …", final entry "Filtered strong solutions …")
is the strong-solution adaptedness of `B:ass:sde` (a Brownian filtration carrying `W` to which `X` is adapted)
that the Itô calculus of the proof of Prop 3.37 needs and `IsStrongSolution` (measurability only, ISSUES D1)
does not record. -/
structure LowTempHyp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : DynData d) (N : ℕ)
    (T Λ ΛV Mb : ℝ) (ρ : ℝ → Torus d → ℝ) (X₀ : Ω → Config d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) : Prop where
  coulomb : D.s = (d : ℝ) - 2
  sym_nonpos : Torus.SymNonpos D.M
  M_bound : ∀ v : Euc d, ‖Torus.matVec D.M v‖ ≤ Mb * ‖v‖
  V_reg : Torus.IsCk 2 D.V ∧ Torus.cbNorm 2 D.V ≤ ΛV
  mf : IsMeanFieldSolution D T ρ
  mf_reg : IsRegularMF 3 Λ T ρ
  Λ_ge : 1 ≤ Λ
  brownian : IsVectorBrownian P W
  indep : ProbabilityTheory.IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P
  sol : IsStrongSolution P D T X₀ W X
  filtered : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X

/-- Proposition 3.37 `M:B:prop:lowtemp` (source lines 3113-3124), bound `B:eq:lowtemp-bound`:
under `LowTempHyp`, `sup_{t∈[0,T]} E[F_N(X^t, μ^t) + o_N] ≤ C (𝓔_N^0 + β_N⁻¹)`,
`𝓔_N^0 = E[F_N(X^0, μ°) + o_N]`, with `C = C(d, |M|, Λ, V, T)` (chosen before `N`, `β_N`, the
solution) and `C₀ = C₀(d,s)` from the coercivity/commutator estimates.

PLAN (source proof 3126-3153): the energy identity `B:eq:coulomb-energy-identity`
(`comparison_kernel_identity` with `h = g`, after stopping at the exit time of
`{min pair distance > ε}`, `exitTime`/`isStoppingTime_exitTime` and `ito_formula_localized` in
`HRS/Stochastic/*`; the Coulomb kernel is `C²` and harmonic off `0`, `Δ(g*μ) = c_d(1-μ)` on the
torus), the sign `N⁻¹∑ a_iᵀ 𝖲 a_i ≤ 0`, the diffusion correction
`B:eq:coulomb-diffusion-correction`: `𝒟_N^t = c_d(-N⁻¹ + 2⟨μ^t, μ_N^t⟩ - ∫(μ^t)²) ≤ 2c_d Λ`, the
commutator bound `commutator_estimate` with `‖u^t‖_* ≤ C(|M|, Λ, V)` (Coulomb: Lipschitz norm
only), Fatou to remove the stopping, and Grönwall for `t ↦ E[F_N^t + o_N]`.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"):
the proof applies Itô's formula to the particles, so `LowTempHyp` now includes a filtered strong solution
(`filtered : ∃ ℱ W', IsFilteredSolution P ℱ W' W X`). -/
theorem lowtemp_coulomb_bound (hd : 2 ≤ d) (T Λ ΛV Mb : ℝ) (hT : 0 ≤ T) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : DynData d) (N : ℕ), 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Torus d → ℝ) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Config d N),
        LowTempHyp P D N T Λ ΛV Mb ρ X₀ W X →
        Integrable (fun ω => correctedEnergy D C₀ Λ ρ (X 0 ω) 0) P →
        ∀ t ∈ Set.Icc 0 T,
          ∫⁻ ω, ENNReal.ofReal (correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t) ∂P ≤
            ENNReal.ofReal (C * (∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P + D.invβ)) := by
  sorry

/-- Proposition 3.37, consequence (`B:eq:lowtemp-threshold`, lines 3120-3123): if
`β_N ≥ δ (NΛ)^{2/d}` then the right-hand side of `B:eq:lowtemp-bound` is bounded by
`C_δ (𝓔_N^0 + o_N)`; this is also item (C3) of Proposition 3.36 (lines 3104-3109), which adds
"no comparison `o_N ≤ 𝓔_N^0` is asserted".

PLAN (lines 3152-3153): at `s = d-2`, `o_N(Λ) ≥ C₀ Λ^{1-2/d} N^{-2/d}` (and the logarithm in the
two-dimensional case), so `β_N⁻¹ ≤ δ⁻¹(NΛ)^{-2/d} ≤ C_δ o_N(Λ)` once `C₀ > 0` is enlarged to be
positive (`periodic_coercivity_mono`); then `lowtemp_coulomb_bound`.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"):
it inherits the filtered strong solution (`LowTempHyp.filtered`) needed for the Itô calculus of `lowtemp_coulomb_bound`. -/
theorem lowtemp_coulomb_threshold (hd : 2 ≤ d) (T Λ ΛV Mb δ : ℝ) (hT : 0 ≤ T) (hδ : 0 < δ) :
    ∃ C₀ Cδ : ℝ, 0 ≤ C₀ ∧ 0 < Cδ ∧
      ∀ (D : DynData d) (N : ℕ), 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Torus d → ℝ) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Config d N),
        LowTempHyp P D N T Λ ΛV Mb ρ X₀ W X →
        Integrable (fun ω => correctedEnergy D C₀ Λ ρ (X 0 ω) 0) P →
        D.invβ ≤ (δ * (N * Λ) ^ (2 / (d : ℝ)))⁻¹ →
        ∀ t ∈ Set.Icc 0 T,
          ∫⁻ ω, ENNReal.ofReal (correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t) ∂P ≤
            ENNReal.ofReal (Cδ * (∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P +
              oNΛ d D.s C₀ Λ N)) := by
  sorry

/-! ### Proposition 3.38: the exact comparison-kernel identity -/

/-- The microscopic mixed term `N⁻¹ ∑_i (∇h*ρ_N)°(x_i) · M (∇g*ρ_N)°(x_i)` of
`B:eq:comparison-kernel-identity` (line 3164). -/
def microTerm (D : DynData d) (h : Torus d → ℝ) (ρ : Torus d → ℝ) (X : Config d N) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, inner ℝ (selfForce (Torus.grad h) ρ X i)
    (Torus.matVec D.M (selfForce (periodicRieszGrad d D.s) ρ X i))

/-- Proposition 3.38 `M:B:prop:comparison-kernel-identity` (source lines 3155-3167): for a smooth
even kernel `h`, `F_{N,h}` the modulated energy with `g` replaced by `h`, and along dynamics
driven by `g` (a collision-free strong solution, `μ` a `(3,Λ)`-regular mean-field solution with
viscosity `β_N⁻¹`, so that `u^t = M∇g*μ^t - ∇V` is Lipschitz),
`d/dt E[F_{N,h}^t] = ½ E[Comm_{N,h}(u^t; X^t, μ^t)] + E[N⁻¹∑_i (∇h*ρ_N^t)°(x_i^t) · M(∇g*ρ_N^t)°(x_i^t)]
+ β_N⁻¹ E[∬_{𝔻²∖△} Δh d(ρ_N^t)^{⊗2}]`, stated in integrated form on `[0,t]`, `t ≤ T`, under the
integrability of the microscopic term that the source presupposes (the other two terms are
bounded for smooth `h`).  "In particular, for `h = g_λ` the middle term is a force–kernel mismatch
and cannot be omitted" is commentary on the identity.

PLAN (lines 3169-3175): Itô's formula (`ito_formula_additive`, `HRS/Stochastic/Ito.lean`, with
the `IsStrongSolution` lift and additive noise `√(2β⁻¹) dW`) for the particle–particle,
particle–background and background–background terms of `F_{N,h}` (`h` smooth so all are `C²` in
`X`); the terms linear in `ρ_N` cancel against the mean-field equation
(`IsMeanFieldSolution.weak` with test `h(x_i - ·)` and `h*μ`), leaving the `h`-commutator with
`u^t`; the microscopic interaction is `∫ (∇h*ρ_N)°·M(∇g*ρ_N)° dμ_N`; the second-order particle and
mean-field terms combine into the diagonal-free `Δh` pairing (`Torus.laplacian`); martingale terms
have zero expectation (`martingale_itoIntegral`); Fubini in `(r, ω)`.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"):
the Itô proof needs the standing assumption `B:ass:sde` in full, so the statement now also assumes `IndepFun X₀ W`
(initial configuration independent of the noise, as in `LowTempHyp`/`MFEHyp`) and a filtered strong solution
(`IsFilteredSolution`); without them the martingale terms need not have zero expectation, so the identity can fail.

Statement repair 2026-10-16 (ISSUES "SPEC-C0"): added `(hV : Torus.IsCk 2 D.V)`; the TeX uses `V ∈ C^{m_V}` (B:sec:conv-confinement, L10073-10077; Prop 3.37 at L3114 assumes it) and the Itô/commutator proof needs it, while the statement had no regularity on `D.V`. -/
theorem comparison_kernel_identity (hd : 1 ≤ d) (D : DynData d) (N : ℕ) (hN : 2 ≤ N)
    (hV : Torus.IsCk 2 D.V)
    (h : Torus d → ℝ) (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x)
    (T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → Torus d → ℝ) (Λ : ℝ)
    (hmf : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF 3 Λ T ρ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hW : IsVectorBrownian P W)
    (hind : ProbabilityTheory.IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P)
    (hsol : IsStrongSolution P D T X₀ W X)
    (hfilt : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
      (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T)
    (hmicro : Integrable (fun p : ℝ × Ω => microTerm D h (ρ p.1) (X (Real.toNNReal p.1) p.2))
      ((volume.restrict (Set.Icc 0 t)).prod P)) :
    ∫ ω, modulatedEnergyKernel h (X (Real.toNNReal t) ω) (withDensityReal (ρ t)) ∂P -
        ∫ ω, modulatedEnergyKernel h (X 0 ω) (withDensityReal (ρ 0)) ∂P =
      ∫ r in Set.Icc 0 t,
        ((1 / 2) * ∫ ω, commQuantityWith (Torus.grad h) (meanFieldDrift D (ρ r))
            (X (Real.toNNReal r) ω) (withDensityReal (ρ r)) ∂P +
          ∫ ω, microTerm D h (ρ r) (X (Real.toNNReal r) ω) ∂P +
          D.invβ * ∫ ω, offDiagDiffPairing (Torus.laplacian h) (X (Real.toNNReal r) ω)
            (withDensityReal (ρ r)) ∂P) := by
  sorry

/-- The quadratic form of `M` only sees `Sym M = (M + Mᵀ)/2`. -/
theorem inner_matVec_symPart (M : Matrix (Fin d) (Fin d) ℝ) (a : Euc d) :
    inner ℝ a (Torus.matVec M a) = inner ℝ a (Torus.matVec (Torus.symPart M) a) := by
  have h1 : Torus.matVec M.transpose a = (Matrix.toEuclideanLin M).adjoint a := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.conjTranspose_eq_transpose_of_trivial]
    rfl
  have h2 : inner ℝ a ((Matrix.toEuclideanLin M).adjoint a) = inner ℝ (Matrix.toEuclideanLin M a) a :=
    LinearMap.adjoint_inner_right _ _ _
  have h3 : Torus.matVec (Torus.symPart M) a =
      (1 / 2 : ℝ) • (Torus.matVec M a + Torus.matVec M.transpose a) := by
    unfold Torus.matVec Torus.symPart
    simp [map_add, map_smul]
  rw [h3, inner_smul_right, inner_add_right, h1, h2]
  have e : inner ℝ (Matrix.toEuclideanLin M a) a = inner ℝ a (Torus.matVec M a) :=
    real_inner_comm _ _
  rw [e]
  ring

/-- Remark 3.39 `M:B:rem:MF-truncated` (source lines 3177-3194), the identity it asserts
(line 3180): for `h = g` the microscopic term of `B:eq:comparison-kernel-identity` is the signed
quadratic form `N⁻¹ ∑_i a_iᵀ 𝖲 a_i`, `𝖲 = ½(M + Mᵀ)`, `a_i = (∇g*ρ_N)°(x_i)` (also used at line
3175 and in `B:eq:coulomb-energy-identity`).  The rest of the remark (the singularity of
`Δg ≍ |x|^{-s-2}` for `s > d-2`, the unresolved near-field mixed product for `h = g_λ`, and the
role of the entropy for gradient flows) is discussion without a formal claim.
PLAN: `inner a (M a) = inner a (symPart M a)` (`Matrix.toEuclideanLin`, `real_inner_comm`,
`Matrix.transpose` adjointness), then `Finset.sum_congr`.  Stated for every force field `G` (here
`G = ∇g`) since only the algebra of `M` enters. -/
theorem microTerm_self_kernel (D : DynData d) (ρ : Torus d → ℝ) (X : Config d N)
    (G : Torus d → Euc d) :
    (1 / (N : ℝ)) * ∑ i, inner ℝ (selfForce G ρ X i) (Torus.matVec D.M (selfForce G ρ X i)) =
      (1 / (N : ℝ)) * ∑ i, inner ℝ (selfForce G ρ X i)
        (Torus.matVec (Torus.symPart D.M) (selfForce G ρ X i)) := by
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact inner_matVec_symPart D.M _

/-! ### Proposition 3.41: periodic modulated free energy -/

/-- Proposition 3.41 `M:B:prop:mfe-uniform` (source lines 3204-3217), bound `B:eq:mfe-uniform`:
under `MFEHyp` (`𝕋^d`, `0 ≤ s < d`, `M = -I`, `β_N < ∞`, `V ∈ C^{m_*+2}`, finite initial Gibbs
entropy, `𝖤_N(f_N^0, μ°) < ∞`, `(m_*+2,Λ)`-regular `μ_{β_N}` with `inf μ_{β_N} ≥ lam₀ > 0`), with
`u_V^t = β_N⁻¹∇log μ^t + ∇g*μ^t + ∇V` and `L_T^* = ∫_0^T ‖u_V^t‖_* dt` (represented by any
integrable `K` with `‖u_V^t‖_* ≤ K t`): the law `P_N^t` of `X_N^t` has a density `f_N^t`
(`P_N^t ≪ dX_N`, the density of the selected law in Proposition B.15), `𝖤_N(f_N^t, μ^t) < ∞`, and
`𝖤_N(f_N^t, μ_{β_N}^t) + o_N ≤ e^{C L_T^*} (𝖤_N(f_N^0, μ°) + o_N)` for `0 ≤ t ≤ T`,
`C = C(d,s)` (from Proposition 3.32) and `C₀ = C₀(d,s)`.

PLAN (lines 3219-3236): Proposition B.15 `M:B:prop:sde-entropy-law` (PART-01, not yet stated;
its content — density of the selected law and the entropy/Fisher-information inequality
`B:eq:selected-gradient-entropy` — is the first input) for the density `f_N^t`; the
modulated-free-energy calculation for the smooth regularised SDE laws of B.15's proof, with the
common one-body drift `-∇V` cancelling in the relative-entropy comparison and entering only through
the commutator with `∇V`; pass to the selected law by lower semicontinuity of entropy, Fisher
information and the diagonal-truncated energy; discard the nonpositive relative Fisher information
to get `d/dt 𝖤_N(f^t,μ^t) ≤ -½ ∫ Comm_N(u_V^t; X_N, μ^t) f^t(X_N) dX_N` (`B:eq:mfe-dissipation`);
bound by `commutator_estimate` with `‖u_V^t‖_* ≤ K t`; `∫(F_N + o_N) f^t ≤ 𝖤_N(f^t,μ^t) + o_N`
since `klDiv ≥ 0` and `F_N + o_N ≥ 0` (`coercivity_lower`); Grönwall.  External inputs: none
beyond Proposition 3.32.

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): `MFEHyp` now includes the filtered strong solution (`filtered`, `IsFilteredSolution`) that Proposition B.15 `sde_entropy_law` (the first input) takes and `IsStrongSolution` (measurability only, ISSUES D1) does not record. -/
theorem mfe_uniform (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : DynData d), D.s = s → ∀ (N : ℕ), 2 ≤ N → ∀ (T Λ lam₀ : ℝ), 0 ≤ T →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Torus d → ℝ) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Config d N),
        MFEHyp P D N T Λ lam₀ ρ X₀ W X →
      ∀ K : ℝ → ℝ, IntegrableOn K (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc 0 T, HasTransportBound d s (mfeTransport D (ρ t)) (K t)) →
      ∀ t ∈ Set.Icc 0 T,
        (P.map (X (Real.toNNReal t))).AbsolutelyContinuous volume ∧
        MFEFinite d s (P.map (X (Real.toNNReal t))) (withDensityReal (ρ t)) ∧
        modulatedFreeEnergy d s D.invβ (P.map (X (Real.toNNReal t))) (withDensityReal (ρ t)) +
            oNΛ d s C₀ Λ N ≤
          Real.exp (C * ∫ r in Set.Icc 0 T, K r) *
            (modulatedFreeEnergy d s D.invβ (P.map X₀) (withDensityReal (ρ 0)) + oNΛ d s C₀ Λ N) := by
  sorry

/-- Proposition 3.41, last sentence (lines 3215-3216): if `0 < β_N⁻¹ ≤ σ₀` and the displayed
mean-field and confinement norms are bounded uniformly in `N` (`‖μ^t‖_{C^{m_*+2}} ≤ Λ`,
`μ^t ≥ lam₀ > 0`, `‖V‖_{C^{m_*+2}} ≤ Λ_V`), then `‖u_V^t‖_* ≤ C` for all `t`, hence
`L_T^* ≤ C T`, with `C` independent of the particular value of `β_N⁻¹ ∈ (0, σ₀]`.

PLAN: `∇ log μ = ∇μ/μ` with `μ ≥ lam₀` gives `C^{m_*+1}` bounds (`Torus.cbNorm` of quotients),
`∇g*μ` is `C^{m_*+1}` for `μ ∈ C^{m_*+2}` (`HRS/Kernel/GradReg.lean`, `GradSmooth.lean`),
`∇V ∈ C^{m_*+1}`; the Lipschitz constant is the `C¹` norm of `u_V`, and for `s < d-2` the
fractional derivative of order `(d+1)/2 ≤ m_*+1` of a `C^{m_*+1}` function is bounded (Fourier
coefficients decay like `|k|^{-(m_*+1)}`, `HRS/PDE/Fourier.lean`), hence in `L^{2d/(d-1)}`. -/
theorem transport_bound_uniform (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (Λ lam₀ ΛV σ₀ : ℝ) (hlam₀ : 0 < lam₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (D : DynData d), D.s = s → 0 < D.invβ → D.invβ ≤ σ₀ →
        Torus.IsCk (PDE.mStar d + 2) D.V → Torus.cbNorm (PDE.mStar d + 2) D.V ≤ ΛV →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk (PDE.mStar d + 2) ρ →
        Torus.cbNorm (PDE.mStar d + 2) ρ ≤ Λ → (∀ x, lam₀ ≤ ρ x) →
        HasTransportBound d s (mfeTransport D ρ) C := by
  sorry

end HRS
