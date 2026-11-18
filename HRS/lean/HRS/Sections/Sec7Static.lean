import HRS.Equilibrium.StaticLimits
import HRS.Prob.Gaussian

/-!
# Section 7 (static and abstract rows): statements (SPEC-7)

Specification file (statements with `sorry` proofs).  Sources (`HRS_periodic_main_20261008T010000Z.tex`):
* Lemma 7.4 `M:N:thm:static-edge` (TeX L7850-7868): scalar cubic contraction;
* Proposition 7.7 `M:F:thm:static` (TeX L8263-8272): static field correction;
* Proposition 7.15 `M:O:prop:tilt` (TeX L9592-9608): transfer under a bounded smooth initial weight;
* Proposition 7.16 `M:O:prop:slow` (TeX L9625-9627): a leading initial limit does not determine its
  first correction.

## Representation decisions
* `Q_{N,β}(μ)` is `HRS.modulatedGibbs (periodicRiesz d s) N β μ`; at `β = 0` it is `μ^{⊗N}` by definition
  (`gibbsNormalizer` is `1`), which is the convention `Q_{N,0}(μ) = μ^{⊗N}` of the lemma.
* The one-body resolvent `R_{β,μ}P_μ φ` is `HRS.responseInverse (periodicRiesz d s) μ β φ` (an a.e.-class,
  the solution of the response equation `h + β K_μ h = P_μ φ`, `μ(h) = 0`).  Where a point value is needed
  (Proposition 7.7, `ℓ_x`), the continuous representative `responseRep` is used.
* `C_b^k(B)` is `HRS.MemCb k` (all derivatives of order `≤ k` bounded) with norm `HRS.cbNorm k`
  (sum of suprema, TeX L510), and the unit ball `HRS.CbUnitBall`.
* Gaussian laws on `ℝ^p` are `ProbabilityTheory.multivariateGaussian 0 C` (the covariance matrix is positive
  semidefinite in all uses, so no junk value occurs); semidefinite covariances are allowed.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Sec7

variable {d : ℕ}

/-- The continuous representative `x ↦ (R_{γ,μ} P_μ ψ)(x)` of the response `R_{γ,μ}P_μψ`:
`P_μψ(x) - γ (K_μ h)(x)` with `h = responseInverse ..`.  Since `K_μ h` only depends on the `μ`-class of `h`,
this is a well-defined everywhere-defined function equal to `h` `μ`-a.e. (the response equation
`h + γ K_μ h = P_μ ψ`, TeX L924 / `N:eq:screening-operators` L7838). -/
def responseRep (g : Torus d → ℝ) (μ : Measure (Torus d)) (γ : ℝ) (ψ : Torus d → ℝ)
    (x : Torus d) : ℝ :=
  projMean μ ψ x - γ * Kop g μ (responseInverse g μ γ ψ) x

/-- The `j`-th standard basis vector of `ℝ^p` (as an element of the Euclidean space). -/
def stdVec {p : ℕ} (j : Fin p) : EuclideanSpace ℝ (Fin p) := EuclideanSpace.single j 1

/-- The statistics `W_N = (√N (μ_N(φ_a) - E[μ_N(φ_a)]))_a` of Lemma 7.4 under a law `Q` on configurations. -/
def centeredStat {p N : ℕ} (Q : Measure (Config d N)) (φ : Fin p → Torus d → ℝ) (X : Config d N) :
    EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun a => Real.sqrt N *
    (pair (empirical X) (φ a) - ∫ Y, pair (empirical Y) (φ a) ∂Q)

/-- Lemma 7.4 `M:N:thm:static-edge` (TeX L7850-7868), first part (`N:eq:static-edge`).
Let `0 ≤ s < d/2`, `β ≥ 0`, `μ = ρ dx` smooth positive, `X_N ∼ Q_{N,β}(μ)`, `φ_1,…,φ_p` fixed tests,
`r_a = R_{β,μ}P_μ φ_a`, `C_{ab} = μ(φ_a r_b)`, `κ_{abc} = μ(r_a r_b r_c)`, `W_N` the exactly centred
linear statistics and `Z ∼ N(0,C)` (possibly degenerate).  For each `F ∈ C_b^5(ℝ^p)`,
`E[F(W_N)] = E[F(Z)] + (6√N)⁻¹ ∑_{a,b,c} κ_{abc} E[∂_{abc}F(Z)] + o(N^{-1/2})`, i.e. `√N` times the
remainder tends to `0`; the `o(N^{-1/2})` is for each fixed `F` (TeX: "For each `F ∈ C_b^5`").
`∂_{abc}F(Z)` is `D³F(Z)[e_a,e_b,e_c]`.

Standing assumptions: `d ≥ 2` (M L419); smooth positive `μ` (TeX L7835, "smooth positive probability
measure").
AMBIGUITY (TeX L7843): "fixed tests `φ_1,…,φ_p`" has no regularity hypothesis; the proof (L7992-8010)
uses smooth `φ_b` (`∇φ_b = ∇r_b + β∇g*(r_bμ)`, test `v_a·∇φ_b`), so the tests are taken smooth.
Technical hypotheses: `hd : 2 ≤ d` is the standing dimension assumption (not in the lemma itself);
smoothness of the tests as just discussed. -/
theorem static_edge (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β : ℝ) (hβ : 0 ≤ β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (p : ℕ) (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    let μ := withDensityReal ρ
    let r : Fin p → Torus d → ℝ := fun a => responseInverse (periodicRiesz d s) μ β (φ a)
    let C : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b => ∫ x, φ a x * r b x ∂μ
    let κ : Fin p → Fin p → Fin p → ℝ := fun a b c => ∫ x, r a x * r b x * r c x ∂μ
    ∀ F : EuclideanSpace ℝ (Fin p) → ℝ, MemCb 5 F →
      Tendsto (fun N : ℕ => Real.sqrt N *
        (∫ X, F (centeredStat (modulatedGibbs (periodicRiesz d s) N β μ) φ X)
            ∂(modulatedGibbs (periodicRiesz d s) N β μ) -
          ∫ z, F z ∂(multivariateGaussian 0 C) -
          (1 / (6 * Real.sqrt N)) * ∑ a, ∑ b, ∑ c, κ a b c *
            ∫ z, iteratedFDeriv ℝ 3 F z ![stdVec a, stdVec b, stdVec c] ∂(multivariateGaussian 0 C)))
        atTop (𝓝 0) := by
  sorry

/-- Lemma 7.4 `M:N:thm:static-edge` (TeX L7850-7868), scalar part (`N:eq:char-edge`): for a scalar test
`φ` with variance `v = μ(φ r) > 0` and `κ = μ(r³)`, `r = R_{β,μ}P_μφ`,
`E[e^{itW_N}] = e^{-vt²/2}(1 + (it)³κ/(6√N)) + o(N^{-1/2})` for fixed `t`, and uniformly for `t` in a fixed
compact interval (the fixed-`t` statement is the compact interval `[-|t|,|t|]`).  Same standing assumptions
and test regularity as `static_edge` (see its docstring). -/
theorem static_edge_char (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β : ℝ) (hβ : 0 ≤ β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    let μ := withDensityReal ρ
    let r : Torus d → ℝ := responseInverse (periodicRiesz d s) μ β φ
    let v : ℝ := ∫ x, φ x * r x ∂μ
    let κ : ℝ := ∫ x, r x ^ 3 ∂μ
    0 < v →
    ∀ T : ℝ, 0 < T → ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ t : ℝ, t ∈ Set.Icc (-T) T →
      ‖∫ X, Complex.exp (Complex.I * (t : ℂ) *
            ((Real.sqrt N * (pair (empirical X) φ -
              ∫ Y, pair (empirical Y) φ ∂(modulatedGibbs (periodicRiesz d s) N β μ)) : ℝ) : ℂ))
          ∂(modulatedGibbs (periodicRiesz d s) N β μ) -
        Complex.exp (-(v : ℂ) * (t : ℂ) ^ 2 / 2) *
          (1 + (Complex.I * (t : ℂ)) ^ 3 * (κ : ℂ) / (6 * (Real.sqrt N : ℂ)))‖ ≤ ε / Real.sqrt N := by
  sorry

/-! ### Proposition 7.7: static field correction -/

/-- The element `ℓ_x ∈ E_r` of `F:eq:ell` (TeX L8253-8255): `⟨φ, ℓ_x⟩ = (R_{γ,μ} P_μ φ)(x)`, defined through its
real Fourier coefficients `ℓ_x(e_k) = (R_{γ,μ}P_μ e_k)(x)` (`e_k = Torus.realMode k`), with the continuous
representative `responseRep`. -/
def ellPt (g : Torus d → ℝ) (μ : Measure (Torus d)) (γ : ℝ) (r : ℝ) (x : Torus d) : NegSobolev d r :=
  NegSobolev.ofSeq r fun k => responseRep g μ γ (Torus.realMode k) x

/-- Proposition 7.7 `M:F:thm:static` (TeX L8263-8272), `F:eq:static-field`.  Let `μ = ρ dx` be smooth and
strictly positive, `γ ≥ 0` (`γ = 0` is the product law `μ^{⊗N}`), `X_N ∼ Q_{N,γ}(μ)`,
`W_N = √N(μ_N - E[μ_N]) ∈ E_r`, and `G` a centred Gaussian random element of `E_r` with
`Cov(G(φ),G(ψ)) = μ(φ R P_μ ψ)`.  With `K_{γ,μ} = ∫ ℓ_x^{⊗3} dμ(x) ∈ E_r^{⊗̂3}` (`F:eq:K0`), uniformly over
the unit ball `‖Φ‖_{C_b^5(E_r)} ≤ 1`,
`√N (E Φ(W_N) - E Φ(G)) - (1/6) E⟨D³Φ(G), K_{γ,μ}⟩ → 0`.
Here the pairing of the continuous trilinear form `D³Φ(G)` with the Bochner integral `K = ∫ ℓ_x^{⊗3}dμ` is
`∫ D³Φ(G)[ℓ_x,ℓ_x,ℓ_x] dμ(x)` (the pairing is continuous on the projective tensor product); the supremum
tending to `0` is written `∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∀ Φ ∈ ball`.

Standing assumptions/AMBIGUITY (TeX L8248-8262): the order `r` of `E_r` is not fixed in the statement; the
proof uses `r = 2d + 6` (`b_k = ⟨k⟩^{-d-3}`, TeX L8284-8289; also L8504, L9171), which is imposed
(`hr`).  `0 ≤ s < d/2` is the standing assumption of the Hilbert--Schmidt range (TeX L7893, "For the
remainder of Sections `N:sec:chaos`-`sec:path-tensor`, assume `s < d/2`") and `d ≥ 2` (M L419).
Technical hypotheses: `G` is a probability measure on `E_r` (a random element). -/
theorem static_field (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (r : ℝ)
    (hr : r = 2 * (d : ℝ) + 6) (γ : ℝ) (hγ : 0 ≤ γ) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ Φ ∈ CbUnitBall (NegSobolev d r) 5,
      |Real.sqrt N *
          (∫ X, Φ (zetaE r (modulatedGibbs (periodicRiesz d s) N γ (withDensityReal ρ)) X)
              ∂(modulatedGibbs (periodicRiesz d s) N γ (withDensityReal ρ)) - ∫ F, Φ F ∂G) -
        (1 / 6) * ∫ F, ∫ x, iteratedFDeriv ℝ 3 Φ F
            ![ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x,
              ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x,
              ellPt (periodicRiesz d s) (withDensityReal ρ) γ r x] ∂(withDensityReal ρ) ∂G| ≤ ε := by
  sorry

/-! ### Proposition 7.15: transfer under a bounded smooth initial weight -/

/-- The law `γ` tilted by the weight `g`: `g γ / ∫ g dγ` (with a `lintegral` normaliser). -/
def weightTilt {α : Type*} [MeasurableSpace α] (γ : Measure α) (g : α → ℝ) : Measure α :=
  (∫⁻ a, ENNReal.ofReal (g a) ∂γ)⁻¹ • γ.withDensity fun a => ENNReal.ofReal (g a)

/-! #### Auxiliary lemmas for Proposition 7.15 (tilted expansions) -/

namespace Tilt715Aux

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cbNorm_nonneg_aux (k : ℕ) (Φ : E → ℝ) : 0 ≤ HRS.cbNorm k Φ := by
  unfold HRS.cbNorm
  exact Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem norm_iter_le_cbNorm {k : ℕ} {Φ : E → ℝ} (hΦ : HRS.MemCb k Φ) {j : ℕ} (hj : j ≤ k) (x : E) :
    ‖iteratedFDeriv ℝ j Φ x‖ ≤ HRS.cbNorm k Φ := by
  have h1 := le_ciSup (hΦ.2 j hj) x
  have h2 : (⨆ z : E, ‖iteratedFDeriv ℝ j Φ z‖) ≤ HRS.cbNorm k Φ := by
    unfold HRS.cbNorm
    exact Finset.single_le_sum (f := fun i => ⨆ z : E, ‖iteratedFDeriv ℝ i Φ z‖)
      (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  exact h1.trans h2

theorem abs_le_cbNorm_aux {k : ℕ} {Φ : E → ℝ} (hΦ : HRS.MemCb k Φ) (x : E) :
    |Φ x| ≤ HRS.cbNorm k Φ := by
  have h := norm_iter_le_cbNorm hΦ (Nat.zero_le k) x
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h

theorem cbNorm_zero_le_aux (k : ℕ) (Φ : E → ℝ) : HRS.cbNorm 0 Φ ≤ HRS.cbNorm k Φ := by
  unfold HRS.cbNorm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ (Nat.zero_le k)))
    fun _ _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem memCb_mul_bound {Φ Ψ : E → ℝ} (hΦ : HRS.MemCb 5 Φ) (hΨ : HRS.MemCb 5 Ψ) :
    HRS.MemCb 5 (fun x => Ψ x * Φ x) ∧
      HRS.cbNorm 5 (fun x => Ψ x * Φ x) ≤ 63 * HRS.cbNorm 5 Ψ * HRS.cbNorm 5 Φ := by
  have hcd : ContDiff ℝ ((5 : ℕ) : WithTop ℕ∞) (fun x => Ψ x * Φ x) := hΨ.1.mul hΦ.1
  have hpt : ∀ n : ℕ, n ≤ 5 → ∀ x : E, ‖iteratedFDeriv ℝ n (fun x => Ψ x * Φ x) x‖ ≤
      2 ^ n * HRS.cbNorm 5 Ψ * HRS.cbNorm 5 Φ := by
    intro n hn x
    refine (norm_iteratedFDeriv_mul_le hΨ.1 hΦ.1 x (n := n) (by exact_mod_cast hn)).trans ?_
    have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i Ψ x‖ *
          ‖iteratedFDeriv ℝ (n - i) Φ x‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * HRS.cbNorm 5 Ψ * HRS.cbNorm 5 Φ := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have h1 := norm_iter_le_cbNorm hΨ (show i ≤ 5 by omega) x
          have h2 := norm_iter_le_cbNorm hΦ (show n - i ≤ 5 by omega) x
          have h0 : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 h0) h2 (norm_nonneg _)
            (mul_nonneg h0 (cbNorm_nonneg_aux 5 Ψ))
      _ = 2 ^ n * HRS.cbNorm 5 Ψ * HRS.cbNorm 5 Φ := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
  have hbdd : ∀ n : ℕ, n ≤ 5 → BddAbove (Set.range fun x : E =>
      ‖iteratedFDeriv ℝ n (fun x => Ψ x * Φ x) x‖) := fun n hn =>
    ⟨2 ^ n * HRS.cbNorm 5 Ψ * HRS.cbNorm 5 Φ, by rintro _ ⟨x, rfl⟩; exact hpt n hn x⟩
  refine ⟨⟨hcd, hbdd⟩, ?_⟩
  unfold HRS.cbNorm
  calc ∑ j ∈ Finset.range (5 + 1), ⨆ x : E, ‖iteratedFDeriv ℝ j (fun x => Ψ x * Φ x) x‖
      ≤ ∑ j ∈ Finset.range (5 + 1), 2 ^ j * HRS.cbNorm 5 Ψ * HRS.cbNorm 5 Φ :=
        Finset.sum_le_sum fun j hj => ciSup_le fun x =>
          hpt j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) x
    _ = 63 * HRS.cbNorm 5 Ψ * HRS.cbNorm 5 Φ := by
        simp [Finset.sum_range_succ]
        ring

theorem memCb_comp_clm {q : ℕ} (π₀ : E →L[ℝ] EuclideanSpace ℝ (Fin q)) {w : EuclideanSpace ℝ (Fin q) → ℝ}
    (hw : HRS.MemCb 5 w) : HRS.MemCb 5 (fun x => w (π₀ x)) := by
  refine ⟨hw.1.comp π₀.contDiff, fun j hj => ?_⟩
  obtain ⟨M, hM⟩ := hw.2 j hj
  refine ⟨M * ‖π₀‖ ^ j, ?_⟩
  rintro _ ⟨x, rfl⟩
  show ‖iteratedFDeriv ℝ j (w ∘ π₀) x‖ ≤ _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right π₀ hw.1 x (by exact_mod_cast hj)]
  have hMx : ‖iteratedFDeriv ℝ j w (π₀ x)‖ ≤ M := hM ⟨π₀ x, rfl⟩
  calc ‖(iteratedFDeriv ℝ j w (π₀ x)).compContinuousLinearMap fun _ => π₀‖
      ≤ ‖iteratedFDeriv ℝ j w (π₀ x)‖ * ∏ _i : Fin j, ‖π₀‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ j w (π₀ x)‖ * ‖π₀‖ ^ j := by simp
    _ ≤ M * ‖π₀‖ ^ j := mul_le_mul_of_nonneg_right hMx (by positivity)

theorem integral_weightTilt_aux [MeasurableSpace E] [BorelSpace E] {γ : Measure E}
    [IsProbabilityMeasure γ] {G : E → ℝ}
    (hG : Continuous G) (hG0 : ∀ x, 0 ≤ G x) (hGi : Integrable G γ) (F : E → ℝ) :
    ∫ x, F x ∂(Sec7.weightTilt γ G) = (∫ x, G x * F x ∂γ) / (∫ x, G x ∂γ) := by
  have hmeas : Measurable (fun x => ENNReal.ofReal (G x)) :=
    ENNReal.measurable_ofReal.comp hG.measurable
  have hint0 : 0 ≤ ∫ x, G x ∂γ := integral_nonneg hG0
  have hlin : (∫⁻ a, ENNReal.ofReal (G a) ∂γ).toReal = ∫ x, G x ∂γ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hGi (Filter.Eventually.of_forall hG0),
      ENNReal.toReal_ofReal hint0]
  unfold Sec7.weightTilt
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) F, ENNReal.toReal_inv, hlin]
  have hcongr : (∫ x, (ENNReal.ofReal (G x)).toReal • F x ∂γ) = ∫ x, G x * F x ∂γ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hG0 x)]
  rw [hcongr, smul_eq_mul, div_eq_inv_mul]

theorem ratio_error {z₀ z Num Den a α β e1 e2 δ M1 M2 M3 M4 E1 E2 : ℝ} (hz₀ : 0 < z₀)
    (hz : z₀ ≤ z) (hzM : z ≤ M4) (hD : z₀ / 2 ≤ Den) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hNum : Num = a + δ * α + e1) (hDen : Den = z + δ * β + e2)
    (ha : |a| ≤ M1) (hα : |α| ≤ M2) (hβ : |β| ≤ M3) (he1 : |e1| ≤ E1) (he2 : |e2| ≤ E2)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) (hM4 : 0 ≤ M4) (hE2 : 0 ≤ E2) :
    |Num / Den - (a / z + δ * (α / z - a * β / z ^ 2))| ≤
      (2 / z₀ ^ 3) * (M2 * M4 + M1 * M3) * (M3 * δ ^ 2 + E2) + (2 / z₀ ^ 2) * (M4 * E1 + M1 * E2) := by
  have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz
  have hDpos : 0 < Den := lt_of_lt_of_le (by positivity) hD
  have hkey : Num / Den - (a / z + δ * (α / z - a * β / z ^ 2)) =
      δ * (α * z - a * β) * (z - Den) / (Den * z ^ 2) + (e1 * z - a * e2) / (Den * z) := by
    rw [hNum]
    field_simp
    rw [hDen]
    ring
  have hzD : z - Den = -(δ * β + e2) := by linarith
  have hK : 0 ≤ M2 * M4 + M1 * M3 := by positivity
  have hX : |α * z - a * β| ≤ M2 * M4 + M1 * M3 := by
    calc |α * z - a * β| ≤ |α * z| + |a * β| := abs_sub _ _
      _ = |α| * |z| + |a| * |β| := by rw [abs_mul, abs_mul]
      _ ≤ M2 * M4 + M1 * M3 := by
        rw [abs_of_pos hzpos]
        exact add_le_add (mul_le_mul hα hzM hzpos.le hM2) (mul_le_mul ha hβ (abs_nonneg _) hM1)
  have hY : |δ * β + e2| ≤ M3 * δ + E2 := by
    calc |δ * β + e2| ≤ |δ * β| + |e2| := abs_add_le _ _
      _ = δ * |β| + |e2| := by rw [abs_mul, abs_of_nonneg hδ0]
      _ ≤ δ * M3 + E2 := add_le_add (mul_le_mul_of_nonneg_left hβ hδ0) he2
      _ = M3 * δ + E2 := by ring
  have hT1 : |δ * (α * z - a * β) * (z - Den) / (Den * z ^ 2)| ≤
      δ * (M2 * M4 + M1 * M3) * (M3 * δ + E2) / ((z₀ / 2) * z₀ ^ 2) := by
    have hnum : |δ * (α * z - a * β) * (z - Den)| ≤ δ * (M2 * M4 + M1 * M3) * (M3 * δ + E2) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hδ0, hzD, abs_neg]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hX hδ0) hY (abs_nonneg _) (mul_nonneg hδ0 hK)
    rw [abs_div, abs_of_pos (mul_pos hDpos (pow_pos hzpos 2))]
    refine div_le_div₀ (mul_nonneg (mul_nonneg hδ0 hK) (add_nonneg (mul_nonneg hM3 hδ0) hE2)) hnum
      (by positivity) ?_
    exact mul_le_mul hD (pow_le_pow_left₀ hz₀.le hz 2) (by positivity) hDpos.le
  have hT2 : |(e1 * z - a * e2) / (Den * z)| ≤ (M4 * E1 + M1 * E2) / ((z₀ / 2) * z₀) := by
    have hE1 : 0 ≤ E1 := le_trans (abs_nonneg _) he1
    have hnum : |e1 * z - a * e2| ≤ M4 * E1 + M1 * E2 := by
      calc |e1 * z - a * e2| ≤ |e1 * z| + |a * e2| := abs_sub _ _
        _ = |e1| * |z| + |a| * |e2| := by rw [abs_mul, abs_mul]
        _ ≤ E1 * M4 + M1 * E2 := by
          rw [abs_of_pos hzpos]
          exact add_le_add (mul_le_mul he1 hzM hzpos.le hE1) (mul_le_mul ha he2 (abs_nonneg _) hM1)
        _ = M4 * E1 + M1 * E2 := by ring
    rw [abs_div, abs_of_pos (mul_pos hDpos hzpos)]
    refine div_le_div₀ (by positivity) hnum (by positivity) ?_
    exact mul_le_mul hD hz (by positivity) hDpos.le
  have hb1 : δ * (M2 * M4 + M1 * M3) * (M3 * δ + E2) / ((z₀ / 2) * z₀ ^ 2) ≤
      (2 / z₀ ^ 3) * (M2 * M4 + M1 * M3) * (M3 * δ ^ 2 + E2) := by
    have e : δ * (M2 * M4 + M1 * M3) * (M3 * δ + E2) / ((z₀ / 2) * z₀ ^ 2) =
        (2 / z₀ ^ 3) * (M2 * M4 + M1 * M3) * (δ * (M3 * δ + E2)) := by
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith
  have hb2 : (M4 * E1 + M1 * E2) / ((z₀ / 2) * z₀) = (2 / z₀ ^ 2) * (M4 * E1 + M1 * E2) := by
    field_simp
  rw [hkey]
  calc |δ * (α * z - a * β) * (z - Den) / (Den * z ^ 2) + (e1 * z - a * e2) / (Den * z)|
      ≤ |δ * (α * z - a * β) * (z - Den) / (Den * z ^ 2)| + |(e1 * z - a * e2) / (Den * z)| :=
        abs_add_le _ _
    _ ≤ δ * (M2 * M4 + M1 * M3) * (M3 * δ + E2) / ((z₀ / 2) * z₀ ^ 2) +
        (M4 * E1 + M1 * E2) / ((z₀ / 2) * z₀) := add_le_add hT1 hT2
    _ ≤ (2 / z₀ ^ 3) * (M2 * M4 + M1 * M3) * (M3 * δ ^ 2 + E2) +
        (2 / z₀ ^ 2) * (M4 * E1 + M1 * E2) := by
        rw [← hb2]
        exact add_le_add hb1 le_rfl

theorem abs_integral_le_cb [MeasurableSpace E] {k : ℕ} {Φ : E → ℝ} (hΦ : HRS.MemCb k Φ)
    (μ : Measure E) [IsProbabilityMeasure μ] : |∫ x, Φ x ∂μ| ≤ HRS.cbNorm k Φ := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := Φ) (C := HRS.cbNorm k Φ)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_le_cbNorm_aux hΦ x)
  rw [Real.norm_eq_abs] at h
  simpa using h

theorem integrable_memCb [MeasurableSpace E] [BorelSpace E] {k : ℕ} {Φ : E → ℝ} (hΦ : HRS.MemCb k Φ)
    (μ : Measure E) [IsFiniteMeasure μ] : MeasureTheory.Integrable Φ μ :=
  MeasureTheory.Integrable.of_bound (hΦ.1.continuous.aestronglyMeasurable) (HRS.cbNorm k Φ)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_le_cbNorm_aux hΦ x)

theorem memCb_one : HRS.MemCb 5 (fun _ : E => (1 : ℝ)) := by
  refine ⟨contDiff_const, fun j _ => ⟨1, ?_⟩⟩
  rintro _ ⟨x, rfl⟩
  by_cases hj0 : j = 0
  · subst hj0
    dsimp only
    rw [norm_iteratedFDeriv_zero]
    simp
  · rw [iteratedFDeriv_const_of_ne hj0]
    simp

theorem cbNorm_one_pos : 1 ≤ HRS.cbNorm 5 (fun _ : E => (1 : ℝ)) := by
  have h0 : HRS.cbNorm 0 (fun _ : E => (1 : ℝ)) = 1 := by
    unfold HRS.cbNorm
    simp [norm_iteratedFDeriv_zero]
  have h1 := cbNorm_zero_le_aux (E := E) 5 (fun _ : E => (1 : ℝ))
  rw [h0] at h1
  exact h1

end Tilt715Aux

/-- Proposition 7.15 `M:O:prop:tilt` (TeX L9592-9608).  `E` is a Banach path space with a bounded (linear,
`docs/ISSUES.md` Q3) time-zero observation `π₀ : E → ℝ^r`; the family `(X_N)` (laws `ν i N`, `i` ranging over
an index set, the TeX's "family") and centred Gaussian laws `γ i` satisfy the base expansion
`|E F(X_N) - E F(Z) - N^{-1/2} 𝒜(F)| ≤ r_N ‖F‖_{C_b^5(E)}` with `r_N = o(N^{-1/2})` and bounded linear
functionals `𝒜 i` on `C_b^5(E)` (`‖𝒜‖ ≤ A`).  For `w ∈ C_b^5(ℝ^r)` nonnegative with
`z = E w(π₀Z) ≥ z₀ > 0`, the reweighted expectation `E_N^w[F(X_N)] = E[w(π₀X_N)F(X_N)]/E[w(π₀X_N)]`
satisfies, for all `N` large, uniformly in `F ∈ C_b^5(E)` and in the family index,
`E_N^w F = E[wF(Z)]/z + N^{-1/2}{𝒜((w∘π₀)F)/z - E[w(π₀Z)F(Z)]𝒜(w∘π₀)/z²} + O((r_N+N^{-1})‖F‖_{C_b^5})`
(first conjunct), and the new leading path law is that of `Z` tilted by `w(π₀Z)` (TeX L9598): `E_N^w F` is within
`C(N^{-1/2} + r_N)‖F‖_{C_b^5}` of `∫ F d(weightTilt γ (w∘π₀))` (second conjunct; `E[wF(Z)]/z` is this integral).
The constant `C` depends only on `z₀` (i.e. `z⁻¹`), `w`, `π₀`, `A` (chosen before the family and `r_N`);
the threshold `N₀` depends only on the sequence `r_N` (and `C, z₀, w, π₀, A`), not on the family (TeX proof
L9609-9613: the denominator is `≥ z/2` "for all sufficiently large `N`").  The statement with a single `Z` is the case of a one-point index set.
`𝒜` is a function on all functions `E → ℝ` (junk off `C_b^5`); additivity, homogeneity and the bound are
assumed on `C_b^5(E)` only.
Technical hypotheses: `E` second countable/Borel for measurability of `C_b^5` functions; `ν`, `γ`
probability measures. -/
theorem tilt_transfer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] (q : ℕ) (π₀ : E →L[ℝ] EuclideanSpace ℝ (Fin q))
    (w : EuclideanSpace ℝ (Fin q) → ℝ) (hw : MemCb 5 w) (hwnn : ∀ x, 0 ≤ w x)
    (z₀ : ℝ) (hz₀ : 0 < z₀) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, ∀ rN : ℕ → ℝ, Tendsto (fun N : ℕ => Real.sqrt N * rN N) atTop (𝓝 0) →
      ∃ N₀ : ℕ, ∀ {ι : Type} (ν : ι → ℕ → Measure E) (γ : ι → Measure E)
      (𝒜 : ι → (E → ℝ) → ℝ),
      (∀ i N, IsProbabilityMeasure (ν i N)) → (∀ i, IsProbabilityMeasure (γ i)) →
      (∀ i, IsCenteredGaussian (γ i)) →
      (∀ i, ∀ F G : E → ℝ, MemCb 5 F → MemCb 5 G → 𝒜 i (F + G) = 𝒜 i F + 𝒜 i G) →
      (∀ i, ∀ (c : ℝ) (F : E → ℝ), MemCb 5 F → 𝒜 i (c • F) = c * 𝒜 i F) →
      (∀ i, ∀ F : E → ℝ, MemCb 5 F → |𝒜 i F| ≤ A * cbNorm 5 F) →
      (∀ i N, 1 ≤ N → ∀ F : E → ℝ, MemCb 5 F →
        |∫ x, F x ∂(ν i N) - ∫ x, F x ∂(γ i) - (Real.sqrt N)⁻¹ * 𝒜 i F| ≤ rN N * cbNorm 5 F) →
      (∀ i, z₀ ≤ ∫ x, w (π₀ x) ∂(γ i)) →
      ∀ N ≥ N₀, 1 ≤ N → ∀ i, ∀ F : E → ℝ, MemCb 5 F →
        |(∫ x, w (π₀ x) * F x ∂(ν i N)) / (∫ x, w (π₀ x) ∂(ν i N)) -
            ((∫ x, w (π₀ x) * F x ∂(γ i)) / (∫ x, w (π₀ x) ∂(γ i)) +
              (Real.sqrt N)⁻¹ * (𝒜 i (fun x => w (π₀ x) * F x) / (∫ x, w (π₀ x) ∂(γ i)) -
                (∫ x, w (π₀ x) * F x ∂(γ i)) / (∫ x, w (π₀ x) ∂(γ i)) ^ 2 *
                  𝒜 i (fun x => w (π₀ x))))| ≤
          C * (rN N + (N : ℝ)⁻¹) * cbNorm 5 F ∧
        |(∫ x, w (π₀ x) * F x ∂(ν i N)) / (∫ x, w (π₀ x) ∂(ν i N)) -
            ∫ x, F x ∂(weightTilt (γ i) fun x => w (π₀ x))| ≤
          C * ((Real.sqrt N)⁻¹ + rN N) * cbNorm 5 F := by
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, K0 = HRS.cbNorm 5 (fun x => w (π₀ x)) := ⟨_, rfl⟩
  have hG : HRS.MemCb 5 (fun x => w (π₀ x)) := Tilt715Aux.memCb_comp_clm π₀ hw
  have hK0nn : 0 ≤ K0 := hK0 ▸ Tilt715Aux.cbNorm_nonneg_aux 5 _
  have hz3 : (0 : ℝ) ≤ 128 / z₀ ^ 3 := div_nonneg (by norm_num) (pow_nonneg hz₀.le 3)
  have hz2 : (0 : ℝ) ≤ 128 / z₀ ^ 2 := div_nonneg (by norm_num) (pow_nonneg hz₀.le 2)
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = (128 / z₀ ^ 3) * A * K0 ^ 2 * (A * K0 + K0) +
      (128 / z₀ ^ 2) * K0 ^ 2 := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = 63 * A * K0 / z₀ + A * K0 ^ 2 / z₀ ^ 2 := ⟨_, rfl⟩
  have hC₁nn : 0 ≤ C₁ := by
    rw [hC₁]
    exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hz3 hA) (sq_nonneg _))
      (add_nonneg (mul_nonneg hA hK0nn) hK0nn)) (mul_nonneg hz2 (sq_nonneg _))
  have hC₂nn : 0 ≤ C₂ := by
    rw [hC₂]
    exact add_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) hK0nn) hz₀.le)
      (div_nonneg (mul_nonneg hA (sq_nonneg _)) (pow_nonneg hz₀.le 2))
  refine ⟨C₁ + C₂, fun rN hrN => ?_⟩
  -- the threshold: `√N⁻¹ (A K0) + rN K0 < z₀/2` and `N ≥ 1`
  have hsqrt_inv : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hrN0 : Tendsto (fun N : ℕ => rN N) atTop (𝓝 0) := by
    have h := hsqrt_inv.mul hrN
    rw [zero_mul] at h
    refine h.congr' (eventually_atTop.2 ⟨1, fun N hN => ?_⟩)
    have hne : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast (show 0 < N by omega))).ne'
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hev : ∀ᶠ N : ℕ in atTop, (Real.sqrt N)⁻¹ * (A * K0) + rN N * K0 < z₀ / 2 := by
    have h := (hsqrt_inv.mul_const (A * K0)).add (hrN0.mul_const K0)
    rw [show (0 : ℝ) * (A * K0) + 0 * K0 = 0 by ring] at h
    exact (tendsto_order.1 h).2 (z₀ / 2) (half_pos hz₀)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop 1))
  refine ⟨N₀, fun {ι} ν γ 𝒜 hνP hγP hγG hadd hsm hbd hexp hz N hN hN1 i F hF => ?_⟩
  obtain ⟨hthr, -⟩ := hN₀ N hN
  haveI := hνP i N
  haveI := hγP i
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsq1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN1)
  set δ := (Real.sqrt N)⁻¹ with hδdef
  have hδ0 : 0 ≤ δ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hδ1 : δ ≤ 1 := inv_le_one_of_one_le₀ hsq1
  have hδsq : δ ^ 2 = (N : ℝ)⁻¹ := by
    rw [hδdef, inv_pow, Real.sq_sqrt hNr.le]
  -- `rN N ≥ 0`, from the expansion for the constant test function `1`
  have hrNnn : 0 ≤ rN N := by
    have h1 := hexp i N hN1 (fun _ => (1 : ℝ)) Tilt715Aux.memCb_one
    have e1 : ∫ x, (1 : ℝ) ∂(ν i N) = 1 := by simp
    have e2 : ∫ x, (1 : ℝ) ∂(γ i) = 1 := by simp
    rw [e1, e2, sub_self, zero_sub, abs_neg] at h1
    have hcb := Tilt715Aux.cbNorm_one_pos (E := E)
    by_contra hneg
    push_neg at hneg
    have h2 : rN N * HRS.cbNorm 5 (fun _ : E => (1 : ℝ)) < 0 :=
      mul_neg_of_neg_of_pos hneg (by linarith)
    have h3 := abs_nonneg ((Real.sqrt N)⁻¹ * 𝒜 i (fun _ : E => (1 : ℝ)))
    linarith
  have hG_cb : HRS.cbNorm 5 (fun x => w (π₀ x)) = K0 := hK0.symm
  have hcbFnn : 0 ≤ HRS.cbNorm 5 F := Tilt715Aux.cbNorm_nonneg_aux 5 F
  set Num := ∫ x, w (π₀ x) * F x ∂(ν i N) with hNum_def
  set Den := ∫ x, w (π₀ x) ∂(ν i N) with hDen_def
  set a := ∫ x, w (π₀ x) * F x ∂(γ i) with ha_def
  set z := ∫ x, w (π₀ x) ∂(γ i) with hz_def
  set α := 𝒜 i (fun x => w (π₀ x) * F x) with hα_def
  set β := 𝒜 i (fun x => w (π₀ x)) with hβ_def
  set cbF := HRS.cbNorm 5 F with hcbF_def
  have hGF : HRS.MemCb 5 (fun x => w (π₀ x) * F x) := (Tilt715Aux.memCb_mul_bound hF hG).1
  have hGFb : HRS.cbNorm 5 (fun x => w (π₀ x) * F x) ≤ 63 * K0 * cbF := by
    have h := (Tilt715Aux.memCb_mul_bound hF hG).2
    rw [← hK0] at h
    exact h
  have hzle : z₀ ≤ z := hz i
  have hz_le : z ≤ K0 := by
    calc z ≤ |z| := le_abs_self _
      _ ≤ K0 := by
        rw [hz_def, ← hG_cb]
        exact Tilt715Aux.abs_integral_le_cb hG (γ i)
  have hGcont : Continuous (fun x => w (π₀ x)) := hG.1.continuous
  have hG0 : ∀ x, 0 ≤ w (π₀ x) := fun x => hwnn _
  have hGint : MeasureTheory.Integrable (fun x => w (π₀ x)) (γ i) :=
    Tilt715Aux.integrable_memCb hG (γ i)
  have ha_bd : |a| ≤ K0 * cbF := by
    rw [ha_def]
    have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := γ i)
      (f := fun x => w (π₀ x) * F x) (C := K0 * cbF)
      (MeasureTheory.ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (Tilt715Aux.abs_le_cbNorm_aux hG x |>.trans (le_of_eq hG_cb))
          (Tilt715Aux.abs_le_cbNorm_aux hF x) (abs_nonneg _) hK0nn)
    rw [Real.norm_eq_abs] at h
    simpa using h
  have hα_bd : |α| ≤ A * (63 * K0 * cbF) := by
    have h := hbd i (fun x => w (π₀ x) * F x) hGF
    exact h.trans (mul_le_mul_of_nonneg_left hGFb hA)
  have hβ_bd : |β| ≤ A * K0 := by
    have h := hbd i (fun x => w (π₀ x)) hG
    rw [hG_cb] at h
    exact h
  have he1 : |Num - a - δ * α| ≤ rN N * (63 * K0 * cbF) := by
    have h := hexp i N hN1 (fun x => w (π₀ x) * F x) hGF
    exact h.trans (mul_le_mul_of_nonneg_left hGFb hrNnn)
  have he2 : |Den - z - δ * β| ≤ rN N * K0 := by
    have h := hexp i N hN1 (fun x => w (π₀ x)) hG
    rw [hG_cb] at h
    exact h
  have hDen_ge : z₀ / 2 ≤ Den := by
    have h1 : |δ * β| ≤ δ * (A * K0) := by
      rw [abs_mul, abs_of_nonneg hδ0]
      exact mul_le_mul_of_nonneg_left hβ_bd hδ0
    have h2 := abs_le.mp he2
    have h3 := abs_le.mp h1
    linarith [h2.1, h2.2, h3.1, h3.2, hthr, hzle]
  have hR := Tilt715Aux.ratio_error (z₀ := z₀) (z := z) (Num := Num) (Den := Den) (a := a)
    (α := α) (β := β) (e1 := Num - a - δ * α) (e2 := Den - z - δ * β) (δ := δ)
    (M1 := K0 * cbF) (M2 := A * (63 * K0 * cbF)) (M3 := A * K0) (M4 := K0)
    (E1 := rN N * (63 * K0 * cbF)) (E2 := rN N * K0) hz₀ hzle hz_le hDen_ge hδ0 hδ1
    (by ring) (by ring) ha_bd hα_bd hβ_bd he1 he2 (mul_nonneg hK0nn hcbFnn)
    (mul_nonneg hA (mul_nonneg (mul_nonneg (by norm_num) hK0nn) hcbFnn)) (mul_nonneg hA hK0nn)
    hK0nn (mul_nonneg hrNnn hK0nn)
  -- the bracket
  have hbracket : (128 / z₀ ^ 3) * A * K0 ^ 2 * (A * K0 * δ ^ 2 + rN N * K0) +
      (128 / z₀ ^ 2) * K0 ^ 2 * rN N ≤ C₁ * (δ ^ 2 + rN N) := by
    have e : C₁ * (δ ^ 2 + rN N) -
        ((128 / z₀ ^ 3) * A * K0 ^ 2 * (A * K0 * δ ^ 2 + rN N * K0) +
          (128 / z₀ ^ 2) * K0 ^ 2 * rN N) =
        (128 / z₀ ^ 3) * A * K0 ^ 2 * K0 * δ ^ 2 + (128 / z₀ ^ 3) * A * K0 ^ 2 * (A * K0) * rN N +
          (128 / z₀ ^ 2) * K0 ^ 2 * δ ^ 2 := by
      rw [hC₁]
      ring
    have hnn : 0 ≤ (128 / z₀ ^ 3) * A * K0 ^ 2 * K0 * δ ^ 2 +
        (128 / z₀ ^ 3) * A * K0 ^ 2 * (A * K0) * rN N + (128 / z₀ ^ 2) * K0 ^ 2 * δ ^ 2 := by
      refine add_nonneg (add_nonneg ?_ ?_) ?_
      · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hz3 hA) (sq_nonneg _)) hK0nn) (sq_nonneg _)
      · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hz3 hA) (sq_nonneg _))
          (mul_nonneg hA hK0nn)) hrNnn
      · exact mul_nonneg (mul_nonneg hz2 (sq_nonneg _)) (sq_nonneg _)
    linarith
  have key1 : |Num / Den - (a / z + δ * (α / z - a * β / z ^ 2))| ≤ cbF * C₁ * (δ ^ 2 + rN N) := by
    calc |Num / Den - (a / z + δ * (α / z - a * β / z ^ 2))|
        ≤ (2 / z₀ ^ 3) * (A * (63 * K0 * cbF) * K0 + K0 * cbF * (A * K0)) * (A * K0 * δ ^ 2 + rN N * K0) +
            (2 / z₀ ^ 2) * (K0 * (rN N * (63 * K0 * cbF)) + K0 * cbF * (rN N * K0)) := hR
      _ = cbF * ((128 / z₀ ^ 3) * A * K0 ^ 2 * (A * K0 * δ ^ 2 + rN N * K0) +
            (128 / z₀ ^ 2) * K0 ^ 2 * rN N) := by ring
      _ ≤ cbF * (C₁ * (δ ^ 2 + rN N)) := mul_le_mul_of_nonneg_left hbracket hcbFnn
      _ = cbF * C₁ * (δ ^ 2 + rN N) := by ring
  constructor
  · -- first conjunct
    have e_inside : a / z + δ * (α / z - a / z ^ 2 * β) = a / z + δ * (α / z - a * β / z ^ 2) := by
      ring
    rw [e_inside]
    refine key1.trans ?_
    rw [hδsq]
    have hpos : 0 ≤ C₂ * (rN N + (N : ℝ)⁻¹) * cbF :=
      mul_nonneg (mul_nonneg hC₂nn (add_nonneg hrNnn (inv_nonneg.mpr hNr.le))) hcbFnn
    have e3 : (C₁ + C₂) * (rN N + (N : ℝ)⁻¹) * cbF =
        cbF * C₁ * ((N : ℝ)⁻¹ + rN N) + C₂ * (rN N + (N : ℝ)⁻¹) * cbF := by ring
    rw [e3]
    linarith
  · -- second conjunct
    have hint : ∫ x, F x ∂(Sec7.weightTilt (γ i) fun x => w (π₀ x)) = a / z :=
      Tilt715Aux.integral_weightTilt_aux hGcont hG0 hGint F
    rw [hint]
    have hzpos : 0 < z := lt_of_lt_of_le (by linarith) hzle
    have hX : |δ * (α / z - a * β / z ^ 2)| ≤ δ * (cbF * C₂) := by
      rw [abs_mul, abs_of_nonneg hδ0]
      refine mul_le_mul_of_nonneg_left ?_ hδ0
      calc |α / z - a * β / z ^ 2| ≤ |α / z| + |a * β / z ^ 2| := abs_sub _ _
        _ = |α| / z + |a| * |β| / z ^ 2 := by
            rw [abs_div, abs_div, abs_mul, abs_of_pos hzpos, abs_of_pos (pow_pos hzpos 2)]
        _ ≤ (A * (63 * K0 * cbF)) / z₀ + (K0 * cbF) * (A * K0) / z₀ ^ 2 := by
            refine add_le_add (div_le_div₀ (mul_nonneg hA (by positivity)) ?_ hz₀ hzle) ?_
            · exact hα_bd.trans (le_refl _)
            · refine div_le_div₀ (mul_nonneg (mul_nonneg hK0nn hcbFnn) (mul_nonneg hA hK0nn)) ?_
                (pow_pos hz₀ 2) (pow_le_pow_left₀ hz₀.le hzle 2)
              exact mul_le_mul ha_bd hβ_bd (abs_nonneg _) (mul_nonneg hK0nn hcbFnn)
        _ = cbF * C₂ := by rw [hC₂]; ring
    have hfin : |Num / Den - a / z| ≤ cbF * C₁ * (δ ^ 2 + rN N) + δ * (cbF * C₂) := by
      have hsplit : Num / Den - a / z = (Num / Den - (a / z + δ * (α / z - a * β / z ^ 2))) +
          δ * (α / z - a * β / z ^ 2) := by ring
      rw [hsplit]
      exact (abs_add_le _ _).trans (add_le_add key1 hX)
    refine hfin.trans ?_
    have h1 : 0 ≤ C₁ * δ * (1 - δ) := mul_nonneg (mul_nonneg hC₁nn hδ0) (by linarith)
    have e5 : (C₁ + C₂) * (δ + rN N) * cbF - (cbF * C₁ * (δ ^ 2 + rN N) + δ * (cbF * C₂)) =
        cbF * (C₁ * δ * (1 - δ)) + cbF * (C₂ * rN N) := by ring
    have h3 : 0 ≤ cbF * (C₁ * δ * (1 - δ)) := mul_nonneg hcbFnn h1
    have h4 : 0 ≤ cbF * (C₂ * rN N) := mul_nonneg hcbFnn (mul_nonneg hC₂nn hrNnn)
    linarith

/-! ### Proposition 7.16: slow initial rates -/

/-- Proposition 7.16 `M:O:prop:slow` (TeX L9625-9627), with the construction of its proof (L9628-9636).
Fix `d ≥ 2`, `0 ≤ s < d/2`, `β > 0`, `m > d/2`.  For every positive sequence `a_N → 0` with `√N a_N → ∞`
(an arbitrarily slow rate) there are preparations `f_N` (probability measures on `𝕋^{dN}`) such that
* homogeneous periodic: `f_N` is invariant under simultaneous translation of all particles;
* uniformly bounded density relative to the fixed positive-temperature Gibbs ensemble
  `Q_{N,β}(dx)` (`= P_{N,β}` with `V = 0` because `ĝ(0) = 0`);
* exact first-marginal centring: the first marginal is Haar measure;
* the initial fluctuation field `η_N^0 = √N(μ_N - dx) ∈ E_m` converges in law to a probability measure `L`;
and yet there are `Φ ∈ C_b^5(E_m)` and `c > 0` with `|E_{f_N}Φ(η_N^0) - L(Φ)| ≥ c a_N` for all large `N`;
since `√N a_N → ∞`, no expansion `E Φ(η_N^0) = L(Φ) + O(N^{-1/2})` with the fixed reference `L` holds.
This is the formal reading of "do not imply an expansion with a remainder of order `N^{-1/2}`; the error
can tend to zero arbitrarily more slowly" (the convergence of the error to `0` is the convergence in law).
AMBIGUITY (TeX L9625-9627): the statement is informal; the limit reference is the law `L` of the leading
initial limit (in the TeX proof, the Gaussian tilted by `1 + ε e^{-|z|²}`), left existentially quantified;
the preparation class includes only the upper density bound (the TeX proof also gives a lower bound). -/
theorem slow_correction (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β : ℝ)
    (hβ : 0 < β) (m : ℝ) (hm : (d : ℝ) / 2 < m) (a : ℕ → ℝ) (ha_pos : ∀ N, 0 < a N)
    (ha0 : Tendsto a atTop (𝓝 0)) (ha : Tendsto (fun N : ℕ => Real.sqrt N * a N) atTop atTop) :
    ∃ (f : ∀ N : ℕ, Measure (Config d N)) (L : Measure (NegSobolev d m))
      (Φ : NegSobolev d m → ℝ) (c : ℝ),
      (∀ N, IsProbabilityMeasure (f N)) ∧ IsProbabilityMeasure L ∧
      (∀ N, ∀ b : Torus d, (f N).map (fun X i => X i + b) = f N) ∧
      (∃ B : ℝ, ∀ N, f N ≪ modulatedGibbs (periodicRiesz d s) N β volume ∧
        ∀ᵐ X ∂(modulatedGibbs (periodicRiesz d s) N β volume),
          (f N).rnDeriv (modulatedGibbs (periodicRiesz d s) N β volume) X ≤ ENNReal.ofReal B) ∧
      (∀ N, 1 ≤ N → firstMarginal (f N) = volume) ∧
      (∀ G : NegSobolev d m → ℝ, Continuous G → (∃ M, ∀ x, |G x| ≤ M) →
        Tendsto (fun N : ℕ => ∫ X, G (etaE m X volume) ∂(f N)) atTop (𝓝 (∫ y, G y ∂L))) ∧
      MemCb 5 Φ ∧ 0 < c ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, c * a N ≤ |∫ X, Φ (etaE m X volume) ∂(f N) - ∫ y, Φ y ∂L| := by
  sorry

end Sec7

end HRS

end
