import HRS.Main.GFSpec2

/-!
# Packet GF-SPEC, part 3: initial coupling (GF-INIT), law identification (GF-LAW), the single-window Wasserstein
comparison (GF-WP), the Powers-Stormer bound for the covariance coupling in trace-norm form (GF-BURES), and the pullback of strong solutions

Sorried STATEMENTS unless marked PROVED.  TeX: M L2445-2478 (proof of Theorem 2.1), in particular L2456-2459 ("a single
adapted coupling of the entire martingales") and L2459-2465 (transport variant).  See `GFSpec1.lean` for the representation
decisions and `GFSpec7.lean` for the assembly.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

/-! ### The deterministic covariance density -/

/-- The deterministic covariance density `r ↦ C̄_N^r = covForm γ q ρ_N^r` on `[0,T]`, extended by `0` (NEW definition,
pointwise equal to `Uniform.Q54c.covDens`; this is the form for which `IsDetCovDensity` holds, the density `ρ` being
arbitrary outside `[0,T]`, and for which the truncated covariation of `IsAdaptedGaussianCoupling.gaussian` coincides with
the untruncated one of `smooth_path_comparison_proof`). -/
def covDensT (γ q T : ℝ) (ρ : ℝ → Torus d → ℝ) :
    ℝ → NegSobolev d γ →L[ℝ] NegSobolev d γ →L[ℝ] ℝ :=
  fun σ => if σ ∈ Set.Icc 0 T then covForm γ q (withDensityReal (ρ σ)) else 0

/-- **GF-DET** (technical).  SORRIED.  Estimated size: S (the lemmas exist: `Q54c.isDetCovDensity_covDens`,
`Q54c.covDens_continuousOn`, `Q54c.weak_continuity`; not imported here because the `Q54c` chain is heavy).
`r ↦ C̄_N^r = covForm γ q ρ_N^r` (zero outside `[0,T]`) is a deterministic covariance density: entrywise measurable (weak continuity of
`ρ_N` plus continuity of `x ↦ b_{x,j} ∈ E_γ`), trace class with trace `≤ 4 q d S_γ`. -/
theorem gf_detCovDensity (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (q : ℝ) (hq : 0 ≤ q) :
    IsDetCovDensity S.T (covDensT (S.γ : ℝ) q S.T (S.ρ N)) := by
  sorry

/-! ### Pullback of strong solutions (PROVED) -/

/-- PROVED.  A strong solution pulls back along a measure-preserving map (needed on the enlargement of `gf_init_enlargement`
for `duality_identity_all`, `gf_fluc_continuous`, …).  All fields are a.e. statements or measurability, which transfer
through `MeasurePreserving` (`projectPath (Y ∘ π) = (projectPath Y) ∘ π` is definitional). -/
theorem isStrongSolution_comp {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {N : ℕ}
    {P : Measure Ω} {P' : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π P' P) {D : DynData d} {T : ℝ}
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : IsStrongSolution P D T X₀ W X) :
    IsStrongSolution P' D T (fun ω' => X₀ (π ω')) (fun t ω' => W t (π ω')) (fun t ω' => X t (π ω')) := by
  obtain ⟨Y, hY, hXY⟩ := h.lift
  refine ⟨⟨fun t ω' => Y t (π ω'), ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hπ.quasiMeasurePreserving.ae hY] with ω' hω'
    exact hω'
  · funext t ω'
    exact congrFun (congrFun hXY t) (π ω')
  · exact hπ.quasiMeasurePreserving.ae h.init
  · exact hπ.quasiMeasurePreserving.ae h.cont
  · exact fun t => (h.adapted t).comp hπ.measurable
  · exact hπ.quasiMeasurePreserving.ae h.no_collision

/-! ### Measurable continuous modification, transport of stochastic convolutions -/

/-- **GF-MOD** (technical; needed because `maximal_estimate_meas` only gives `AEMeasurable (Z t)` while
`smooth_path_comparison_proof` requires `Measurable (Z t)` AND a.s. continuity of the same process).  SORRIED.  Estimated
size: S-M.  An a.s.-continuous process on `[0,T]` with a.e.-measurable time sections has a modification `Z'` with measurable time
sections and *everywhere* continuous paths on `[0,T]`, `Z' t = Z t` a.s. for every `t ∈ [0,T]`
(`Z' t ω = lim_{q → t, q ∈ ℚ} Z q'` on the measurable set where the rational-time paths are uniformly continuous, `0` elsewhere,
with `Z q'` measurable versions at rational times). -/
theorem gf_measurable_modification {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (T : ℝ) (Z : ℝ → Ω → E) (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Z t) P) :
    ∃ Z' : ℝ → Ω → E, (∀ t, Measurable (Z' t)) ∧ (∀ ω, ContinuousOn (fun t => Z' t ω) (Set.Icc 0 T)) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, Z' t =ᵐ[P] Z t := by
  sorry

/-- PROVED.  `IsStochConv` only depends on the convolution up to a.e. equality. -/
theorem isStochConv_congr_ae {Ω : Type*} [MeasurableSpace Ω] {H E : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [NormedAddCommGroup E] [InnerProductSpace ℝ E] {P : Measure Ω}
    {VE : ℝ → ℝ → E →L[ℝ] E} {j : H →L[ℝ] E} {M : ℝ → Ω → H} {a t : ℝ} {Z Z' : Ω → E}
    (h : IsStochConv P VE j M a t Z) (hZ : Z =ᵐ[P] Z') : IsStochConv P VE j M a t Z' := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := h ε hε
  refine ⟨δ, hδ, fun n r h0 hn hmono hmesh => ?_⟩
  refine lt_of_le_of_lt (le_of_eq ?_) (hh n r h0 hn hmono hmesh)
  refine lintegral_congr_ae ?_
  filter_upwards [hZ] with ω hω
  rw [hω]

/-- PROVED.  Transport of a stochastic convolution along a measure-preserving map: the Riemann sums of `M ∘ π` are those of
`M` composed with `π`, and the `L²`-distance is preserved by `π` (a.e.-measurability of `Z` and of the `M_τ` is used for
`lintegral_map'`). -/
theorem isStochConv_comp {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} {P' : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π P' P)
    {VE : ℝ → ℝ → E →L[ℝ] E} {j : H →L[ℝ] E} {M : ℝ → Ω → H} {a t : ℝ} {Z : Ω → E}
    (hMm : ∀ τ, AEMeasurable (fun ω => j (M τ ω)) P) (hZm : AEMeasurable Z P)
    (h : IsStochConv P VE j M a t Z) :
    IsStochConv P' VE j (fun τ ω' => M τ (π ω')) a t (fun ω' => Z (π ω')) := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := h ε hε
  refine ⟨δ, hδ, fun n r h0 hn hmono hmesh => ?_⟩
  have hjm : ∀ i : Fin n, AEMeasurable (fun ω => j (M (r i.succ) ω - M (r i.castSucc) ω)) P := fun i => by
    have := (hMm (r i.succ)).sub (hMm (r i.castSucc))
    have e : (fun ω => j (M (r i.succ) ω - M (r i.castSucc) ω)) =
        (fun ω => j (M (r i.succ) ω)) - fun ω => j (M (r i.castSucc) ω) := by
      funext ω; simp [map_sub]
    rw [e]; exact this
  have hrs : AEMeasurable (riemannSum VE j M t r) P := by
    unfold riemannSum
    have := Finset.aemeasurable_sum (μ := P) (Finset.univ : Finset (Fin n))
      (f := fun i ω => VE t (r i.castSucc) (j (M (r i.succ) ω - M (r i.castSucc) ω)))
      fun i _ => (show AEMeasurable (fun ω => VE t (r i.castSucc)
          (j (M (r i.succ) ω - M (r i.castSucc) ω))) P from
        (VE t (r i.castSucc)).continuous.measurable.comp_aemeasurable (hjm i))
    simpa [Finset.sum_fn] using this
  have hf : AEMeasurable (fun ω => ‖Z ω - riemannSum VE j M t r ω‖ₑ ^ 2) P :=
    ((hZm.sub hrs).enorm).pow_const 2
  have := hh n r h0 hn hmono hmesh
  calc ∫⁻ ω', ‖Z (π ω') - riemannSum VE j (fun τ ω' => M τ (π ω')) t r ω'‖ₑ ^ 2 ∂P'
      = ∫⁻ ω, ‖Z ω - riemannSum VE j M t r ω‖ₑ ^ 2 ∂P := by
        rw [← hπ.map_eq, lintegral_map' (by rw [hπ.map_eq]; exact hf) hπ.aemeasurable]
        rfl
    _ < _ := this

/-! ### GF-INIT: the initial coupling -/

/-- **GF-INIT** (TeX M L2456-2459: "`X₀' = Aη°` is `ℱ_0`-measurable"; hypothesis of Theorem 2.1: `(X₀, η°)` independent of the
noise).  SORRIED.  Estimated size: L.
The hypothesis of Theorem 2.1 only makes `(X₀, η°)` independent of the Brownian path, whereas
`smooth_path_comparison_proof` needs `X₀' = Aη°` to be `ℱ_0`-measurable for a Brownian filtration to which `X` is adapted.
Enlargement: `Ω' = Ω × E_γ`, `P' = P ⊗ κ` with `κ(ω, ·) = condDistrib η° (X₀) (X₀ ω)` (`E_γ` and `Config d N` are standard Borel),
`η'(ω,e) = e`, `π = fst`, `ℱ'_t = (ℱ_t pulled back) ∨ σ(η') ∨ null sets`; `W'` stays an `ℱ'`-Brownian motion because `η'` is
conditionally independent of everything given `X₀ ∈ ℱ_0`.  The conclusion records exactly what the later steps use:
`π` measure preserving, `ℱ ⊆ ℱ'` (pulled back), the pulled-back solution is still a *filtered* solution for `ℱ'`,
`η'` is `ℱ'_0`-measurable, and `(X₀∘π, η')` has the law of `(X₀, η°)` (so `ε_{N,p}`, and the law of `Y_N`'s initial value, are
unchanged).  The pulled-back strong solution property is `isStrongSolution_comp`.

Repaired 2026-10-17, ISSUES GFB4: the link `hX0 : X 0 = X₀` a.s. was missing (`X₀` was unrelated to `X`; counterexample in ISSUES). -/
theorem gf_init_enlargement (S : GeneralSetup d) (N : ℕ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X)
    (hX0 : ∀ᵐ ω ∂P, X 0 ω = X₀ ω)
    (η₀ : Ω → NegSobolev d (S.γ : ℝ)) (hη : Measurable η₀)
    (hind : IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P) :
    ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (π : Ω' → Ω) (_ : MeasurePreserving π P' P) (ℱ' : Filtration ℝ mΩ')
      (η' : Ω' → NegSobolev d (S.γ : ℝ)),
      (∀ τ, (ℱ τ).comap π ≤ ℱ' τ) ∧
      IsFilteredSolution P' ℱ' (fun t ω' k => W' t (π ω') k) (fun t ω' => W t (π ω'))
        (fun t ω' => X t (π ω')) ∧
      Measurable[ℱ' 0] η' ∧
      P'.map (fun ω' => (X₀ (π ω'), η' ω')) = P.map (fun ω => (X₀ ω, η₀ ω)) := by
  sorry

/-! ### GF-LAW: law identification at level `m` -/

/-- **GF-LAW** (TeX M L2456-2459; the identification of the Gaussian surrogate `X̄ = V(·,0)X₀' + ∫V dG` with the linear
fluctuation solution `Y_N` of `H:eq:linear-equation`/`H:eq:linear-mild`).  SORRIED.  Estimated size: L-XL.
Let `G` be an `E_γ`-valued continuous martingale with the deterministic covariation `C̄_N^r = covForm γ q_N ρ_N^r` (hence
Gaussian with independent increments, Lévy), independent of the `ℱ'_0`-measurable initial datum `X₀'` (`hGind`), and
`Z̄ = ∫V dG` its stochastic convolution in `E_m` (`IsStochConv`, continuous, measurable).  If `Y` solves the linear equation
(`IsLinearFluctuationSolution`, Gaussian part independent of `Y₀`) with initial value `Y₀` of the law of `j X₀'`, then the
laws on `C([0,T]; E_m)` of `Y` and of `X̄ = V(·,0) j X₀' + Z̄` coincide.
Proof: both are continuous processes (`Q54c.toPath_law_eq` reduces to finite-dimensional laws, in coordinates
`⟨k⟩^{-m}Ŷ^t(k)`); `Y_t(φ) = Y₀(U^{0,t}φ) + (Gaussian)` with the covariance `2q ∫ ρ_r ∇U^{r,t}φ·∇U^{r,t'}ψ dr`, and on the
other side `⟨Z̄_t, φ⟩` is the Wiener integral `∫⟨dG_r, U^{r,t}φ⟩` (the Gaussian half of GF-PAIR: stochastic Fubini against
`C¹` deterministic integrands), centered Gaussian jointly in `(t,φ)` with the same covariance since
`covForm γ q ρ (U^{r,t}φ-dual, U^{r,t'}ψ-dual) = 2q ∫ ∇U^{r,t}φ·∇U^{r,t'}ψ ρ dx`; independence from `Y₀`/`X₀'` is `hGind`.
Cf. `Q54c.toPath_law_eq`, `Q54c.noise_gaussian`, `Q54c.PdeSetup.Data.fdd_eq` (the analogues at level `n+4`). -/
theorem gf_law_identification (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (hN : 2 ≤ N) (m K : ℝ) (hm : (S.γ : ℝ) ≤ m)
    (EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m)) (hEV : GFEvo S M N m K EV)
    {Ω Ω' : Type} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (ℱ' : Filtration ℝ mΩ') (X₀' : Ω' → NegSobolev d (S.γ : ℝ)) (hX₀' : Measurable X₀')
    (G : ℝ → Ω' → NegSobolev d (S.γ : ℝ))
    (hG : IsHilbertMartingaleWithCovariation P' ℱ' S.T G
      (fun r _ => covDensT (S.γ : ℝ) (qN S N) S.T (S.ρ N) r))
    (hGind : Indep (MeasurableSpace.comap X₀' inferInstance)
      (⨆ τ ∈ Set.Icc (0 : ℝ) S.T, MeasurableSpace.comap (G τ) inferInstance) P')
    (Zb : ℝ → Ω' → NegSobolev d m) (hZb : ∀ t ∈ Set.Icc (0 : ℝ) S.T, IsStochConv P' EV.VE EV.j G 0 t (Zb t))
    (hZbc : ∀ᵐ ω ∂P', ContinuousOn (fun t => Zb t ω) (Set.Icc 0 S.T)) (hZbm : ∀ t, Measurable (Zb t))
    (Y₀ : Ω → NegSobolev d m) (hY₀ : Measurable Y₀) (hlaw : P.map Y₀ = P'.map (fun ω' => EV.j (X₀' ω')))
    (Y : ℝ → Ω → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P (S.dynM M N) (S.ρ N) m (qN S N) S.T Y₀ Y) :
    law P (toPath m S.T Y) =
      law P' (windowPath 0 S.T (fun t ω' => EV.VE t 0 (EV.j (X₀' ω')) + Zb t ω')) := by
  sorry

/-! ### GF-WP: the single-window Wasserstein comparison -/

/-- **GF-WP** (TeX M L2457-2459 (single adapted coupling of the entire martingales), the single-window `EvolData`-based
version of the frozen `comparison_wasserstein`, `p = 1, 2`).  SORRIED.  Estimated size: L.
On one probability space carry the particle martingale `M`, a Gaussian-driven martingale `G`, and the *difference
martingale* `M - G` (stopped at `T`) with covariation density `Sd`, `‖Sd_r‖₁ ≤ cost_r` (exactly the fields `difference`, `cost` of
`IsAdaptedGaussianCoupling`, with `M`, `G` already composed with the projection `π`).  Let `X = V(·,0)jX₀ + Z + R`,
`X̄ = V(·,0)jX₀' + Z̄`, `Z = ∫V dM`, `Z̄ = ∫V dG`.  Then
`W_p(Law X, Law X̄) ≤ C ‖X₀ - X₀'‖_{L^p} + ‖R‖_{L^p(C_T E)} + C (E ∫_0^T cost_r dr)^{1/2}`
with `C = C(T,K)` (`windowPath 0 T`, sup norm; `p = 1,2` have the same right side, as in `comparison_wasserstein`).
Proof: the coupling `(X, X̄)` on `Ω` (`wassersteinE_le_cost`), `X - X̄ = V(·,0)j(X₀-X₀') + (Z - Z̄) + R`, `Z - Z̄` is the stochastic
convolution of the martingale `M - G` (linearity of `IsStochConv`), and `HRS.Uniform.Q45.maximal_estimate_meas` for `M - G`
gives `E sup ‖Z - Z̄‖² ≤ C E ∫ ‖Sd_r‖₁ dr` (uniqueness of `L²`-limits plus path continuity identifies it with the
maximal-estimate version); Minkowski.  No independence is used here (that is GF-LAW).

Repaired 2026-10-17, ISSUES GFB4: added `∀ t, Measurable (M t)`, `∀ t, Measurable (G t)` (`IsStochConv` is a lower integral; the
unrepaired statement is false for non-measurable `M`, `G`). -/
theorem gf_wasserstein_comparison (T K : ℝ) (hT : 0 ≤ T) (p : ℝ) (hp : p = 1 ∨ p = 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ)
        (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
        (S : EvolData H E) (_ : S.MaxHyp T K)
        (X₀ X₀' : Ω → H) (_ : Measurable X₀) (_ : Measurable X₀') (M G : ℝ → Ω → H)
        (_ : ∀ t, Measurable (M t)) (_ : ∀ t, Measurable (G t)) (Sd : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)) (cost : ℝ → Ω → ℝ)
        (_ : IsHilbertMartingaleWithCovariation P ℱ T (fun τ ω => M (min τ T) ω - G (min τ T) ω)
          (fun r ω => if r ≤ T then Sd r ω else 0))
        (_ : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → r ≤ T → traceNormForm (Sd r ω) ≤ cost r ω)
        (Z Zb R : ℝ → Ω → E)
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j M 0 t (Z t))
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j G 0 t (Zb t))
        (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
        (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 T))
        (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 T))
        (_ : ∀ t, Measurable (Z t)) (_ : ∀ t, Measurable (Zb t)) (_ : ∀ t, Measurable (R t))
        (X Xb : ℝ → Ω → E)
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, X t ω = S.VE t 0 (S.j (X₀ ω)) + Z t ω + R t ω)
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, Xb t ω = S.VE t 0 (S.j (X₀' ω)) + Zb t ω),
        wassersteinE p (law P (windowPath 0 T X)) (law P (windowPath 0 T Xb)) ≤
          ENNReal.ofReal C * (∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ p ∂P) ^ (1 / p) +
            (∫⁻ ω, ‖windowPath 0 T R ω‖ₑ ^ p ∂P) ^ (1 / p) +
            ENNReal.ofReal C *
              (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ∂P) ^ (1 / 2 : ℝ) := by
  sorry

/-! ### The covariance coupling in trace-norm form -/

/-- **GF-BURES** (Powers–Størmer form; TeX M L2121-2137 (Lemma 3.19), L2686 (`R:eq:Bures-bound`)).  SORRIED.  Estimated
size: S-M.  For nonnegative trace-class forms, `𝔟(C,D)² = Tr C + Tr D - 2‖D^{1/2}C^{1/2}‖₁ ≤ ‖C - D‖₁`.
Proof: `𝔟² ≤ ‖C^{1/2} - D^{1/2}‖²_{𝔖₂}` (as `‖D^{1/2}C^{1/2}‖₁ ≥ Tr(D^{1/2}C^{1/2})`) and
`HRS.powers_stormer` (`‖C^{1/2} - D^{1/2}‖²_{𝔖₂} ≤ ‖C - D‖₁`), the same inequality that proves `polar_coupling_cost`. -/
theorem gf_bures2_le_traceNorm {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] (C D : H →L[ℝ] H →L[ℝ] ℝ)
    (hC : IsTraceClassCov C) (hD : IsTraceClassCov D) : bures2 C D ≤ traceNormForm (C - D) := by
  sorry

end HRS.GF
