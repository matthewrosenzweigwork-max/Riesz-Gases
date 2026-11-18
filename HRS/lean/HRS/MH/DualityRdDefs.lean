import HRS.Whole.AppendixAAdjoint

/-!
# Definitions and proved glue lemmas shared by the packets of `duality_identity_rd_fix`; see `DualityRdSpec.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.DualityRd

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-! ### Shared definitions -/

/-- Regularity of a time-dependent test `f` on `[0,t] × ℝ^d` with prescribed time derivative `ft`
(the whole-space analogue of `HRS.IsC12Test`, `HRS/Stochastic/SelectedFlow.lean:128`, for
`Euc d` in place of the covering space of the torus).  Compared with the torus notion there are two additions that
are automatic on the compact torus but not on `ℝ^d`: the uniform bounds `bdd` on `f, ∇f, ∇²f`, and the linear growth
`lin_growth` of the time derivative.  `IsClassicalAdjointW` implies it with `ft = -generatorW` (`isC12TestRd`). -/
structure IsC12TestRd (t : ℝ) (f ft : ℝ → Euc d → ℝ) : Prop where
  c2 : ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 2 (f r)
  bdd : ∀ j ≤ 2, ∃ B : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖iteratedFDeriv ℝ j (f r) x‖ ≤ B
  cont_c2 : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => iteratedFDeriv ℝ j (f p.1) p.2
  time_deriv : ∀ x : Euc d, ∀ r ∈ Set.Ioo (0 : ℝ) t, HasDerivAt (fun r' => f r' x) (ft r x) r
  cont_time_deriv : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => ft p.1 p.2
  lin_growth : ∃ B : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, |ft r x| ≤ B * (1 + ‖x‖)

/-- A classical adjoint solution is an `IsC12TestRd` test with time derivative `-𝓛_r f^r`. -/
theorem _root_.HRS.Whole.IsClassicalAdjointW.isC12TestRd {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ}
    {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f) :
    IsC12TestRd t f (fun r x => -(generatorW C r (f r) x)) where
  c2 := hf.c2
  bdd := hf.bdd
  cont_c2 := hf.cont_c2
  time_deriv := hf.time_deriv
  cont_time_deriv := hf.cont_time_deriv.neg
  lin_growth := by
    obtain ⟨B, hB⟩ := hf.bdd_time_deriv
    exact ⟨B, fun r hr x => by simpa [abs_neg] using hB r hr x⟩

/-- `f r ∈ C_b²(ℝ^d)` for `r ∈ [0,t]`. -/
theorem IsC12TestRd.memCb {t : ℝ} {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) t) : MemCb 2 (f r) := by
  refine ⟨hf.c2 r hr, fun j hj => ?_⟩
  obtain ⟨B, hB⟩ := hf.bdd j hj
  exact ⟨B, by rintro _ ⟨x, rfl⟩; exact hB r hr x⟩

/-- The "drift test function" `ft + β⁻¹Δf - ∇V·∇f` against which the empirical and the mean-field measures are
paired in the Itô formula and in the time-dependent weak form. -/
def driftTestRd (D : WholeDyn d) (f ft : ℝ → Euc d → ℝ) (r : ℝ) (x : Euc d) : ℝ :=
  ft r x + D.invβ * Laplacian.laplacian (f r) x - inner ℝ (gradient D.V x) (gradient (f r) x)

/-- The integrand of the weak form of the mean-field equation in `IsWholeMeanFieldSolution.weak`
(`β⁻¹Δψ - ∇V·∇ψ` paired with `ρ`, plus the interaction pairing `B_ψ(ρ,ρ)`). -/
def mfGen (D : WholeDyn d) (ψ ρr : Euc d → ℝ) : ℝ :=
  Whole.pair (Whole.withDensityReal ρr)
      (fun x => D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x)) +
    interactionPairingW D ψ (Whole.withDensityReal ρr) (Whole.withDensityReal ρr)

/-- The Brownian direction `σ_{(i,j)} = √(2β⁻¹) e_{(i,j)}` of the configuration space `(ℝ^d)^N`
(the `σ k` of `ito_formula_additive`). -/
def noiseDir {N : ℕ} (D : WholeDyn d) (k : Fin N × Fin d) : EucConfig d N :=
  Real.sqrt (2 * D.invβ) • Pi.single k.1 (EuclideanSpace.single k.2 (1 : ℝ))

/-- The Itô integrand of the empirical martingale, truncated to `[0,t]` and without the factor `√(2β⁻¹)/N`:
exactly the integrand inside `DualityIdentityRdTrunc`. -/
def truncGradIntegrand {Ω : Type*} {N : ℕ} (t : ℝ) (f : ℝ → Euc d → ℝ) (X : ℝ≥0 → Ω → EucConfig d N) :
    ℝ → Ω → (Fin N × Fin d) → ℝ :=
  fun r ζ ia => if r ∈ Set.Icc (0 : ℝ) t then gradComp ia.2 (f r) (X (Real.toNNReal r) ζ ia.1) else 0

/-- The nonlocal term `𝒢_ρ ψ = Σ_j (∇g * (ρ (Mᵀ∇ψ)_j))_j` (cancellation convention): the part
`- Div g*(ρ Mᵀ∇ψ)` of `generatorW` is `- nlTermRd`. -/
def nlTermRd (D : WholeDyn d) (ρ ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ j : Fin d, (convGradConvW (rieszKernelGrad d D.s)
    (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x) j

/-- `generatorW` along the trajectory `ρ'` of `D.coeff ρ'`: `β⁻¹Δψ + ⟨b,∇ψ⟩ - 𝒢ψ`. -/
theorem generatorW_coeff (D : WholeDyn d) (ρ' : ℝ → Euc d → ℝ) (r : ℝ) (ψ : Euc d → ℝ) (x : Euc d) :
    generatorW (D.coeff ρ') r ψ x = D.invβ * Laplacian.laplacian ψ x +
      inner ℝ (meanFieldDriftW D (ρ' r) x) (gradient ψ x) - nlTermRd D (ρ' r) ψ x := rfl

/-- The kernel of `interactionPairingW` (junk `0` on the diagonal). -/
def pairKernelRd (D : WholeDyn d) (ψ : Euc d → ℝ) (x y : Euc d) : ℝ :=
  if x = y then 0 else
    inner ℝ (gradient ψ x - gradient ψ y) (Torus.matVec D.M (rieszKernelGrad d D.s (x - y)))

/-- Time slice of the regularity hypotheses used by the pairing algebra: `ρ` a probability density which is
`C_b³` with finite `⟨x⟩^{d+3}`-weighted sup norm (the `t`-slice of `IsRegularMFRd s 3 Λ T ρ`). -/
def RegSliceRd (ρ : Euc d → ℝ) : Prop :=
  Whole.IsProbDensity ρ ∧ MemCb 3 ρ ∧ weightedSupE 3 ((d : ℝ) + 3) ρ < ⊤

/-- The common hypotheses of the mean-field packets and of `duality_identity_rd_fix` on `(D, ρ)`. -/
structure MFData (s Λ T ΛV G₀ : ℝ) (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) : Prop where
  hs : D.s = s
  hs0 : 0 ≤ s
  hsd : s < d
  hinv : 0 ≤ D.invβ
  hV : VHypRd 2 ΛV G₀ D.V
  hρ : IsWholeMeanFieldSolution D T ρ
  hreg : IsRegularMFRd s 3 Λ T ρ

theorem MFData.one_le_d {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ}
    (h : MFData s Λ T ΛV G₀ D ρ) : 1 ≤ d := by
  have : (0 : ℝ) < d := lt_of_le_of_lt h.hs0 h.hsd
  exact_mod_cast this

theorem MFData.regSlice {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ}
    (h : MFData s Λ T ΛV G₀ D ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) : RegSliceRd (ρ r) :=
  ⟨h.hρ.density r hr, (h.hreg.1 r hr).1, (h.hreg.1 r hr).2.1⟩



theorem measurable_gradient_of_vhyp {ΛV G₀ : ℝ} {V : Euc d → ℝ} (hV : VHypRd 2 ΛV G₀ V) :
    Measurable (gradient V) := by
  have hc : Continuous (fderiv ℝ V) := hV.1.continuous_fderiv (by simp)
  unfold gradient
  exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp hc).measurable

/-- Branch dispatch of `SelectedFlowRd`: all three branches are contact-allowing strong solutions, with `M = 0` or null contact
occupation (branch (a): the contact set is empty; (b): `IsWholeCepaLepingleFlow.occupation`; (c): `M = 0`). -/
theorem flow_contact {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {P : Measure Ω} {D : WholeDyn d} {T : ℝ}
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (h : SelectedFlowRd P D T X₀ W X) :
    IsWholeContactStrongSolution P D T X₀ W X ∧
      (D.M = 0 ∨ ∀ᵐ ζ ∂P,
        volume {s : ℝ | s ∈ Set.Icc (0 : ℝ) T ∧ X (Real.toNNReal s) ζ ∈ eucCollisionSet d N} = 0) := by
  rcases h.flow with ⟨h1, -⟩ | ⟨-, -, -, -, h1⟩ | ⟨-, -, -, hM, h1⟩
  · refine ⟨⟨h1.init, h1.eqn, h1.cont, h1.adapted⟩, Or.inr ?_⟩
    filter_upwards [h1.no_collision] with ζ hζ
    have : {s : ℝ | s ∈ Set.Icc (0 : ℝ) T ∧ X (Real.toNNReal s) ζ ∈ eucCollisionSet d N} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun s hs => ?_
      refine hζ (Real.toNNReal s) ?_ hs.2
      rw [Real.coe_toNNReal _ hs.1.1]
      exact hs.1.2
    rw [this, measure_empty]
  · exact ⟨h1.toContact, Or.inr h1.occupation⟩
  · exact ⟨h1, Or.inl hM⟩


end HRS.MH.DualityRd
