import HRS.MS.UniqFAux5

/-!
# UNIQ-F tie: uniqueness of classical adjoint solutions for the S5.7 coefficient `fixedEqCoeff`

`UqfCase b ν c ρ := 0 < ν ∨ UqfTie b c ρ` is the exact coverage (see the scope in `UniqFAux1`):

* `0 < ν`: any matrix `M`, any regime, free bounded time-dependent `c` (`uniqf_unique_of_pos`, maximum principle);
* `ν ∈ [0,ν*]` and the mean-field tie `c_t = M∇g*ρ_t - c₀` (`UqfTie`): the F-CAU engine (`uniqf_unique_tie`), all regimes of `FixedEqFcauHyp.regime`.

NOT covered: `ν = 0` with a free `c` that is not of the form `M∇g*ρ_t - c₀`.

* `uniqf_unique`, `uniqf_propagatorW_eq`: one family `(ν,c,ρ)` under the slice hypotheses of `fixed_equation` (level `ℓ ≥ b.k + 6`).
* `uniqf_unique_fe`, `uniqf_propagatorW_eq_fe`: BOTH families `(νN,cN,ρN)`, `(ν,c,ρ)` with exactly the density / drift hypothesis blocks of
  `fixed_equation` (level `b.k + 6 + ⌈d/2⌉ + 4 + ⌈d/2⌉`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.UniqF

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- the mean-field tie `c_t = M ∇g*ρ_t - c₀` on `[0,T]` (true for the coefficients of `WholeSetup`) -/
def UqfTie (b : WholeBounds d) (c : ℝ → Euc d → Euc d) (ρ : ℝ → Euc d → ℝ) : Prop :=
  ∃ c₀ : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) b.T, ∀ x, c t x =
    Torus.matVec b.M (convGradConvW (rieszKernelGrad d b.s) (ρ t) x) - c₀

/-- the covered part of the hypothesis space: positive viscosity, or the mean-field tie -/
def UqfCase (b : WholeBounds d) (ν : ℝ) (c : ℝ → Euc d → Euc d) (ρ : ℝ → Euc d → ℝ) : Prop :=
  0 < ν ∨ UqfTie b c ρ

/-- **`uniqf_unique`** -/
theorem uniqf_unique (b : WholeBounds d) (hb : b.Valid) {ν : ℝ} (hν0 : 0 ≤ ν) (hνs : ν ≤ b.νstar)
    {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ} (hF : FixedEqFcauHyp b ν c ρ) (hcase : UqfCase b ν c ρ)
    {ℓ : ℕ} (hℓ : b.k + 6 ≤ ℓ)
    (hdens : ∀ t ∈ Set.Icc (0 : ℝ) b.T, HRS.Whole.IsProbDensity (ρ t) ∧ ContDiff ℝ ℓ (ρ t) ∧
      weightedSupE ℓ b.L (ρ t) ≤ ENNReal.ofReal b.Λ)
    (hdrift : ∀ t ∈ Set.Icc (0 : ℝ) b.T, cbNormVecE ℓ (c t) ≤ ENNReal.ofReal b.Λ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) {φ : Euc d → ℝ} {f₁ f₂ : ℝ → Euc d → ℝ}
    (h₁ : IsClassicalAdjointW (fixedEqCoeff b.s b.M b.Q ν c ρ) t φ f₁)
    (h₂ : IsClassicalAdjointW (fixedEqCoeff b.s b.M b.Q ν c ρ) t φ f₂) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, f₁ r = f₂ r := by
  rcases hcase with hpos | ⟨c₀, htie⟩
  · exact uniqf_unique_of_pos b hb hpos (by omega) hdens hdrift ht h₁ h₂
  · exact uniqf_unique_tie b hb hν0 hνs hF (by omega) hdens c₀ htie ht h₁ h₂

/-- **`uniqf_propagatorW_eq`**: `propagatorW` is the classical solution -/
theorem uniqf_propagatorW_eq (b : WholeBounds d) (hb : b.Valid) {ν : ℝ} (hν0 : 0 ≤ ν) (hνs : ν ≤ b.νstar)
    {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ} (hF : FixedEqFcauHyp b ν c ρ) (hcase : UqfCase b ν c ρ)
    {ℓ : ℕ} (hℓ : b.k + 6 ≤ ℓ)
    (hdens : ∀ t ∈ Set.Icc (0 : ℝ) b.T, HRS.Whole.IsProbDensity (ρ t) ∧ ContDiff ℝ ℓ (ρ t) ∧
      weightedSupE ℓ b.L (ρ t) ≤ ENNReal.ofReal b.Λ)
    (hdrift : ∀ t ∈ Set.Icc (0 : ℝ) b.T, cbNormVecE ℓ (c t) ≤ ENNReal.ofReal b.Λ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW (fixedEqCoeff b.s b.M b.Q ν c ρ) t φ f) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, propagatorW (fixedEqCoeff b.s b.M b.Q ν c ρ) r t φ = f r :=
  uniqf_unique b hb hν0 hνs hF hcase hℓ hdens hdrift ht (HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩) hf

/-- **both families of `fixed_equation`**, with exactly its density and drift hypothesis blocks -/
theorem uniqf_unique_fe (b : WholeBounds d) (hb : b.Valid)
    {νN ν : ℝ} {cN c : ℝ → Euc d → Euc d} {ρN ρ : ℝ → Euc d → ℝ}
    (hνN0 : 0 ≤ νN) (hνNs : νN ≤ b.νstar) (hν0 : 0 ≤ ν) (hνs : ν ≤ b.νstar)
    (hFN : FixedEqFcauHyp b νN cN ρN) (hF : FixedEqFcauHyp b ν c ρ)
    (hcaseN : UqfCase b νN cN ρN) (hcase : UqfCase b ν c ρ)
    (hdens : ∀ t ∈ Set.Icc 0 b.T, HRS.Whole.IsProbDensity (ρN t) ∧ HRS.Whole.IsProbDensity (ρ t) ∧
        ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (ρN t) ∧
        ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (ρ t) ∧
        weightedSupE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) b.L (ρN t) ≤ ENNReal.ofReal b.Λ ∧
        weightedSupE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) b.L (ρ t) ≤ ENNReal.ofReal b.Λ)
    (hdrift : ∀ t ∈ Set.Icc 0 b.T, ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (cN t) ∧
        ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (c t) ∧
        cbNormVecE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (cN t) ≤ ENNReal.ofReal b.Λ ∧
        cbNormVecE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (c t) ≤ ENNReal.ofReal b.Λ) :
    (∀ t ∈ Set.Icc (0 : ℝ) b.T, ∀ (φ : Euc d → ℝ) (f₁ f₂ : ℝ → Euc d → ℝ),
      IsClassicalAdjointW (fixedEqCoeff b.s b.M b.Q νN cN ρN) t φ f₁ →
      IsClassicalAdjointW (fixedEqCoeff b.s b.M b.Q νN cN ρN) t φ f₂ → ∀ r ∈ Set.Icc (0 : ℝ) t, f₁ r = f₂ r) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) b.T, ∀ (φ : Euc d → ℝ) (f₁ f₂ : ℝ → Euc d → ℝ),
      IsClassicalAdjointW (fixedEqCoeff b.s b.M b.Q ν c ρ) t φ f₁ →
      IsClassicalAdjointW (fixedEqCoeff b.s b.M b.Q ν c ρ) t φ f₂ → ∀ r ∈ Set.Icc (0 : ℝ) t, f₁ r = f₂ r) := by
  refine ⟨fun t ht φ f₁ f₂ h₁ h₂ => ?_, fun t ht φ f₁ f₂ h₁ h₂ => ?_⟩
  · exact uniqf_unique b hb hνN0 hνNs hFN hcaseN (ℓ := b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (by omega)
      (fun t ht => ⟨(hdens t ht).1, (hdens t ht).2.2.1, (hdens t ht).2.2.2.2.1⟩)
      (fun t ht => (hdrift t ht).2.2.1) ht h₁ h₂
  · exact uniqf_unique b hb hν0 hνs hF hcase (ℓ := b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (by omega)
      (fun t ht => ⟨(hdens t ht).2.1, (hdens t ht).2.2.2.1, (hdens t ht).2.2.2.2.2⟩)
      (fun t ht => (hdrift t ht).2.2.2) ht h₁ h₂

/-- `propagatorW` is the classical solution, both families -/
theorem uniqf_propagatorW_eq_fe (b : WholeBounds d) (hb : b.Valid)
    {νN ν : ℝ} {cN c : ℝ → Euc d → Euc d} {ρN ρ : ℝ → Euc d → ℝ}
    (hνN0 : 0 ≤ νN) (hνNs : νN ≤ b.νstar) (hν0 : 0 ≤ ν) (hνs : ν ≤ b.νstar)
    (hFN : FixedEqFcauHyp b νN cN ρN) (hF : FixedEqFcauHyp b ν c ρ)
    (hcaseN : UqfCase b νN cN ρN) (hcase : UqfCase b ν c ρ)
    (hdens : ∀ t ∈ Set.Icc 0 b.T, HRS.Whole.IsProbDensity (ρN t) ∧ HRS.Whole.IsProbDensity (ρ t) ∧
        ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (ρN t) ∧
        ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (ρ t) ∧
        weightedSupE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) b.L (ρN t) ≤ ENNReal.ofReal b.Λ ∧
        weightedSupE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) b.L (ρ t) ≤ ENNReal.ofReal b.Λ)
    (hdrift : ∀ t ∈ Set.Icc 0 b.T, ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (cN t) ∧
        ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (c t) ∧
        cbNormVecE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (cN t) ≤ ENNReal.ofReal b.Λ ∧
        cbNormVecE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (c t) ≤ ENNReal.ofReal b.Λ) :
    (∀ t ∈ Set.Icc (0 : ℝ) b.T, ∀ (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ),
      IsClassicalAdjointW (fixedEqCoeff b.s b.M b.Q νN cN ρN) t φ f →
      ∀ r ∈ Set.Icc (0 : ℝ) t, propagatorW (fixedEqCoeff b.s b.M b.Q νN cN ρN) r t φ = f r) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) b.T, ∀ (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ),
      IsClassicalAdjointW (fixedEqCoeff b.s b.M b.Q ν c ρ) t φ f →
      ∀ r ∈ Set.Icc (0 : ℝ) t, propagatorW (fixedEqCoeff b.s b.M b.Q ν c ρ) r t φ = f r) := by
  obtain ⟨hN, hL⟩ := uniqf_unique_fe b hb hνN0 hνNs hν0 hνs hFN hF hcaseN hcase hdens hdrift
  exact ⟨fun t ht φ f hf => fun r hr => hN t ht φ _ _ (HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩) hf r hr,
    fun t ht φ f hf => fun r hr => hL t ht φ _ _ (HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩) hf r hr⟩

end HRS.MS.UniqF
