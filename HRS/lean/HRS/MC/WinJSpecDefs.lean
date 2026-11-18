import HRS.MC.E214O5

/-!
# Sorry-free vocabulary for the statements of `HRS/MC/WinJSpec.lean` (`winJ_compare`, row 2.14)

Nothing here is unproved; these definitions are only abbreviations and mixed objects used by the packet statements P1-P12
of `docs/MAIN_C_WINJ_SCOPE.md`.  Notation (all for a `StatDatum sd` of the prepared datum `S`):

* `Rp sd b hb` : the prepared regime `regime S β₀ hE` restarted at time `b` (`E213F.shift`);
* `Rs sd b hb` : the stationary regime `regime sd.Ss S.β sd.hEs` restarted at time `b`
  (its `D` is that of `Rp`, its density is the constant `ρβ`, by `sd.hD`, `sd.hρ`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.WinJ

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan HRS.MC.Sec7.PID HRS.MC.E213U3

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

/-- The prepared regime restarted at time `b ≥ 0`. -/
abbrev Rp (sd : StatDatum S β₀ m hE) (b : ℝ) (hb : 0 ≤ b) : Regime d :=
  HRS.MC.E213F.shift (regime S β₀ hE) b hb

/-- The stationary regime restarted at time `b ≥ 0`. -/
abbrev Rs (sd : StatDatum S β₀ m hE) (b : ℝ) (hb : 0 ≤ b) : Regime d :=
  HRS.MC.E213F.shift (regime sd.Ss S.β sd.hEs) b hb

/-- The difference kernel nodes `p(u) (1_{u ≤ t_i} V^{t_i,u} - 1_{u ≤ t_i} V̄^{t_i,u}) e` at the dyadic grid
`t_i = gridPt c c' n i` (prepared minus stationary, both restarted at `b`). -/
def kernelNodesW (sd : StatDatum S β₀ m hE) (b : ℝ) (hb : 0 ≤ b) (c c' : ℝ) (n : ℕ) (p : ℝ → ℝ)
    (e : NegSobolev d m) (u : ℝ) (i : ℕ) : NegSobolev d m :=
  kernelNodes (Rp sd b hb).D (Rp sd b hb).ρ m c c' n p e u i -
    kernelNodes (Rs sd b hb).D (Rs sd b hb).ρ m c c' n p e u i

/-- The difference of two polygonal paths built from two node families and two dynamics:
`polyPath D ρ .. v - polyPath D' ρ' .. v'` (an element of `𝒳_{m,T}`). -/
def polyPathMix (D D' : DynData d) (ρ ρ' : ℝ → Torus d → ℝ) (m T c c' : ℝ) (n : ℕ)
    (v v' : ℕ → NegSobolev d m) : PathSpace d m T :=
  polyPath D ρ m T c c' n v - polyPath D' ρ' m T c c' n v'

/-- The time-smoothed nuclear tensor of the kernel families `p(u) 1_{u ≤ t_i} V^{t_i,u} e_k` and
`q(u) 1_{u ≤ t_i} V^{t_i,u} e_l` of the regime `R`, with the node truncation `tr` applied to every node
(`tr = truncF m F` for the truncated bound, `tr = id` for the full one). -/
def nucK (R : Regime d) (m T c c' : ℝ) (n : ℕ) (p q : ℝ → ℝ) (k l : NonzeroLattice d)
    (tr : NegSobolev d m → NegSobolev d m) : TensorDual (PathSpace d m T) 2 :=
  nuc R.D R.ρ m T c c' n (fun u i => tr (kernelNodes R.D R.ρ m c c' n p (modeVec m k) u i))
    (fun u i => tr (kernelNodes R.D R.ρ m c c' n q (modeVec m l) u i))

/-- The evaluation predicate of the covariance tensor `τ_{kl}` of the regime `R` (as in the conclusion of
`E213M.e213m_cov`): `τ ∈ projTensor` and `τ(ℓ_a ⊗ ℓ_b) = ∫_{(c,c'] ∩ [0,t_a ∧ t_b]} p q ⟨V^{t_a,u} e_k, φ_a⟩ ⟨V^{t_b,u} e_l, φ_b⟩ du`. -/
def CovEval (R : Regime d) (m T : ℝ) (p q : ℝ → ℝ) (c c' : ℝ) (k l : NonzeroLattice d)
    (τ : TensorDual (PathSpace d m T) 2) : Prop :=
  τ ∈ projTensor (PathSpace d m T) 2 ∧
    ∀ (ta tb : ℝ) (φa φb : Torus d → ℝ) (l₁ l₂ : StrongDual ℝ (PathSpace d m T)),
      Torus.IsSmooth φa → Torus.IsSmooth φb →
      ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
      (∀ w, l₁ w = NegSobolev.eval (pathAt w ta) φa) → (∀ w, l₂ w = NegSobolev.eval (pathAt w tb) φb) →
      τ (prodForm l₁ l₂) = ∫ u in Set.Ioc c c' ∩ Set.Icc 0 (min ta tb), p u * q u *
        NegSobolev.eval (Vprop R.D R.ρ m ta u (modeVec m k)) φa *
        NegSobolev.eval (Vprop R.D R.ρ m tb u (modeVec m l)) φb

/-- **The difference version of `E213U3.Good`**: for the coefficient `z` on `(α, β]` there are window tensors `X`, `X'`
of the two regimes (`SJW`, series form) with `‖X - X'‖ ≤ C ∫_{(α,β]} e^{-c(a-v)} e^{-κ v} ‖z v‖ dv`. -/
def GoodDiff (R R' : Regime d) (r m T a C c κ : ℝ) (z : ℝ → NegSobolev d r) (α β : ℝ) : Prop :=
  ∃ X X' : TensorDual (PathSpace d m T) 2, SJW R r m T a z (Set.Ioc α β) X ∧
    SJW R' r m T a z (Set.Ioc α β) X' ∧
    ‖X - X'‖ ≤ C * ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖

end HRS.MC.WinJ

end
