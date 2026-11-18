import HRS.Main.HeadlineEdgeworth
import HRS.MC.E213A
import HRS.MC.E213B
import HRS.MC.E213D
import HRS.MC.E213E2
import HRS.MC.E213H
import HRS.MC.E213G
import HRS.MC.E213L
import HRS.MC.E213M5
import HRS.MC.E213N3
import HRS.MC.E213O2
import HRS.MC.E213P
import HRS.MC.E213Q2
import HRS.MC.E213TSymm

/-!
# Definitions for the Theorem 2.13 (`edgeworth_window`) chain

Split off from `HRS.MC.E213Plan` (Step 0 of `docs/MC_E213_ASSEMBLY.md` section (b)): the setting `rLvl`, `regime`, the
generic building blocks, `GaussData` and the window objects `Zwin`, `Dwin`, `Jwin`, `Kwin`, `Kproj`, and every other
definition of the plan that does not depend on a sorried lemma (`canonFut`, `Ucan`, `PrepFamily`, `rsA`, `rsJ`, `JwinP`,
`errVal`, `ExpData`, `ExpData.expr`), with the proved helper lemmas that only use those definitions.  Nothing here is
`sorry`.  The names stay in the namespace `HRS.MC.E213Plan`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213Plan

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}
/-! ## §0  Setting -/

/-- The Sobolev level of the particle/Gaussian fields: `r = 2d + 6` (TeX L8284, L8504, L9171). -/
def rLvl (d : ℕ) : ℝ := 2 * (d : ℝ) + 6

/-- `r ≤ m` under `EdgeworthHyp` (`m > 3d + 8`). -/
theorem rLvl_le {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m) : rLvl d ≤ m :=
  HRS.MC.E213P.e213p_r_le_m hE rfl

/-- The standing `Regime` of Section 7 built from the prepared datum (`E213A`). -/
abbrev regime (S : PreparedData d) (β₀ : ℝ) {m : ℝ} (hE : EdgeworthHyp S β₀ m) : Regime d :=
  HRS.MC.E213A.regimeOfPrepared S β₀ hE


/-! ### Generic building blocks (definitions; no `sorry`) -/

open Classical in
/-- The tensor behind `jPair`: the chosen `J` with `IsJValue … z I J`, and `0` if there is none (junk). -/
def jTensor (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) (z : ℝ → NegSobolev d m) (I : Set ℝ) :
    TensorDual (PathSpace d m T) 2 :=
  if h : ∃ J, IsJValue D ρ m T z I J then h.choose else 0

theorem jPair_eq_jTensor (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) (z : ℝ → NegSobolev d m)
    (I : Set ℝ) (M : PathSpace d m T [×2]→L[ℝ] ℝ) : jPair D ρ m T z I M = jTensor D ρ m T z I M := by
  unfold jPair jTensor
  by_cases h : ∃ J, IsJValue D ρ m T z I J <;> simp [h]

/-- The window covariance tensor `𝒥_{a,z}(I) = (R_a ⊗ R_a) 𝒥_z(I)` (TeX `U:eq:window-D` and the lines after it): the
horizon-`a+T` tensor of `path_Ito`, pushed to the window `𝒳_{m,T}` by `winRestr a`.  Its evaluations are
`2β⁻¹ ∫_{I ∩ [0,a+t_a∧t_b]} z^u(∇U^{u,a+t_a}φ_a·∇U^{u,a+t_b}φ_b) du`. -/
def winJ (R : Regime d) (m T a : ℝ) (ha : 0 ≤ a) (z : ℝ → NegSobolev d m) (I : Set ℝ) :
    TensorDual (PathSpace d m T) 2 :=
  tensorPow' 2 (winRestr a ha) (jTensor R.D R.ρ m (a + T) z I)

/-- The window drift increment `𝒟_{a,b}((u,u'])(t) = ∫_{(u,u']∩[0,a+t]} V^{a+t,v} b(v) dv` (TeX `U:eq:window-D`). -/
def winDrift (R : Regime d) (m T a : ℝ) (ha : 0 ≤ a) (b : ℝ → NegSobolev d m) (u u' : ℝ) :
    PathSpace d m T :=
  winRestr a ha (driftInc R.D R.ρ m (a + T) b u u')

/-- The predicted window `Y_a^τ = R_a 𝖳_τ w` (TeX `U:eq:predicted-window`) of a horizon-`a+T` path `w`. -/
def winPred (R : Regime d) (m T a : ℝ) (ha : 0 ≤ a) (w : PathSpace d m (a + T)) (τ : ℝ) : PathSpace d m T :=
  winRestr a ha (predicted R.D R.ρ w τ)

/-- The window heat function `U_{a,Φ}(τ,y) = E[Φ(y + R_a Γ_τ)]` (TeX `U:eq:window-heat`) for a family `γ` of
future laws on `𝒳_{m,a+T}`; `heatFn γ (Φ ∘ R_a) τ = U_{a,Φ}(τ, R_a ·)` (linearity of `R_a`). -/
def Ucal (m T a : ℝ) (ha : 0 ≤ a) (γ : ℝ → Measure (PathSpace d m (a + T))) (Φ : PathSpace d m T → ℝ)
    (τ : ℝ) (y : PathSpace d m T) : ℝ :=
  ∫ z, Φ (y + winRestr a ha z) ∂(γ τ)

/-- The coefficient `f` on `[b,∞)`, zero before `b` (the near-window part of a noise coefficient). -/
def nearCoef {E : Type*} [Zero E] (b : ℝ) (f : ℝ → E) : ℝ → E := fun u => if b ≤ u then f u else 0

/-- The coefficient `f` on `(-∞,b)`, zero from `b` on (the far-window part). -/
def farCoef {E : Type*} [Zero E] (b : ℝ) (f : ℝ → E) : ℝ → E := fun u => if u < b then f u else 0

theorem nearCoef_add_farCoef {E : Type*} [AddZeroClass E] (b : ℝ) (f : ℝ → E) :
    (fun u => nearCoef b f u + farCoef b f u) = f := by
  funext u
  by_cases h : b ≤ u
  · simp [nearCoef, farCoef, h, not_lt.mpr h]
  · simp [nearCoef, farCoef, h, not_le.mp h]

open Classical in
/-- The Riemann--Stieltjes limit on `[0,T]` of the sums `S` (`0` if the limit does not exist: junk value,
every use is accompanied by an `IsRS` statement). -/
def rsLim (T : ℝ) (S : ℝ → ℝ → ℝ → ℝ) : ℝ := if h : ∃ I, IsRS T S I then h.choose else 0

/-- The drift summand of `path_Ito`: `DU(τ, Y^τ)[𝒟((u,u'])]`. -/
def rsSumD {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (U : ℝ → X → ℝ) (Y : ℝ → X)
    (Dm : ℝ → ℝ → X) : ℝ → ℝ → ℝ → ℝ :=
  fun τ u u' => fderiv ℝ (U τ) (Y τ) (Dm u u')

/-- The covariance summand of `path_Ito`: `⟨D²U(τ, Y^τ), 𝒥((u,u'])⟩`. -/
def rsSumJ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (U : ℝ → X → ℝ) (Y : ℝ → X)
    (Jm : ℝ → ℝ → TensorDual X 2) : ℝ → ℝ → ℝ → ℝ :=
  fun τ u u' => Jm u u' (iteratedFDeriv ℝ 2 (U τ) (Y τ))

/-! ### The canonical Gaussian data -/

/-- ONE global Gaussian limit field `η` at level `r = 2d+6` (all horizons) together with its Wick-centred quadratic
field `ℬ` (`U:eq:B-limit`), on one probability space.  This is the object on which `K a` is defined, once and for
all (the quantifier order of `IsWindowEdgeworth`: `K` is chosen before `a, N, Ω, Z, Φ`).  Existence:
`exists_gaussData`; `ℬ` is unique up to null sets: `pairLim_law_eq_of_wick`.  (Field types use `S.dyn`, `S.ρ`,
`S.ρ0`, which are `rfl`-equal to `(regime S β₀ hE).D, .ρ, .ρ₀`.) -/
structure GaussData (S : PreparedData d) (β₀ : ℝ) {m : ℝ} (_hE : EdgeworthHyp S β₀ m) where
  Ω₀ : Type
  [mΩ₀ : MeasurableSpace Ω₀]
  P₀ : Measure Ω₀
  [probP₀ : IsProbabilityMeasure P₀]
  η : ℝ → Ω₀ → NegSobolev d (rLvl d)
  B : ℝ → Ω₀ → NegSobolev d (rLvl d)
  limit : IsGaussianLimitField S.dyn S.ρ (withDensityReal S.ρ0) β₀ (rLvl d) P₀ η
  B_meas : Measurable (Function.uncurry B)
  B_wick : ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
    IsWickQuadraticField S.s P₀ (fun ω => η t ω) (withDensityReal (S.ρ t)) (B t)
  B_L2 : ∀ Rw : ℝ, 0 < Rw → ∀ a : ℝ, 0 ≤ a →
    ∀ᵐ ω ∂P₀, MemLp (fun t => B (a + t) ω) 2 (volume.restrict (Set.Icc (0 : ℝ) Rw))

attribute [instance] GaussData.mΩ₀ GaussData.probP₀

/-- The window initial map `I_a : E_r →L 𝒳_{m,T}`, `(I_a z)(t) = V^{a+t,0} z` (TeX after `U:eq:predicted-window`), as a
family of continuous linear maps with `‖I_a‖ ≤ C e^{-ca}`.  (Wrapper of `initWin_decay`.) -/
theorem exists_Iwin (S : PreparedData d) (β₀ : ℝ) {m : ℝ} (hE : EdgeworthHyp S β₀ m) (T : ℝ) :
    ∃ (I : ℝ → NegSobolev d (rLvl d) →L[ℝ] PathSpace d m T) (C c : ℝ), 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a →
        (∀ z, I a z = HRS.MC.E213O.initWinFun (regime S β₀ hE).D (regime S β₀ hE).ρ m (rLvl d) T a z) ∧
        ‖I a‖ ≤ C * Real.exp (-c * a) := by
  obtain ⟨C, c, hC, hc, h⟩ := HRS.MC.E213O.initWin_decay S β₀ hE (rLvl d) m T (rLvl_le hE)
  classical
  refine ⟨fun a => if ha : 0 ≤ a then Classical.choose (h a ha) else 0, C, c, hC, hc, fun a ha => ?_⟩
  simp only [ha, dif_pos]
  exact Classical.choose_spec (h a ha)

open Classical in
/-- `I_a` (for `a < 0` the zero map). -/
def Iwin (S : PreparedData d) (β₀ : ℝ) {m : ℝ} (hE : EdgeworthHyp S β₀ m) (T : ℝ) :
    ℝ → NegSobolev d (rLvl d) →L[ℝ] PathSpace d m T :=
  Classical.choose (exists_Iwin S β₀ hE T)

/-- The vector `ℓ_x ∈ E_r` of `F:eq:ell` (`ellPt`) at the preparation `(β₀, μ°)`. -/
def ellVec (S : PreparedData d) (β₀ : ℝ) (x : Torus d) : NegSobolev d (rLvl d) :=
  ellPt (periodicRiesz d S.s) S.μ0 β₀ (rLvl d) x

theorem μ0_isProb (S : PreparedData d) : IsProbabilityMeasure S.μ0 :=
  HRS.isProb_withDensityReal S.hρ0.density

/-- The initial tensor `K_{β₀,μ°} = ∫ ℓ_x^{⊗3} dμ°(x) ∈ E_r^{⊗̂3}` (`F:eq:K0`). -/
def Kinit0 (S : PreparedData d) (β₀ : ℝ) : TensorDual (NegSobolev d (rLvl d)) 3 :=
  haveI := μ0_isProb S
  bochTensor3 S.μ0 (ellVec S β₀) (ellVec S β₀) (ellVec S β₀)

namespace GaussData

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- `Z_a = R_a Z`: the window `[a,a+T]` of the Gaussian limit as a random element of `𝒳_{m,T}`
(level `r` path pushed to level `m` by `epath`; a.s. equal to `windowPath m T a (embed ∘ η)`). -/
def Zwin (T a : ℝ) : gd.Ω₀ → PathSpace d m T :=
  fun ω => HRS.MD.EQInterp.epath (rLvl_le hE) T (procWin (rLvl d) T a gd.η ω)

/-- `D_a = 𝒟_{a,ℬ}([0,a+T])` (TeX `U:eq:totals-window`): centred second Gaussian chaos in `𝒳_{m,T}`. -/
def Dwin (T a : ℝ) : gd.Ω₀ → PathSpace d m T :=
  fun ω => if ha : 0 ≤ a then
    winDrift (regime S β₀ hE) m T a ha (fun u => NegSobolev.embed m (gd.B u ω)) 0 (a + T) else 0

/-- `J_a = 𝒥_{a,η}([0,a+T])` (TeX `U:eq:totals-window`): first Gaussian chaos in `𝒳_{m,T}^{⊗̂2}`. -/
def Jwin (T a : ℝ) : gd.Ω₀ → TensorDual (PathSpace d m T) 2 :=
  fun ω => if ha : 0 ≤ a then
    winJ (regime S β₀ hE) m T a ha (fun u => NegSobolev.embed m (gd.η u ω)) (Set.Ioc 0 (a + T)) else 0

/-- The (unsymmetrised-input, symmetrised-output) tensor of TeX `U:eq:window-tensor`:
`K_{a,T} = Sym( I_a^{⊗3}K_{β₀,μ°} - 3 E[D_a⊗Z_a⊗Z_a] + 3 E[J_a⊗Z_a] )`.  Since `I_a^{⊗3}K_{β₀,μ°}` is already
symmetric (`K_{β₀,μ°}` is an integral of cubes), this equals the TeX `I_a^{⊗3}K - 3 Sym E[D⊗Z⊗Z] + 3 Sym E[J⊗Z]`. -/
def Kwin (T a : ℝ) : TensorDual (PathSpace d m T) 3 :=
  symm3 (PathSpace d m T)
    (pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀)
      - (3 : ℝ) • bochTensor3 gd.P₀ (gd.Dwin T a) (gd.Zwin T a) (gd.Zwin T a)
      + (3 : ℝ) • bochTensor21 gd.P₀ (gd.Jwin T a) (gd.Zwin T a))

open Classical in
/-- The family `K : ℝ → projTensor 𝒳_{m,T} 3` of the theorem (`K a := Kwin (max a 0)`; junk `0` only if the membership
lemma `Kwin_mem` failed). -/
def Kproj (T : ℝ) : ℝ → projTensor (PathSpace d m T) 3 := fun a =>
  if h : gd.Kwin T (max a 0) ∈ projTensor (PathSpace d m T) 3 then ⟨gd.Kwin T (max a 0), h⟩ else 0

end GaussData

/-! ## Further definitions that do not depend on any sorried lemma -/

section Later

variable {S : PreparedData d} {β₀ m : ℝ}

open Classical in
/-- The chosen family of future laws on the horizon `H` (`0` if there is none, in particular for `H ≤ 0`: junk, never used).
Defined by `Classical.choose` on the *proposition* (not through the theorem `exists_futureGaussians`), so that this
definition does not depend on any lemma that is still `sorry`. -/
def canonFut (hE : EdgeworthHyp S β₀ m) (H : ℝ) : ℝ → Measure (PathSpace d m H) :=
  if h : ∃ γ : ℝ → Measure (PathSpace d m H), ∀ u ∈ Set.Icc (0 : ℝ) H,
      IsFutureGaussian (regime S β₀ hE).D (regime S β₀ hE).ρ m H u (γ u) ∧ IsProbabilityMeasure (γ u)
  then h.choose else fun _ => 0

/-- The window heat function of the canonical future laws (`U:eq:window-heat`). -/
def Ucan (hE : EdgeworthHyp S β₀ m) (T a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) :
    ℝ → PathSpace d m T → ℝ :=
  Ucal m T a ha (canonFut hE (a + T)) Φ

/-- `u_{Φ∘R_a}(τ, y) = U_{a,Φ}(τ, R_a y)` (linearity of `R_a`). (i) `U:eq:window-heat`; (ii) none; (iii) ~15 lines; LOW. -/
theorem heatFn_comp_winRestr (hE : EdgeworthHyp S β₀ m) (T a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (τ : ℝ) (y : PathSpace d m (a + T)) :
    heatFn (canonFut hE (a + T)) (fun w => Φ (winRestr a ha w)) τ y = Ucan hE T a ha Φ τ (winRestr a ha y) := by
  unfold heatFn Ucan Ucal
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp [map_add]

/-- The particle-system filtration/realisation datum on all horizons, `N ≥ 1` (hypothesis shape of `uniform_chaos`). -/
structure PrepFamily (S : PreparedData d) (β₀ : ℝ) {m : ℝ} (hE : EdgeworthHyp S β₀ m) where
  Ω : ℕ → Type
  [mΩ : ∀ N, MeasurableSpace (Ω N)]
  P : ∀ N, Measure (Ω N)
  [pP : ∀ N, IsProbabilityMeasure (P N)]
  X₀ : ∀ N, Ω N → Config d N
  W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)
  X : ∀ N, ℝ≥0 → Ω N → Config d N
  hreal : ∀ N, 1 ≤ N → PreparedRealization (regime S β₀ hE).D (P N)
    (modulatedGibbs (periodicRiesz d (regime S β₀ hE).D.s) N (regime S β₀ hE).β₀
      (withDensityReal (regime S β₀ hE).ρ₀)) (X₀ N) (W N) (X N)

attribute [instance] PrepFamily.mΩ PrepFamily.pP

/-- The drift summand data of `path_Ito` at window level: `A = ∫_0^{a+T} DU(τ, Y^τ) d𝒟_{ℬ}(τ)`, as the
Riemann--Stieltjes limit of `rsSumD`, for a horizon-`(a+T)` path `w` and a coefficient `bq`. -/
def rsA (R : Regime d) (m T a : ℝ) (ha : 0 ≤ a) (U : ℝ → PathSpace d m T → ℝ) (w : PathSpace d m (a + T))
    (bq : ℝ → NegSobolev d m) : ℝ :=
  rsLim (a + T) (rsSumD U (fun τ => winPred R m T a ha w τ) (fun u u' => winDrift R m T a ha bq u u'))

/-- The covariance summand data of `path_Ito`: `J = ∫_0^{a+T} ⟨D²U(τ, Y^τ), d𝒥_{η}(τ)⟩`. -/
def rsJ (R : Regime d) (m T a : ℝ) (ha : 0 ≤ a) (U : ℝ → PathSpace d m T → ℝ) (w : PathSpace d m (a + T))
    (zq : ℝ → NegSobolev d m) : ℝ :=
  rsLim (a + T) (rsSumJ U (fun τ => winPred R m T a ha w τ) (fun u u' => winJ R m T a ha zq (Set.Ioc u u')))

namespace GaussData

variable {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

open Classical in
/-- `J_a` as a projective-tensor-valued random variable (junk `0` where `Jwin` is not in `projTensor`; a.s. no junk by
`gd_moments`). -/
def JwinP (T a : ℝ) : gd.Ω₀ → projTensor (PathSpace d m T) 2 := fun ω =>
  if h : gd.Jwin T a ω ∈ projTensor (PathSpace d m T) 2 then ⟨gd.Jwin T a ω, h⟩ else 0

/-- The error of the expansion for a particle system `(P, X)`, written with the canonical Gaussian data
(`Zwin`, `Kproj`); by `Z_universal` it is the error of the theorem for every Gaussian `Z`.  The particle law is that of
`Main.windowZeta` (centred at the actual first marginal). -/
def errVal (T : ℝ) (N : ℕ) (a : ℝ) (Φ : PathSpace d m T → ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) : ℝ :=
  |Real.sqrt N * (∫ z, Φ z ∂(law P (HRS.Main.windowZeta m T a P X)) - ∫ z, Φ z ∂(law gd.P₀ (gd.Zwin T a))) -
    (1 / 6) * ∫ ω, ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
      (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) ∂gd.P₀|

end GaussData

/-- One instance of the expansion: all the data the quantifiers of `IsWindowEdgeworth.expansion` range over (with `N ≥ 2`,
`a ≥ 0`, the particle system, the Gaussian `Z`, the test function `Φ` in the unit ball). -/
structure ExpData (S : PreparedData d) (β₀ m T : ℝ) where
  a : ℝ
  ha : 0 ≤ a
  N : ℕ
  hN : 2 ≤ N
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [pP : IsProbabilityMeasure P]
  X₀ : Ω → Config d N
  W : ℝ≥0 → Ω → (Fin N → Euc d)
  X : ℝ≥0 → Ω → Config d N
  hSel : SelectedFlow P S.dyn (a + T) X₀ W X
  hfilt : ∃ (ℱ : MeasureTheory.Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
    IsFilteredSolution P ℱ W' W X
  hlaw : law P X₀ = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0
  ν : Measure (NegSobolev d m)
  hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0)
  Ω' : Type
  [mΩ' : MeasurableSpace Ω']
  P' : Measure Ω'
  [pP' : IsProbabilityMeasure P']
  Z₀ : Ω' → NegSobolev d m
  Z : ℝ → Ω' → NegSobolev d m
  hZ : IsPreparedLinear S m (a + T) ν P' Z₀ Z
  Φ : PathSpace d m T → ℝ
  hΦ : Φ ∈ CbUnitBall (PathSpace d m T) 5

attribute [instance] ExpData.mΩ ExpData.pP ExpData.mΩ' ExpData.pP'

/-- The error of the expansion of Theorem 2.13 for the instance `x` and the tensor family `K` (exactly the quantity bounded
in `IsWindowEdgeworth.expansion`; the outer `|·|` is part of the definition). -/
def ExpData.expr {T : ℝ} (x : ExpData S β₀ m T) (K : ℝ → projTensor (PathSpace d m T) 3) : ℝ :=
  |Real.sqrt x.N * (∫ z, x.Φ z ∂(law x.P (HRS.Main.windowZeta m T x.a x.P x.X)) -
      ∫ z, x.Φ z ∂(law x.P' (HRS.Main.windowPath m T x.a x.Z))) -
    (1 / 6) * ∫ ω, ((K x.a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
      (iteratedFDeriv ℝ 3 x.Φ (HRS.Main.windowPath m T x.a x.Z ω)) ∂x.P'|

end Later

end HRS.MC.E213Plan

end
