import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovOscAux5

/-!
# S6.7 nonlinear breakdown, packet 33: strong measurability of higher oscillator representatives

`s67bd_higher_measurable`: a path continuous in `L²_0` with `Σ^p`-valued values everywhere has
`v ↦ OscSpace.ofFun p (movFun (h v))` a.e. strongly measurable.  Route: finite Hermite truncations
have continuous (hence measurable) coordinates, and converge in `ℓ²` pointwise in `v` (the
`hasSum_single` expansion of the actual higher representative), so strong measurability passes to the
pointwise limit.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- Each Hermite coefficient of an `L²` path is continuous in the `L²` topology. -/
theorem s67bd_coeff_continuousOn (ρ₀ : Euc d → ℝ) (h : ℝ → MovL2Zero ρ₀) (S : Set ℝ)
    (hc : ContinuousOn h S) (α : MultiIndex d) :
    ContinuousOn (fun v => hermiteCoeff (movFun (h v)) α) S := by
  have hcont : ContinuousOn (fun v => inner ℝ (hermiteLpD α)
      ((h v : MovL2Zero ρ₀) : Lp ℝ 2 (volume : Measure (Euc d)))) S :=
    (innerSL ℝ (hermiteLpD α)).continuous.comp_continuousOn
      (continuous_subtype_val.comp_continuousOn hc)
  refine hcont.congr fun v _ => ?_
  have hmem : MemLp (movFun (h v)) 2 (volume : Measure (Euc d)) :=
    Lp.memLp ((h v : MovL2Zero ρ₀) : Lp ℝ 2 (volume : Measure (Euc d)))
  have := OscSpace.inner_hermiteLpD_toLp (movFun (h v)) hmem α
  have h2 : hmem.toLp (movFun (h v)) = ((h v : MovL2Zero ρ₀) : Lp ℝ 2 (volume : Measure (Euc d))) :=
    Lp.toLp_coeFn _ hmem
  rw [← this, h2]

theorem s67bd_higher_measurable (ρ₀ : Euc d → ℝ) (p T : ℝ)
    (hp : 0 ≤ p) (hT : 0 ≤ T) (h : ℝ → MovL2Zero ρ₀)
    (hc : ContinuousOn h (Icc (0 : ℝ) T))
    (hm : ∀ v ∈ Icc (0 : ℝ) T, MemOsc p (movFun (h v))) :
    AEStronglyMeasurable (fun v => OscSpace.ofFun p (movFun (h v)))
      (volume.restrict (Icc (0 : ℝ) T)) := by
  classical
  set e : MultiIndex d → lp (fun _ : MultiIndex d => ℝ) 2 := fun α => lp.single 2 α (1 : ℝ)
    with he
  set F : ℕ → ℝ → lp (fun _ : MultiIndex d => ℝ) 2 := fun n v =>
    ∑ α ∈ mova2_S d n, (oscEigenvalue d α ^ (p / 2) * hermiteCoeff (movFun (h v)) α) • e α
    with hF
  have hFm : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (Icc (0 : ℝ) T)) := by
    intro n
    refine Finset.aestronglyMeasurable_fun_sum _ fun α _ => ?_
    exact ((continuousOn_const.mul (s67bd_coeff_continuousOn ρ₀ h _ hc α)).aestronglyMeasurable
      measurableSet_Icc).smul_const (e α)
  have hlim : ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) T)),
      Tendsto (fun n => F n v) atTop (𝓝 (OscSpace.ofFun p (movFun (h v)) :
        lp (fun _ : MultiIndex d => ℝ) 2)) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun v hv => ?_)
    have hmv := hm v hv
    set f : lp (fun _ : MultiIndex d => ℝ) 2 := (OscSpace.ofFun p (movFun (h v)) :
      lp (fun _ : MultiIndex d => ℝ) 2) with hf
    have hsum := lp.hasSum_single (E := fun _ : MultiIndex d => ℝ) (p := 2) ENNReal.ofNat_ne_top f
    have hT' := hsum.comp (tendsto_atTop_finset_of_monotone (mova2_S_mono (d := d)) mova2_S_exh)
    refine hT'.congr fun n => ?_
    simp only [Function.comp_apply, hF]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hfα : f α = oscEigenvalue d α ^ (p / 2) * hermiteCoeff (movFun (h v)) α :=
      OscSpace.coord_ofFun_eq hmv α
    rw [hfα, he]
    simp only
    rw [← lp.single_smul (𝕜 := ℝ), smul_eq_mul, mul_one]
  exact aestronglyMeasurable_of_tendsto_ae atTop hFm hlim

end HRS.MS.BreakdownS67
