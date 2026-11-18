import HRS.MS.GenPathAux18
import HRS.MP.RdRemainder

/-!
# S5.6 packet P5a (part 3): joint measurability of `(r,x) ↦ Γ_{r,a}(x) ∈ 𝒦`

With the time clamp `mrrClamp T r = max 0 (min r T)`: for fixed `x` the map `r ↦ Γ_{clamp r,a}(x)` is weakly continuous
(`s56_feat_inner_cont`), hence measurable in the separable Hilbert space `𝒦` (`measurable_of_inner_basis`); for fixed `r` the
map is continuous in `x` (`general_orbits_features_proof`).  Carathéodory (`measurable_uncurry_of_continuous_of_measurable`)
gives joint measurability.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_feat_meas_r (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) (a : Fin d) (x : Euc d) :
    Measurable fun r : ℝ => gradFeature (S.coeff N) b.m b.T a (mrrClamp b.T r) x := by
  obtain ⟨ι, hι, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := KSpace d b.m b.T)
  haveI := hι
  refine measurable_of_inner_basis e fun i => ?_
  exact ((s56_feat_inner_cont b hbv S N hC a x (e i)).comp_continuous (continuous_mrrClamp b.T)
    (fun r => mrrClamp_mem hbv.hT.le r)).measurable

theorem s56_carath (f : Euc d → ℝ → ℝ) (hc : ∀ r, Continuous fun x => f x r) (hm : ∀ x, Measurable (f x)) :
    Measurable (fun p : ℝ × Euc d => f p.2 p.1) := by
  have h := measurable_uncurry_of_continuous_of_measurable (ι := Euc d) (α := ℝ) (β := ℝ) (u := f) hc hm
  exact h.comp measurable_swap

theorem s56_feat_meas (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) (a : Fin d) :
    Measurable fun p : ℝ × Euc d => gradFeature (S.coeff N) b.m b.T a (mrrClamp b.T p.1) p.2 := by
  obtain ⟨C, hCf⟩ := HRS.MS.Star.general_orbits_features_proof b hbv
  obtain ⟨ι, hι, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := KSpace d b.m b.T)
  haveI := hι
  refine measurable_of_inner_basis e fun i => ?_
  have hcont : ∀ r : ℝ, Continuous fun x : Euc d =>
      inner ℝ (e i) (gradFeature (S.coeff N) b.m b.T a (mrrClamp b.T r) x) := fun r =>
    continuous_const.inner (hCf S N a _ (mrrClamp_mem hbv.hT.le r)).1.continuous
  exact s56_carath (fun (x : Euc d) (r : ℝ) =>
    inner ℝ (e i) (gradFeature (S.coeff N) b.m b.T a (mrrClamp b.T r) x)) hcont (fun x =>
      ((s56_feat_inner_cont b hbv S N hC a x (e i)).comp_continuous (continuous_mrrClamp b.T)
        (fun r => mrrClamp_mem hbv.hT.le r)).measurable)

end HRS.MS.GenPath
