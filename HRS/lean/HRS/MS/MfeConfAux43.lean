import HRS.MS.MfeConfAux42

/-!
# S.B.1, packet F6 (part 5): the time-integrated cut-off inequality with a tilted reference

`sb1_hasDerivAt_Phi`: `∂_s Φ_s = a Λ + u ∂_sΨ/θ` for `Φ_s = u log u + u (H + Ψ_s)/θ`;
`sb1_time_ineq`: the integral over `[0,t]` of the fixed-time inequality (the transplant of
`P4MolData.time_ineq`, with the source `u S` in place of the sign-condition on `∂_sV`).
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {θ T : ℝ} {b : ℝ → EucConfig d N → EucConfig d N} {H : EucConfig d N → ℝ}
  {Ψ : ℝ → EucConfig d N → ℝ} {w : ℝ → EucConfig d N → EucConfig d N} {Wψ : ℝ → EucConfig d N → ℝ}
  {μ : ℝ → Measure (EucConfig d N)} {Kl : ℝ≥0} {B K M CV : ℝ} {v : ℝ}

theorem sb1_hasDerivAt_Phi (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV) (hv : 0 < v)
    (hWd : ∀ r ∈ Set.Ioo (0 : ℝ) T, ∀ x, HasDerivAt (fun s => Ψ s x) (Wψ r x) r)
    (x : EucConfig d N) {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => p4m_Phi v θ μ (fun s y => H y + Ψ s y) s x)
      (p4m_a v θ (μ r) (b r) x * p4m_Lam v θ (μ r) (fun y => H y + Ψ r y) x +
        p4Mol v (μ r) x * Wψ r x / θ) r := by
  have hu := hP.hasDerivAt_u hv x hr
  have hpos := (hP.pos_u hv r x).ne'
  have hl := hu.log hpos
  have hVd : HasDerivAt (fun s => H x + Ψ s x) (Wψ r x) r := (hWd r hr x).const_add (H x)
  have h3 := (hu.mul hl).add ((hu.mul hVd).div_const θ)
  unfold p4m_Phi p4m_Lam
  convert h3 using 1
  field_simp
  ring

end

end HRS.MS.MfeConf
