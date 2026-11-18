import HRS.MS.SA16Y9En3

/-!
# S.A.16 (SA16Y9) Lw1: compatibility of `Δ` and `B_bc` with the level-lowering maps (stability, G1a)

`sa16y9_Lap_low`: `ι²_m ∘ Δ_{m+2} = Δ_m ∘ ι²_{m+2}`; `sa16y9_B_low`: `ι²_m ∘ ι_{m+2} ∘ B_{m+3}(bc) = ι_m ∘ B_{m+1}(bc) ∘ ι²_{m+2}`
(both from `W^{m+4,p}`), by density of the `C_c^∞` jets.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Lw1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y9_wrep_iota2 (m : ℕ) (G : WmpSpace d (m + 1 + 1) p) :
    wrep d m p (sa16sz_iota2 d m p G) =ᵐ[volume] wrep d (m + 1 + 1) p G := by
  unfold sa16sz_iota2
  simp only [ContinuousLinearMap.comp_apply]
  filter_upwards [sa16r_iota_wrep (p := p) m (sa16r_iota d (m + 1) p G),
    sa16r_iota_wrep (p := p) (m + 1) G] with x h1 h2
  rw [h1, h2]

theorem sa16y9_Lap_low (m : ℕ) :
    (sa16sz_iota2 d m p).comp (sa16so_Lap d (m + 2) p) =
      (sa16so_Lap d m p).comp (sa16sz_iota2 d (m + 2) p) := by
  refine sa16so_clm_ext fun φ => sa16r_wrep_inj d m p _ _ ?_
  simp only [ContinuousLinearMap.comp_apply]
  rw [sa16sz_iota2_Jcc]
  filter_upwards [sa16y9_wrep_iota2 (p := p) m (sa16so_Lap d (m + 2) p (sa16r_Jcc d (m + 2 + 2) p φ)),
    sa16so_Lap_Jcc (p := p) (m + 2) φ, sa16so_Lap_Jcc (p := p) m φ] with x h1 h2 h3
  rw [h1, h2, h3]

theorem sa16y9_B_low (m : ℕ) {B : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16BddCoef (m + 3) B bc) :
    (sa16sz_iota2 d m p).comp ((sa16r_iota d (m + 2) p).comp (sa16so_B d (m + 3) p bc)) =
      (sa16r_iota d m p).comp ((sa16so_B d (m + 1) p bc).comp (sa16sz_iota2 d (m + 2) p)) := by
  have hb1 : SA16BddCoef (m + 1) B bc :=
    ⟨hb.nonneg, hb.smooth, fun i j hj x => hb.bound i j (by omega) x⟩
  refine sa16so_clm_ext fun φ => sa16r_wrep_inj d m p _ _ ?_
  simp only [ContinuousLinearMap.comp_apply]
  rw [sa16sz_iota2_Jcc]
  filter_upwards [sa16y9_wrep_iota2 (p := p) m (sa16r_iota d (m + 2) p (sa16so_B d (m + 3) p bc
      (sa16r_Jcc d (m + 2 + 2) p φ))),
    sa16r_iota_wrep (p := p) (m + 2) (sa16so_B d (m + 3) p bc (sa16r_Jcc d (m + 2 + 2) p φ)),
    sa16so_B_Jcc (p := p) hb φ, sa16r_iota_wrep (p := p) m (sa16so_B d (m + 1) p bc (sa16r_Jcc d (m + 2) p φ)),
    sa16so_B_Jcc (p := p) hb1 φ] with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5]

end Lw1

end HRS.Whole.AppendixA.Phase2SA16R
