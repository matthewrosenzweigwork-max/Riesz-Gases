import HRS.MS.SA16Y3Mem2
import HRS.MS.SA16RHeat13

/-!
# S.A.16 (SA16Y3) Ext1: the bounded operator `P_μ : W^{m+2,p} → W^{m,p}` (packet P7 iso, step (a))

`sa16y3_L`: the linear map `φ ↦ P_μ φ`, `C_c^∞ → sa16r_S d m p`.
`sa16y3_extend`: it extends (`sa16r_extend_cc`) to a bounded linear `T : W^{m+2,p} → W^{m,p}`, `‖T‖ ≤ K Λ`, whose value on the
jet class of `φ ∈ C_c^∞` is the jet class of `P_μ φ` (a.e. equality of the jets with `wJet m (P_μ φ)`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Ext1
variable {d : ℕ} {s p : ℝ} [Fact (2 ≤ p)]

/-- `φ ↦ P_μ φ` as a linear map `C_c^∞ → sa16r_S d m p` -/
def sa16y3_L (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ)
    {μ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (hCb : sa16z_Cb (m + 2) Λ μ) :
    ccSub d →ₗ[ℝ] sa16r_S d m p where
  toFun φ := ⟨sa16z_P s μ φ.1, sa16y3_P_memS hd hs0 hsd hθ1 m hμ φ.2 hΛ hCb⟩
  map_add' φ ψ := Subtype.ext (sa16y3_P_add hs0 hsd hμ φ.2 ψ.2)
  map_smul' c φ := Subtype.ext (sa16y3_P_smul hs0 hsd hμ φ.2 c)

theorem sa16y3_extend (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {μ : Euc d → ℝ}, ContDiff ℝ ∞ μ → ∀ {Λ : ℝ}, 0 ≤ Λ → sa16z_Cb (m + 2) Λ μ →
      ∃ T : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p, ‖T‖ ≤ K * Λ ∧
        ∀ φ : ccSub d, wrep d m p (T (sa16r_Jcc d (m + 1 + 1) p φ)) =ᵐ[volume] sa16z_P s μ φ.1 ∧
          (((T (sa16r_Jcc d (m + 1 + 1) p φ) : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ))
            =ᵐ[volume] wJet m (sa16z_P s μ φ.1) := by
  obtain ⟨K, hK0, hK⟩ := sa16y3_P_Jbound (s := s) (p := p) hd hs0 hsd hθ1 m
  refine ⟨K, hK0, fun {μ} hμ {Λ} hΛ hCb => ?_⟩
  obtain ⟨T, hT, hTJ, -⟩ := sa16r_extend_cc d (m + 1 + 1) m p (sa16y3_L hd hs0 hsd hθ1 m hμ hΛ hCb)
    (mul_nonneg hK0 hΛ) (fun φ => hK hμ hΛ hCb φ _ rfl)
  refine ⟨T, hT, fun φ => ?_⟩
  have hS : MemLp (sa16j_S d m (sa16z_P s μ φ.1)) (ENNReal.ofReal p) volume :=
    sa16y3_S_memLp hd hs0 hsd hθ1 m hμ φ.2 hΛ hCb
  rw [hTJ φ]
  exact ⟨sa16r_J_spec d m p _, sa16r_J_coe m (f := sa16y3_L hd hs0 hsd hθ1 m hμ hΛ hCb φ) hS⟩

end Ext1

end HRS.Whole.AppendixA.Phase2SA16R
