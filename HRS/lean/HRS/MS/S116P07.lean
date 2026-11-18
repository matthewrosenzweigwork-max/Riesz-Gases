import HRS.MS.S116P06
import HRS.MS.R2IidPathTie

/-!
# S11.6 packet P07 (`R26-T8B.P07`): the initial-path Edgeworth clause for the iid preparation

Prefix `s116_`, namespace `HRS.MS.S116`.  The native iid path theorem `s11p_path_iid` (R2IidPathTie) with its continuity premise supplied by `s116_all_order_continuity` (P06); the
three original hypotheses (adjoint existence, cosine-orbit `C_b^k` membership and summability) are kept.
-/

set_option autoImplicit false

noncomputable section

namespace HRS.MS.S116

open HRS HRS.Whole

theorem s116_iid_path {d : ℕ} (hd : 2 ≤ d) (a β T : ℝ) (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T)
    (εstar c₁ C₁ : ℝ) (ρβ : Euc d → ℝ) (hρβ : IsThermalEquilibrium d 0 a β ρβ)
    (hR : HRS.MS.R2WinErr.S104bTermRegGen d 0 a β ρβ εstar c₁ C₁)
    (ρ : ℝ → Euc d → ℝ) (htraj : IsR2WindowTrajectory d 0 a β ρβ εstar c₁ C₁ ρ)
    (hprob : HRS.Whole.IsProbDensity (ρ 0))
    (k m : ℕ) (hk : 4 * d + 40 ≤ k) (hm : (k : ℝ) + 2 * d + 4 < m)
    (hex : ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW ((quadraticGradientDyn d 0 a β).coeff ρ) t (oscTestFun (m : ℝ) α) f)
    (hmem : ∀ n α, MemCb k (r2CosOrbitTest ((quadraticGradientDyn d 0 a β).coeff ρ) (m : ℝ) T n α))
    (hsum : Summable fun p : ℕ × MultiIndex d =>
      cbNorm k (r2CosOrbitTest ((quadraticGradientDyn d 0 a β).coeff ρ) (m : ℝ) T p.1 p.2)) :
    R2InitPathEdgeworth ((quadraticGradientDyn d 0 a β).coeff ρ) 0 0 m T (ρ 0) :=
  HRS.Whole.s11p_path_iid hd a β ha hβ T hT k m hk hm ρ hprob hex hmem hsum
    (s116_all_order_continuity hd ha hβ hρβ hR ρ htraj T hT m hex)

end HRS.MS.S116

end
