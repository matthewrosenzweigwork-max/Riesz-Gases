import HRS.MS.R2GenInitAux18
import HRS.MS.GenPathAux18

/-!
# S10.5 window comparison, packet B5: measurability in `r` of the pairings of the window feature

`s105_win_eq`: `r2WindowFeature = KSpace.mk (ellVec A₀) (toLp f) (ellVec B)` once the pieces are in `ℓ²`/`L²` (`s105_winK`).
`s105_win_inner`: the pairing with `e ∈ 𝒦_T` is `⟨e.A₀,A₀⟩ + ∫_0^T⟨e.A'(u),f(u)⟩du + ⟨e.B,B⟩`.
`s105_win_inner_meas`: `r ↦ ⟨e, Γ_{b,clamp r,a}(x)⟩` is measurable: `A₀` and the middle term are continuous on `[0,b+T]`
(dominated convergence), the third slot is `1_{b≤r}⟨e.B,∂_aφ⟩`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.MP.RdRem HRS.MS.Go HRS.MS.R2WinErr HRS.MS.GenPath

variable {d : ℕ}

theorem s105_win_eq (C : WholeCoeff d) (m T b r : ℝ) (a : Fin d) (x : Euc d)
    (hA : Memℓp (fun α => gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x) 2)
    (hmem : MemLp (fun u : ℝ => if r < b + u then ellVec (d := d) m (fun α => gradComp a (propagatorW C r (b + u)
      (generatorW C (b + u) (oscTestFun m α))) x) else 0) 2 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    r2WindowFeature C m T (gradComp a) b r x =
      KSpace.mk (ellVec (d := d) m (fun α => gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x))
        (hmem.toLp _) (ellVec (d := d) m (fun α => if b ≤ r then gradComp a (oscTestFun m α) x else 0)) := by
  classical
  unfold r2WindowFeature
  dsimp only
  congr 1
  · exact dif_pos hmem
  · split_ifs with h
    · rfl
    · exact (s55f_ellVec_zero m).symm

theorem s105_win_inner {m T : ℝ} (e : KSpace d m T) (A0 B0 : OscDual d m) (f : ℝ → OscDual d m)
    (hmem : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    inner ℝ e (KSpace.mk A0 (hmem.toLp f) B0) = inner ℝ e.A₀ A0 +
      (∫ u in Set.Icc (0 : ℝ) T, inner ℝ ((e.A' : L2Path d m T) u) (f u)) + inner ℝ e.B B0 := by
  rw [HRS.MS.S52.s52_inner_mk, MeasureTheory.L2.inner_def]
  have hae : ∀ᵐ u ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      inner ℝ ((e.A' : L2Path d m T) u) ((hmem.toLp f : L2Path d m T) u) =
        inner ℝ ((e.A' : L2Path d m T) u) (f u) := by
    filter_upwards [hmem.coeFn_toLp] with u hu
    rw [hu]
  rw [integral_congr_ae hae]

end HRS.MS.R2GenInit
