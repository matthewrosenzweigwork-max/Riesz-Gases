import HRS.MS.WsInitGAux13
import HRS.MS.WsStatAux34

/-!
# S21 packet G, part 14: the smooth half of `S21Init` in the shape of `S21InitAt`

`S21InitSmoothAt`: the first three conjuncts of `S21InitAt` (WsStatAux34), i.e. `S21InitAt` without the `W_1` clause (packet H).
`s21g_init_smooth_at`: `S21InitSmoothAt d s a β T (wholeSpaceIndex d) _` for `d ≥ 2`, `0 ≤ s < d`, `a, β, T > 0`.
`s21g_gauss_coord_sq`: second moments of the coordinates of the Gaussian `γ` (input of the `W_1` projection tails of packet H).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem
open HRS (Euc cbNorm MemCb smoothDist)

variable {d : ℕ}

/-- `S21InitAt` without the `W_1` conjunct. -/
def S21InitSmoothAt (d : ℕ) (s a β T m : ℝ) (hT : 0 ≤ T) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ → ∀ N : ℕ, 2 ≤ N →
    ∃ γ0 : Measure (OscPath d m T), IsProbabilityMeasure γ0 ∧
      (∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
        (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts i)
            (oscTestFun m (αs i)))
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts j)
            (oscTestFun m (αs j)))).PosSemidef ∧
        γ0.map (fun w : OscPath d m T => (WithLp.toLp 2 fun i =>
            OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p))) =
          multivariateGaussian 0 (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s)
            (HRS.Whole.withDensityReal ρ) β
            (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts i)
              (oscTestFun m (αs i)))
            (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts j)
              (oscTestFun m (αs j))))) ∧
      smoothDist 2 ((HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β).map
          (s21IP m T hT ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) N
            (HRS.Whole.meanEmpirical (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β)))) γ0 ≤
        C * Real.sqrt (HRS.deltaN d s N)

/-- **The smooth half of `S21Init`** (packet G). -/
theorem s21g_init_smooth_at (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {T : ℝ} (hT : 0 < T) :
    S21InitSmoothAt d s a β T ((wholeSpaceIndex d : ℕ) : ℝ) hT.le :=
  s21g_init_smooth hd hs0 hsd ha hβ hT

theorem s21g_gauss_coord_sq {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {g : Euc d → ℝ}
    {K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν} (hK : S45.IsKData ν g K) {β : ℝ} (hβ : 0 < β) {J : ℕ} {φ : ℕ → Euc d → ℝ}
    (hφ : IsSummableFeatureFamily J φ) {γ : Measure SeqL2}
    (hγ : IsCenteredGaussianSeq γ (fun i j => HRS.Whole.susceptibilityCov g ν β (φ i) (φ j))) (j : ℕ) :
    ∫ z, SeqL2.coord z j * SeqL2.coord z j ∂γ ≤ 4 * cbNorm J (φ j) ^ 2 := by
  have hφm : ∀ i, MemLp (φ i) 2 ν := fun i => HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 i)
  rw [(hγ.2 j j).2]
  show HRS.Whole.susceptibilityCov g ν β (φ j) (φ j) ≤ _
  rw [S45.s45_susceptibilityCov_eq hK hβ (hφm j) (hφm j)]
  have h1 := S45.s45_inner_Rr_le hK hβ.le (S45.s45_U (φ j) (hφm j))
  have h2 := S45.s45_U_norm_le (hφm j) fun x => HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 j) x
  have h3 : ‖S45.s45_U (φ j) (hφm j)‖ ^ 2 ≤ (2 * cbNorm J (φ j)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  nlinarith

end HRS.MS.S21
