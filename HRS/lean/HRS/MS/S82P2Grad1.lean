import HRS.MS.S82P2Pair1

/-!
# S8.2 (S82P2): the configuration gradient of the pair statistic (UNCOMPILED DRAFT)
For a configuration without collisions at site `i`,
`Phase2S82.configGrad (pairStatistic Q) X i = 2 N^{-3/2} • ∑_{j ≠ i} ∇_x Q (X i) (X j)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82p2_Q_diff {d : ℕ} {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (x z : Euc d) (hxz : x ≠ z) :
    DifferentiableAt ℝ (fun y => Q y z) x := by
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have h1 : DifferentiableAt ℝ (Function.uncurry Q) (x, z) :=
    (hQ.smooth.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hxz)
  have h2 : DifferentiableAt ℝ (fun y : Euc d => (y, z)) x :=
    differentiableAt_id.prodMk (differentiableAt_const z)
  exact h1.comp x h2

lemma s82p2_phi_formula {d m : ℕ} {Q : Euc d → Euc d → ℝ} (hsym : ∀ x y, Q x y = Q y x)
    (i : Fin (m + 1)) (X : EucConfig d (m + 1)) (y : Euc d) :
    Phase2S82.pairStatistic (N := m + 1) Q (Function.update X i y) =
      Phase2S82.pairStatistic (N := m + 1) Q
          (i.insertNth (X i) (fun k => X (i.succAbove k)) : EucConfig d (m + 1)) +
        2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
          ∑ k : Fin m, (Q y (X (i.succAbove k)) - Q (X i) (X (i.succAbove k))) := by
  have hX : X = i.insertNth (X i) (fun k => X (i.succAbove k)) :=
    (Fin.insertNth_self_removeNth i X).symm
  have hu : Function.update X i y = i.insertNth y (fun k => X (i.succAbove k)) := by
    conv_lhs => rw [hX]
    exact s82p2_update_insertNth i (X i) y _
  rw [hu]
  have := s82p2_pairStat_diff hsym i (X i) y (fun k => X (i.succAbove k))
  linarith

lemma s82p2_configGrad_pair {d m : ℕ} {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q)
    (i : Fin (m + 1)) (X : EucConfig d (m + 1)) (hX : ∀ j, j ≠ i → X j ≠ X i) :
    Phase2S82.configGrad (Phase2S82.pairStatistic (N := m + 1) Q) X i =
      (2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) •
        ∑ k : Fin m, Phase2S82.pairGradX Q (X i) (X (i.succAbove k)) := by
  have hsym := hQ.symmetric
  have hk : ∀ k : Fin m, HasGradientAt (fun y => Q y (X (i.succAbove k)))
      (Phase2S82.pairGradX Q (X i) (X (i.succAbove k))) (X i) := fun k =>
    (s82p2_Q_diff hQ (X i) (X (i.succAbove k))
      (fun h => hX _ (Fin.succAbove_ne i k) h.symm)).hasGradientAt
  set c0 : ℝ := Phase2S82.pairStatistic (N := m + 1) Q
    (i.insertNth (X i) (fun k => X (i.succAbove k)) : EucConfig d (m + 1)) with hc0
  set cN : ℝ := ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) with hcN
  have hform : (fun y => Phase2S82.pairStatistic (N := m + 1) Q (Function.update X i y)) =
      fun y => c0 + 2 * cN * ∑ k : Fin m, (Q y (X (i.succAbove k)) -
        Q (X i) (X (i.succAbove k))) := by
    funext y
    exact s82p2_phi_formula hsym i X y
  have hsub : ∀ k : Fin m, HasGradientAt
      (fun y => Q y (X (i.succAbove k)) - Q (X i) (X (i.succAbove k)))
      (Phase2S82.pairGradX Q (X i) (X (i.succAbove k))) (X i) := fun k => by
    have := (hasGradientAt_iff_hasFDerivAt.1 (hk k)).sub_const (Q (X i) (X (i.succAbove k)))
    exact hasGradientAt_iff_hasFDerivAt.2 this
  have hsum : HasGradientAt (fun y => c0 + 2 * cN * ∑ k : Fin m, (Q y (X (i.succAbove k)) -
        Q (X i) (X (i.succAbove k))))
      ((2 * cN) • ∑ k : Fin m, Phase2S82.pairGradX Q (X i) (X (i.succAbove k))) (X i) := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have h1 : HasFDerivAt (fun y => ∑ k : Fin m, (Q y (X (i.succAbove k)) -
        Q (X i) (X (i.succAbove k))))
        (∑ k : Fin m, (InnerProductSpace.toDual ℝ (Euc d)) (Phase2S82.pairGradX Q (X i) (X (i.succAbove k)))) (X i) :=
      HasFDerivAt.fun_sum fun k _ => hasGradientAt_iff_hasFDerivAt.1 (hsub k)
    have h2 := (h1.const_mul (2 * cN)).const_add c0
    rw [map_smul, map_sum]
    convert h2 using 1
  show gradient (fun y => Phase2S82.pairStatistic (N := m + 1) Q (Function.update X i y)) (X i) = _
  rw [hform]
  exact hsum.gradient

end HRS.MS.S82P2
