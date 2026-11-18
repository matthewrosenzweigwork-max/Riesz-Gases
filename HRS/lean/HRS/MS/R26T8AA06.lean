import HRS.MS.R26T8AA06a
import HRS.MS.R26T8AA06b
import HRS.MS.R26T8AA04b

/-!
# S8.2 observed-time layer, packet T8A.A06: the lifted pair generator

Packet statement `r26t8a_lifted_pair_generator`: for a collision-free configuration
`L_N Φ_Q(X) = -Φ_{HSource}(X) + errorStatistic(Q)(X)`.  Route: `A04` (gradient and Laplacian of the pair statistic), the drift
decomposition `b_i = b₀(X_i) + e_i` (`A06b`), the local pair identity `(…) = -HSource - pairJ` (`A06a`, from `A03` and the
Poisson equation), the splitting of `e` into the repeated-label and distinct-triple terms (`A06b`), and `A05`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_a06_swap {N : ℕ} (F : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, F i j = ∑ i, ∑ j ∈ Finset.univ.erase i, F j i := by
  refine Finset.sum_comm' (s := (Finset.univ : Finset (Fin N))) (t := fun i => Finset.univ.erase i)
    (t' := (Finset.univ : Finset (Fin N))) (s' := fun j => Finset.univ.erase j)
    (f := fun i j => F i j) ?_
  intro x y
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

theorem r26t8a_a06_gY {d : ℕ} (Q : Euc d → Euc d → ℝ) (hsym : ∀ x y, Q x y = Q y x) (x y : Euc d) :
    HRS.MS.Phase2S82.pairGradY Q x y = HRS.MS.Phase2S82.pairGradX Q y x := by
  unfold HRS.MS.Phase2S82.pairGradY HRS.MS.Phase2S82.pairGradX
  have : Q x = fun z => Q z x := funext fun z => hsym x z
  rw [this]

theorem r26t8a_lifted_pair_generator (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (a beta M A : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (HRS.MS.Phase2S82.criticalS d) a beta rho)
    (f : Euc d → ℝ) (Q : Euc d → Euc d → ℝ)
    (hQ : HRS.MS.Phase2S82.PairCorrector a beta rho M A f Q) :
    ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      HRS.MS.Phase2S82.particleGenerator
          (quadraticGradientDyn d (HRS.MS.Phase2S82.criticalS d) a beta)
          (HRS.MS.Phase2S82.pairStatistic Q) X =
        -HRS.MS.Phase2S82.pairStatistic
            (HRS.MS.Phase2S82.HSource (HRS.Whole.withDensityReal rho) f) X +
          HRS.MS.Phase2S82.errorStatistic (critCoeff d a beta rho) rho Q X := by
  intro X hX
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by positivity
  have hNr : (N : ℝ) ≠ 0 := hNpos.ne'
  have hsym := hQ.symmetric
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.smooth.of_le (by norm_num)
  obtain ⟨hgrad, hlap⟩ := r26t8a_pair_generator_differentiation Q hQ2 hsym X hX
  have hne : ∀ i j : Fin N, j ≠ i → X i ≠ X j := fun i j hji hEq => hX ⟨j, i, hji, hEq.symm⟩
  set cN : ℝ := (N : ℝ) ^ (-(3 / 2 : ℝ)) with hcN
  have h52 : (N : ℝ) ^ (-(5 / 2 : ℝ)) = cN * (1 / (N : ℝ)) := by
    rw [hcN, one_div, ← Real.rpow_neg_one, ← Real.rpow_add hNpos]; norm_num
  -- notation for the per-pair quantities
  set b0 : Fin N → Euc d := fun i => (critCoeff d a beta rho).drift 0 (X i) with hb0
  set gX : Fin N → Fin N → Euc d := fun i j => HRS.MS.Phase2S82.pairGradX Q (X i) (X j) with hgX
  set gY : Fin N → Fin N → Euc d := fun i j => HRS.MS.Phase2S82.pairGradY Q (X i) (X j) with hgY
  have hgYX : ∀ i j, gY i j = gX j i := fun i j => r26t8a_a06_gY Q hsym (X i) (X j)
  have hbX : ∀ i, particleDriftW (quadraticGradientDyn d (HRS.MS.Phase2S82.criticalS d) a beta) X i =
      b0 i + r26t8a_a06b_e rho X i := fun i => r26t8a_a06b_drift hN1 a beta rho X i
  unfold HRS.MS.Phase2S82.particleGenerator
  rw [hlap]
  simp only [hgrad, hbX]
  -- the drift pairing
  have hdrift : ∑ i, inner ℝ (b0 i + r26t8a_a06b_e rho X i)
      ((2 * cN) • ∑ j ∈ Finset.univ.erase i, HRS.MS.Phase2S82.pairGradX Q (X i) (X j)) =
      cN * ∑ i, ∑ j ∈ Finset.univ.erase i,
        (inner ℝ (b0 i + r26t8a_a06b_e rho X i) (gX i j) +
          inner ℝ (b0 j + r26t8a_a06b_e rho X j) (gY i j)) := by
    have e1 : ∑ i, inner ℝ (b0 i + r26t8a_a06b_e rho X i)
        ((2 * cN) • ∑ j ∈ Finset.univ.erase i, HRS.MS.Phase2S82.pairGradX Q (X i) (X j)) =
        2 * cN * ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (b0 i + r26t8a_a06b_e rho X i) (gX i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_right, inner_sum, Finset.mul_sum]
    have e2 := r26t8a_a06_swap (fun i j => inner ℝ (b0 i + r26t8a_a06b_e rho X i) (gX i j))
    have e3 : ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (b0 j + r26t8a_a06b_e rho X j) (gX j i) =
        ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (b0 j + r26t8a_a06b_e rho X j) (gY i j) := by
      simp only [hgYX]
    simp only [Finset.sum_add_distrib]
    rw [e1, ← e3, ← e2]
    ring
  rw [hdrift]
  -- the per-pair identity
  have hpair : ∀ i, ∀ j ∈ Finset.univ.erase i,
      (beta⁻¹ * (Laplacian.laplacian (fun x => Q x (X j)) (X i) +
          Laplacian.laplacian (Q (X i)) (X j)) +
        (inner ℝ (b0 i + r26t8a_a06b_e rho X i) (gX i j) +
          inner ℝ (b0 j + r26t8a_a06b_e rho X j) (gY i j))) =
      (-HRS.MS.Phase2S82.HSource (HRS.Whole.withDensityReal rho) f (X i) (X j) -
          HRS.MS.Phase2S82.pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q (X i) (X j)) +
        ((1 / (N : ℝ)) * (-HRS.MS.Phase2S82.repeatedB rho Q (X i) (X j)) +
          (1 / (N : ℝ)) * ∑ k ∈ (Finset.univ.erase i).erase j,
            HRS.MS.Phase2S82.tripleT rho Q (X i) (X j) (X k)) := by
    intro i j hj
    have hji : j ≠ i := (Finset.mem_erase.1 hj).1
    have h1 := r26t8a_a06a_pair_local d hd a beta M A ha hbeta rho hrho f Q hQ (X i) (X j) (hne i j hji)
    have h2 := r26t8a_a06b_pair_e rho Q hsym X i j hj
    simp only [inner_add_left]
    rw [← h2]
    simp only [hb0, hgX, hgY] at *
    linarith
  have hD : (quadraticGradientDyn d (HRS.MS.Phase2S82.criticalS d) a beta).invβ = beta⁻¹ := rfl
  rw [hD]
  have hS : ∑ i, ∑ j ∈ Finset.univ.erase i,
      (beta⁻¹ * (Laplacian.laplacian (fun x => Q x (X j)) (X i) +
          Laplacian.laplacian (Q (X i)) (X j)) +
        (inner ℝ (b0 i + r26t8a_a06b_e rho X i) (gX i j) +
          inner ℝ (b0 j + r26t8a_a06b_e rho X j) (gY i j))) =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
      ((-HRS.MS.Phase2S82.HSource (HRS.Whole.withDensityReal rho) f (X i) (X j) -
          HRS.MS.Phase2S82.pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q (X i) (X j)) +
        ((1 / (N : ℝ)) * (-HRS.MS.Phase2S82.repeatedB rho Q (X i) (X j)) +
          (1 / (N : ℝ)) * ∑ k ∈ (Finset.univ.erase i).erase j,
            HRS.MS.Phase2S82.tripleT rho Q (X i) (X j) (X k))) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl (hpair i)
  have hcomb : beta⁻¹ * (cN * ∑ i, ∑ j ∈ Finset.univ.erase i,
        (Laplacian.laplacian (fun x => Q x (X j)) (X i) + Laplacian.laplacian (Q (X i)) (X j))) +
      cN * ∑ i, ∑ j ∈ Finset.univ.erase i,
        (inner ℝ (b0 i + r26t8a_a06b_e rho X i) (gX i j) +
          inner ℝ (b0 j + r26t8a_a06b_e rho X j) (gY i j)) =
      cN * ∑ i, ∑ j ∈ Finset.univ.erase i,
        (beta⁻¹ * (Laplacian.laplacian (fun x => Q x (X j)) (X i) +
            Laplacian.laplacian (Q (X i)) (X j)) +
          (inner ℝ (b0 i + r26t8a_a06b_e rho X i) (gX i j) +
            inner ℝ (b0 j + r26t8a_a06b_e rho X j) (gY i j))) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hcomb, hS]
  have hJs : ∀ x y, HRS.MS.Phase2S82.pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x y =
      HRS.MS.Phase2S82.pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q y x := by
    intro x y
    unfold HRS.MS.Phase2S82.pairJ
    have hx : Q x = fun z => Q z x := funext fun z => hsym x z
    have hy : Q y = fun z => Q z y := funext fun z => hsym y z
    rw [hx, hy]
    ring
  have htc := r26t8a_triple_count (d := d) (N := N) hN (critCoeff d a beta rho) rho Q X hsym hJs
  simp only [HRS.MS.Phase2S82.tripleSum, HRS.MS.Phase2S82.pairSum] at htc
  simp only [HRS.MS.Phase2S82.errorStatistic, HRS.MS.Phase2S82.pairStatistic,
    HRS.MS.Phase2S82.tripleSum, HRS.MS.Phase2S82.pairSum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [htc, h52]
  field_simp
  ring

end HRS.MS.R26T8A

end
