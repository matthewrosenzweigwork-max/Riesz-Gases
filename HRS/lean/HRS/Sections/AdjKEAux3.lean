import HRS.Sections.AdjKEAux2
import HRS.Energy.PressureAlg
import HRS.Duality.PairingExpansion
import HRS.Energy.PressureProof

/-!
# ADJKE part 3: the modulated energy of the commutator kernel is a bounded linear functional of the Lipschitz constant

For a continuous `L`-Lipschitz vector field `w`, a probability density `ρ ≤ Λ` and a configuration `X`:
`|F_N^{h_w}(X, ρ)| ≤ L · A (pairSum(X) + (3/2) Λ I)`, with `pairSum(X) = (2N²)⁻¹ ∑_{i≠j} (g(x_i - x_j) + c*)`,
and `w ↦ F_N^{h_w}` is additive (`RowOK`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

variable {d : ℕ} {s : ℝ}

theorem adjke_riesz_continuousAt (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {z : Torus d} (hz : z ≠ 0) :
    ContinuousAt (periodicRiesz d s) z := by
  have hsm := KernelGrad.contDiffOn_periodicRiesz hd hs0 hsd
  have hopen : IsOpen {x : Euc d | Torus.mk x ≠ 0} :=
    (isOpen_ne : IsOpen {w : Torus d | w ≠ 0}).preimage KernelGrad.isOpenQuotientMap_mk.continuous
  have hr : Torus.mk (Torus.rep z) ≠ 0 := by rw [Torus.mk_rep]; exact hz
  have h1 : ContinuousAt (Torus.lift (periodicRiesz d s)) (Torus.rep z) :=
    (hsm.continuousOn).continuousAt (hopen.mem_nhds hr)
  have h2 : ContinuousAt (periodicRiesz d s ∘ (Torus.mk : Euc d → Torus d)) (Torus.rep z) := h1
  have h3 := (KernelGrad.isOpenQuotientMap_mk.continuousAt_comp_iff).mp h2
  rwa [Torus.mk_rep] at h3

/-- The pair sum controlling the modulated energy of a commutator kernel along a configuration. -/
def adjkePairSum (d : ℕ) (s cstar : ℝ) {N : ℕ} (X : Config d N) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, (periodicRiesz d s (X i - X j) + cstar)

theorem adjke_E_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {N : ℕ} (hN : 0 < N) :
    ∃ cstar A I : ℝ, 0 ≤ A ∧ 0 ≤ I ∧ ∀ {ρ : Torus d → ℝ}, IsProbDensity ρ → ∀ {Λ : ℝ}, (∀ y, ρ y ≤ Λ) →
      ∀ {w : Torus d → Euc d}, Continuous w → ∀ {L : ℝ}, 0 ≤ L → IsLipschitzVF L w →
      ∀ X : Config d N,
        RowOK (withDensityReal ρ) (commKernel (periodicRieszGrad d s) w) ∧
        |modulatedEnergy (commKernel (periodicRieszGrad d s) w) X (withDensityReal ρ)| ≤
          L * (A * (adjkePairSum d s cstar X + 3 / 2 * Λ * I)) := by
  obtain ⟨cstar, A, hA, hc1, hc0, hdom⟩ := Q40b.q40b_hdom hd hs0 hsd
  have hI : Integrable (fun z : Torus d => periodicRiesz d s z + cstar) :=
    (KernelAux.integrable_periodicRiesz hd hs0 hsd).add (integrable_const cstar)
  have hnn : ∀ z : Torus d, 0 ≤ periodicRiesz d s z + cstar := by
    intro z
    by_cases hz : z = 0
    · rw [hz]; exact hc0
    · linarith [hc1 z hz]
  set I : ℝ := ∫ z : Torus d, (periodicRiesz d s z + cstar) with hIdef
  have hI0 : 0 ≤ I := integral_nonneg hnn
  refine ⟨cstar, A, I, hA, hI0, ?_⟩
  intro ρ hρ Λ hΛ w hw L hL hLip X
  have hΛ0 : 0 ≤ Λ := (hρ.nonneg 0).trans (hΛ 0)
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hfin : IsFiniteMeasure (withDensityReal ρ) := inferInstance
  set k : Torus d → Torus d → ℝ := commKernel (periodicRieszGrad d s) w with hk
  have hmeas : Measurable (Function.uncurry k) := Q40b.q40b_commKernel_meas hsd hw
  have hrowm : ∀ x, Measurable (k x) := fun x => hmeas.comp (measurable_const.prodMk measurable_id)
  have hptw : ∀ x y, |k x y| ≤ (A * L) * (periodicRiesz d s (x - y) + cstar) :=
    fun x y => hdom L w hL hLip x y
  have hgx : ∀ x, Integrable (fun y : Torus d => (A * L) * (periodicRiesz d s (x - y) + cstar)) volume :=
    fun x => (hI.comp_sub_left x).const_mul (A * L)
  have hrowv : ∀ x, Integrable (k x) volume := fun x =>
    Integrable.mono' (hgx x) (hrowm x).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hptw x y)
  have hrowμ : ∀ x, Integrable (k x) (withDensityReal ρ) := fun x =>
    Duality.integrable_withDensityReal_of hΛ (hrowv x)
  have hrowI : ∀ x, ∫ y, |k x y| ∂(withDensityReal ρ) ≤ Λ * (A * L * I) := by
    intro x
    have h1 := Duality.integral_withDensityReal_le hΛ hΛ0 (g := fun y => |k x y|)
      (fun y => abs_nonneg _) (hrowv x).abs
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hΛ0)
    calc ∫ y, |k x y| ≤ ∫ y, (A * L) * (periodicRiesz d s (x - y) + cstar) :=
          integral_mono (hrowv x).abs (hgx x) (fun y => hptw x y)
      _ = A * L * I := by
          rw [integral_const_mul]
          congr 1
          exact integral_sub_left_eq_self (fun z : Torus d => periodicRiesz d s z + cstar) volume x
  have hrow : RowOK (withDensityReal ρ) k :=
    ⟨hmeas, hrowμ, ⟨Λ * (A * L * I), hrowI⟩⟩
  refine ⟨hrow, ?_⟩
  have hAL : 0 ≤ A * L * I := mul_nonneg (mul_nonneg hA hL) hI0
  have habsrow : ∀ x, |∫ y, k x y ∂(withDensityReal ρ)| ≤ Λ * (A * L * I) := fun x =>
    (abs_integral_le_integral_abs).trans (hrowI x)
  unfold modulatedEnergy
  set S1 : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j) with hS1
  set S2 : ℝ := ∑ i, ∫ y, k (X i) y ∂(withDensityReal ρ) with hS2
  set S3 : ℝ := ∫ x, ∫ y, k x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) with hS3
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hS1b : |S1| ≤ A * L * ∑ i, ∑ j ∈ Finset.univ.erase i, (periodicRiesz d s (X i - X j) + cstar) := by
    calc |S1| ≤ ∑ i, |∑ j ∈ Finset.univ.erase i, k (X i) (X j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, |k (X i) (X j)| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, (A * L) * (periodicRiesz d s (X i - X j) + cstar) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hptw _ _
      _ = A * L * ∑ i, ∑ j ∈ Finset.univ.erase i, (periodicRiesz d s (X i - X j) + cstar) := by
          simp only [← Finset.mul_sum]
  have hS2b : |S2| ≤ N * (Λ * (A * L * I)) := by
    calc |S2| ≤ ∑ i, |∫ y, k (X i) y ∂(withDensityReal ρ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, Λ * (A * L * I) := Finset.sum_le_sum fun i _ => habsrow _
      _ = N * (Λ * (A * L * I)) := by simp
  have hS3b : |S3| ≤ Λ * (A * L * I) := by
    have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρ)
      (f := fun x => ∫ y, k x y ∂(withDensityReal ρ)) (C := Λ * (A * L * I))
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact habsrow x)
    simpa [Measure.real, measure_univ] using this
  have e1 : |(1 / (2 * (N : ℝ) ^ 2)) * S1| ≤ (1 / (2 * (N : ℝ) ^ 2)) * (A * L *
      ∑ i, ∑ j ∈ Finset.univ.erase i, (periodicRiesz d s (X i - X j) + cstar)) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hS1b (by positivity)
  have e2 : |(1 / (N : ℝ)) * S2| ≤ Λ * (A * L * I) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / (N : ℝ) * |S2| ≤ 1 / (N : ℝ) * (N * (Λ * (A * L * I))) :=
          mul_le_mul_of_nonneg_left hS2b (by positivity)
      _ = Λ * (A * L * I) := by field_simp
  have e3 : |(1 / 2 : ℝ) * S3| ≤ (1 / 2) * (Λ * (A * L * I)) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left hS3b (by norm_num)
  have hfinal : |(1 / (2 * (N : ℝ) ^ 2)) * S1 - (1 / (N : ℝ)) * S2 + (1 / 2 : ℝ) * S3| ≤
      (1 / (2 * (N : ℝ) ^ 2)) * (A * L *
        ∑ i, ∑ j ∈ Finset.univ.erase i, (periodicRiesz d s (X i - X j) + cstar)) +
      Λ * (A * L * I) + (1 / 2) * (Λ * (A * L * I)) := by
    have h := abs_add_le (|(1 / (2 * (N : ℝ) ^ 2)) * S1 - (1 / (N : ℝ)) * S2|) 0
    calc _ ≤ |(1 / (2 * (N : ℝ) ^ 2)) * S1 - (1 / (N : ℝ)) * S2| + |(1 / 2 : ℝ) * S3| :=
          abs_add_le _ _
      _ ≤ (|(1 / (2 * (N : ℝ) ^ 2)) * S1| + |(1 / (N : ℝ)) * S2|) + |(1 / 2 : ℝ) * S3| := by
          gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  refine hfinal.trans (le_of_eq ?_)
  unfold adjkePairSum
  ring

/-- Additivity of the modulated energy in the vector field. -/
theorem adjke_E_sub {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {N : ℕ} {w w' : Torus d → Euc d}
    (hw : RowOK (withDensityReal ρ) (commKernel (periodicRieszGrad d s) w))
    (hw' : RowOK (withDensityReal ρ) (commKernel (periodicRieszGrad d s) w')) (X : Config d N) :
    modulatedEnergy (commKernel (periodicRieszGrad d s) (fun x => w x - w' x)) X (withDensityReal ρ) =
      modulatedEnergy (commKernel (periodicRieszGrad d s) w) X (withDensityReal ρ) -
        modulatedEnergy (commKernel (periodicRieszGrad d s) w') X (withDensityReal ρ) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hk : (commKernel (periodicRieszGrad d s) (fun x => w x - w' x)) =
      fun x y => commKernel (periodicRieszGrad d s) w x y - commKernel (periodicRieszGrad d s) w' x y := by
    funext x y
    unfold commKernel
    by_cases hxy : x = y
    · simp [hxy]
    · simp only [hxy, if_false]
      rw [← inner_sub_left]
      congr 1
      abel
  rw [hk]
  exact modulatedEnergy_sub hw hw' X

end HRS.AdjK
