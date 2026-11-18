import HRS.MC.S7FCBGram

/-!
# FC-B, part 10: `fcbT n h` is a smooth finite-rank symmetric kernel
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.FCB

open HRS HRS.KernelAux

variable {d : ℕ}

local instance fcb_borel_prod2f : BorelSpace (Torus d × Torus d) := Prod.borelSpace
local instance fcb_open_prod4f : OpensMeasurableSpace ((Torus d × Torus d) × Torus d × Torus d) :=
  Prod.opensMeasurableSpace

theorem fcb_integrable_cont_mul {h' : Torus d × Torus d → ℝ} (hi : Integrable h' (volume.prod volume))
    {u : Torus d × Torus d → ℝ} (hu : Continuous u) :
    Integrable (fun q => u q * h' q) (volume.prod volume) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hu.continuousOn
  exact hi.bdd_mul hu.aestronglyMeasurable (c := C) (Eventually.of_forall fun q => by
    have := hC q (mem_univ _); simpa using this)

theorem fcbT_finite_rank (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) {h' : Torus d × Torus d → ℝ}
    (hi : Integrable h' (volume.prod volume)) (hsym : ∀ q : Torus d × Torus d, h' q.swap = h' q) :
    ∃ (m : ℕ) (p : Fin m → Torus d → ℝ) (c : Fin m → Fin m → ℝ),
      (∀ i, Torus.IsSmooth (p i)) ∧ (∀ i j, c i j = c j i) ∧
      ∀ x y, fcbT d n h' (x, y) = ∑ i, ∑ j, c i j * p i x * p j y := by
  obtain ⟨m, p, hp, hK0⟩ := fcbK_gram hd hn
  have hK : ∀ x x' : Torus d, fcbK d n (x - x') = ∑ i, p i x * p i x' := hK0
  have hpc : ∀ i, Continuous (p i) := fun i => fcb_smooth_continuous (hp i)
  let c : Fin m → Fin m → ℝ := fun a b => ∫ q, p a q.1 * p b q.2 * h' q ∂(volume.prod volume)
  have hF : ∀ a b, Integrable (fun q : Torus d × Torus d => p a q.1 * p b q.2 * h' q) (volume.prod volume) :=
    fun a b => fcb_integrable_cont_mul hi (((hpc a).comp continuous_fst).mul ((hpc b).comp continuous_snd))
  refine ⟨m, p, c, hp, fun a b => ?_, fun x y => ?_⟩
  · have e := integral_prod_swap (μ := (volume : Measure (Torus d))) (ν := (volume : Measure (Torus d)))
      (fun z : Torus d × Torus d => p a z.1 * p b z.2 * h' z)
    show ∫ q, p a q.1 * p b q.2 * h' q ∂(volume.prod volume) = ∫ q, p b q.1 * p a q.2 * h' q ∂(volume.prod volume)
    rw [← e]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Prod.fst_swap, Prod.snd_swap, hsym z]
    ring
  · unfold fcbT
    have key : ∀ q : Torus d × Torus d, fcbKap d n ((x, y) - q) * h' q =
        ∑ a, ∑ b, p a x * p b y * (p a q.1 * p b q.2 * h' q) := by
      intro q
      simp only [fcbKap, Prod.fst_sub, Prod.snd_sub]
      rw [hK, hK, Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    refine (integral_congr_ae (Eventually.of_forall key)).trans ?_
    rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ => (hF a b).const_mul _))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ (fun b _ => (hF a b).const_mul _)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul]
    show _ = c a b * p a x * p b y
    ring

end HRS.MC.Sec7.FCB
