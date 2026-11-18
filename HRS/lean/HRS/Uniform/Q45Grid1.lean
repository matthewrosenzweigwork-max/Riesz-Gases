import HRS.Uniform.Q45Fin5

/-!
# Q45: the grid objects (coordinates, path synthesis map, block vectors)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The orthogonal-projection image `Σ_a ⟨b_a, w⟩ b_a`. -/
def projB {d : ℕ} (b : Fin d → E) (w : E) : E := ∑ a, inner ℝ (b a) w • b a

lemma norm_projB_le {d : ℕ} {b : Fin d → E} (hb : Orthonormal ℝ b) (w : E) : ‖projB b w‖ ≤ ‖w‖ := by
  have h1 := norm_embedCLM_apply hb (WithLp.toLp 2 (fun a => inner ℝ (b a) w))
  rw [embedCLM_apply] at h1
  have h2 : projB b w = ∑ a, (WithLp.toLp 2 (fun a => inner ℝ (b a) w) : EuclideanSpace ℝ (Fin d)) a • b a :=
    rfl
  rw [h2, h1, EuclideanSpace.norm_eq]
  have hbessel := hb.sum_inner_products_le w (s := Finset.univ)
  calc Real.sqrt (∑ i, ‖(WithLp.toLp 2 (fun a => inner ℝ (b a) w) : EuclideanSpace ℝ (Fin d)) i‖ ^ 2)
      ≤ Real.sqrt (‖w‖ ^ 2) := Real.sqrt_le_sqrt (by simpa using hbessel)
    _ = ‖w‖ := Real.sqrt_sq (norm_nonneg _)


/-- The `i`-th node vector `∑_a c_{(i,a)} b_a` of the synthesis map. -/
def synthVec {g d : ℕ} (b : Fin d → E) (c : ℝ^((g + 1) * d)) (i : Fin (g + 1)) : E :=
  ∑ a : Fin d, c (finProdFinEquiv (i, a)) • b a

lemma synthVec_add {g d : ℕ} (b : Fin d → E) (c c' : ℝ^((g + 1) * d)) :
    synthVec b (c + c') = synthVec b c + synthVec b c' := by
  funext i
  simp [synthVec, add_smul, Finset.sum_add_distrib]

lemma synthVec_smul {g d : ℕ} (b : Fin d → E) (r : ℝ) (c : ℝ^((g + 1) * d)) :
    synthVec b (r • c) = r • synthVec b c := by
  funext i
  simp [synthVec, smul_smul, Finset.smul_sum]

lemma norm_synthVec_le {g d : ℕ} {b : Fin d → E} (hb : Orthonormal ℝ b) (c : ℝ^((g + 1) * d))
    (i : Fin (g + 1)) : ‖synthVec b c i‖ ≤ ‖c‖ := by
  have h1 := norm_embedCLM_apply hb (WithLp.toLp 2 (fun a => c (finProdFinEquiv (i, a))))
  rw [embedCLM_apply] at h1
  have h2 : synthVec b c i = ∑ a, (WithLp.toLp 2 (fun a => c (finProdFinEquiv (i, a))) :
      EuclideanSpace ℝ (Fin d)) a • b a := rfl
  rw [h2, h1, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  have e : ∑ j, ‖c j‖ ^ 2 = ∑ p : Fin (g + 1) × Fin d, ‖c (finProdFinEquiv p)‖ ^ 2 :=
    (Equiv.sum_comp finProdFinEquiv (fun j => ‖c j‖ ^ 2)).symm
  rw [e, Fintype.sum_prod_type]
  calc ∑ a, ‖(WithLp.toLp 2 (fun a => c (finProdFinEquiv (i, a))) : EuclideanSpace ℝ (Fin d)) a‖ ^ 2
      = ∑ a, ‖c (finProdFinEquiv (i, a))‖ ^ 2 := rfl
    _ ≤ ∑ i', ∑ a, ‖c (finProdFinEquiv (i', a))‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ a, ‖c (finProdFinEquiv (i', a))‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

/-- The synthesis map `ℝ^{(g+1)d} → C([0,T];E)`, `c ↦ ∑_{i,a} c_{(i,a)} φ_i b_a`. -/
def pathMap {T : ℝ} (hT : 0 < T) {g : ℕ} (hg : 1 ≤ g) {d : ℕ} {b : Fin d → E} (hb : Orthonormal ℝ b) :
    (ℝ^((g + 1) * d)) →L[ℝ] PathSp T E :=
  LinearMap.mkContinuous
    { toFun := fun c => hatPath T g (synthVec b c)
      map_add' := fun c c' => by rw [synthVec_add, hatPath_add]
      map_smul' := fun r c => by
        rw [synthVec_smul, hatPath_smul]; rfl } 1
    (fun c => by
      rw [one_mul]
      exact norm_hatPath_le hT hg _ (norm_nonneg _) (norm_synthVec_le hb c))

lemma pathMap_apply {T : ℝ} (hT : 0 < T) {g : ℕ} (hg : 1 ≤ g) {d : ℕ} {b : Fin d → E}
    (hb : Orthonormal ℝ b) (c : ℝ^((g + 1) * d)) :
    pathMap hT hg hb c = hatPath T g (synthVec b c) := rfl

lemma norm_pathMap_le {T : ℝ} (hT : 0 < T) {g : ℕ} (hg : 1 ≤ g) {d : ℕ} {b : Fin d → E}
    (hb : Orthonormal ℝ b) : ‖pathMap hT hg hb‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end HRS.Uniform.Q45
