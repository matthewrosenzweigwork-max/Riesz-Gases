import HRS.Uniform.Q45Grid4

/-!
# Q45: continuity of the interpolation map and the grid-approximation lemma
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma hatPath_sub (T : ℝ) (g : ℕ) (v w : Fin (g + 1) → E) :
    hatPath T g (v - w) = hatPath T g v - hatPath T g w := by
  have h1 : v - w = v + (-1 : ℝ) • w := by simp [sub_eq_add_neg]
  rw [h1, hatPath_add, hatPath_smul]
  simp [sub_eq_add_neg]

/-- The interpolation map as a continuous linear map from node values. -/
def hatCLM {T : ℝ} (hT : 0 < T) {g : ℕ} (hg : 1 ≤ g) : (Fin (g + 1) → E) →L[ℝ] PathSp T E :=
  LinearMap.mkContinuous
    { toFun := fun v => hatPath T g v
      map_add' := fun v w => hatPath_add T g v w
      map_smul' := fun r v => by rw [hatPath_smul]; rfl } 1
    (fun v => by
      rw [one_mul]
      exact norm_hatPath_le hT hg v (norm_nonneg _) (fun i => norm_le_pi_norm v i))

lemma hatCLM_apply {T : ℝ} (hT : 0 < T) {g : ℕ} (hg : 1 ≤ g) (v : Fin (g + 1) → E) :
    hatCLM hT hg v = hatPath T g v := rfl

lemma continuous_hatPath {T : ℝ} (hT : 0 < T) {g : ℕ} (hg : 1 ≤ g) :
    Continuous (fun v : Fin (g + 1) → E => hatPath T g v) :=
  (hatCLM hT hg).continuous


variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Grid + spatial projection approximates a continuous path uniformly. -/
lemma lambda_approx {T : ℝ} (hT : 0 < T) {d : ℕ → ℕ} {b : ∀ n, Fin (d n) → E}
    (hb : ∀ n, Orthonormal ℝ (b n))
    (hspat : ∀ (y : PathSp T E) (ε : ℝ), 0 < ε → ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t : Set.Icc (0 : ℝ) T,
      ‖pcm y t - ∑ a, inner ℝ (b n a) (pcm y t) • b n a‖ ≤ ε)
    (y : PathSp T E) {ε : ℝ} (hε : 0 < ε) :
    ∃ n0 : ℕ, ∀ n ≥ n0,
      ‖hatPath T (n + 1) (fun i => projB (b n) (samplePath hT.le (n + 1) y i)) - y‖ ≤ ε := by
  obtain ⟨n1, hn1⟩ := hspat y (ε / 2) (by positivity)
  obtain ⟨g0, hg0⟩ := hatPath_sample_close hT y (show 0 < ε / 2 by positivity)
  refine ⟨max n1 g0, fun n hn => ?_⟩
  have hn1' : n1 ≤ n := (le_max_left _ _).trans hn
  have hg0' : g0 ≤ n := (le_max_right _ _).trans hn
  have h1 : ‖hatPath T (n + 1) (fun i => projB (b n) (samplePath hT.le (n + 1) y i)) -
      hatPath T (n + 1) (samplePath hT.le (n + 1) y)‖ ≤ ε / 2 := by
    rw [← hatPath_sub]
    refine norm_hatPath_le hT (Nat.le_add_left 1 n) _ (by positivity) fun i => ?_
    have := hn1 n hn1' (Set.projIcc 0 T hT.le (i * T / (n + 1 : ℕ)))
    simp only [Pi.sub_apply, samplePath, projB]
    rw [norm_sub_rev]
    exact this
  have h2 := hg0 (n + 1) (by omega) (Nat.le_add_left 1 n)
  calc ‖hatPath T (n + 1) (fun i => projB (b n) (samplePath hT.le (n + 1) y i)) - y‖
      ≤ ‖hatPath T (n + 1) (fun i => projB (b n) (samplePath hT.le (n + 1) y i)) -
          hatPath T (n + 1) (samplePath hT.le (n + 1) y)‖ +
        ‖hatPath T (n + 1) (samplePath hT.le (n + 1) y) - y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := by ring

end HRS.Uniform.Q45
