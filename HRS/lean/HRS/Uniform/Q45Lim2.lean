import HRS.Uniform.Q45Lim1

/-!
# Q45: the Riemann sums on the grid converge in `L¹` (from the `L²` definition of the stochastic convolution)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} [MeasurableSpace Ω]

lemma rsum_eq_riemannSum (S : EvolData H E) (T : ℝ) (g κ : ℕ) (M : ℝ → Ω → H) (i : ℕ) (ω : Ω) :
    rsum S T g κ M i ω = riemannSum S.VE S.j M (unifPart T g i) (n := i * κ)
      (fun k => rr (g * κ) T (k : ℕ)) ω := by
  unfold rsum riemannSum
  rw [← Fin.sum_univ_eq_sum_range (fun k => S.VE (unifPart T g i) (rr (g * κ) T k)
    (S.j (M (rr (g * κ) T (k + 1)) ω - M (rr (g * κ) T k) ω))) (i * κ)]
  rfl

lemma enorm_le_add_sq (f η : ℝ≥0∞) (hη0 : η ≠ 0) (hηt : η ≠ ⊤) : f ≤ η + f ^ 2 / η := by
  by_cases h : f ≤ η
  · exact h.trans le_self_add
  · rw [not_le] at h
    refine le_trans ?_ le_add_self
    rw [sq, ENNReal.le_div_iff_mul_le (Or.inl hη0) (Or.inl hηt)]
    exact mul_le_mul' le_rfl h.le

/-- `L²`-closeness gives `L¹`-closeness (probability measure). -/
lemma lintegral_le_of_lintegral_sq_le (P : Measure Ω) [IsProbabilityMeasure P] {f : Ω → ℝ≥0∞}
    {η : ℝ≥0∞} (hη0 : η ≠ 0) (hηt : η ≠ ⊤) :
    ∫⁻ ω, f ω ∂P ≤ η + (∫⁻ ω, f ω ^ 2 ∂P) / η := by
  calc ∫⁻ ω, f ω ∂P ≤ ∫⁻ ω, (η + f ω ^ 2 / η) ∂P := lintegral_mono fun ω => enorm_le_add_sq _ _ hη0 hηt
    _ = η + (∫⁻ ω, f ω ^ 2 ∂P) / η := by
        rw [lintegral_add_left measurable_const]
        simp only [lintegral_const, measure_univ, mul_one]
        congr 1
        simp only [div_eq_mul_inv]
        exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hη0)


lemma rr_succ_sub {T : ℝ} {g κ : ℕ} (hg : 1 ≤ g) (hκ : 1 ≤ κ) (k : ℕ) :
    rr (g * κ) T (k + 1) - rr (g * κ) T k = T / ((g : ℝ) * κ) := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hκ' : (0 : ℝ) < κ := by exact_mod_cast hκ
  unfold rr unifPart
  push_cast
  field_simp
  ring

lemma rr_grid_end {T : ℝ} {g κ : ℕ} (hg : 1 ≤ g) (hκ : 1 ≤ κ) (i : ℕ) :
    rr (g * κ) T (i * κ) = unifPart T g i := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hκ' : (0 : ℝ) < κ := by exact_mod_cast hκ
  unfold rr unifPart
  push_cast
  field_simp

lemma rsum_L1_close {T : ℝ} (hT : 0 < T) {g : ℕ} (hg : 1 ≤ g) (P : Measure Ω) [IsProbabilityMeasure P]
    (S : EvolData H E) (M : ℝ → Ω → H) (Z : ℝ → Ω → E)
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j M 0 t (Z t)) {η : ℝ} (hη : 0 < η) :
    ∃ κ0 : ℕ, ∀ κ ≥ κ0, 1 ≤ κ → ∀ i : Fin (g + 1),
      ∫⁻ ω, ‖Z (unifPart T g i) ω - rsum S T g κ M i ω‖ₑ ∂P ≤ ENNReal.ofReal η := by
  set ε2 : ℝ := η ^ 2 / 4 with hε2
  have hε2p : 0 < ε2 := by positivity
  have hmem : ∀ i : Fin (g + 1), unifPart T g i ∈ Set.Icc (0 : ℝ) T := fun i =>
    ⟨unifPart_nonneg hT.le _ _, gridT_le hT hg i⟩
  choose δ hδ hconv using fun i : Fin (g + 1) => hZ _ (hmem i) ε2 hε2p
  refine ⟨Finset.univ.sup (fun i : Fin (g + 1) => ⌈T / δ i⌉₊ + 1), fun κ hκ hκ1 i => ?_⟩
  have hκi : ⌈T / δ i⌉₊ + 1 ≤ κ := (Finset.le_sup (f := fun i : Fin (g + 1) => ⌈T / δ i⌉₊ + 1)
    (Finset.mem_univ i)).trans hκ
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hκ' : (0 : ℝ) < κ := by exact_mod_cast hκ1
  have hmesh : T / ((g : ℝ) * κ) < δ i := by
    have h1 : T / δ i < κ := by
      have := Nat.le_ceil (T / δ i)
      have h2 : (⌈T / δ i⌉₊ : ℝ) + 1 ≤ κ := by exact_mod_cast hκi
      linarith
    have h3 : T < κ * δ i := (div_lt_iff₀ (hδ i)).1 h1
    have h4 : T / ((g : ℝ) * κ) ≤ T / κ := by
      refine div_le_div_of_nonneg_left hT.le hκ' ?_
      have : (1 : ℝ) ≤ g := by exact_mod_cast hg
      nlinarith
    exact h4.trans_lt ((div_lt_iff₀ hκ').2 (by linarith))
  have hNb : 1 ≤ g * κ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hL2 := hconv i (i * κ) (fun k => rr (g * κ) T (k : ℕ)) (by simp [rr, unifPart])
    (by
      show rr (g * κ) T ((Fin.last (i * κ) : Fin (i * κ + 1)) : ℕ) = _
      rw [Fin.val_last, rr_grid_end hg hκ1])
    (fun a b hab => rr_mono hT.le hNb (Fin.le_def.1 hab))
    (fun k => by
      show rr (g * κ) T (k.succ : ℕ) - rr (g * κ) T (k.castSucc : ℕ) < δ i
      rw [Fin.val_succ, Fin.val_castSucc, rr_succ_sub hg hκ1]
      exact hmesh)
  have hL2' : ∫⁻ ω, ‖Z (unifPart T g i) ω - rsum S T g κ M i ω‖ₑ ^ 2 ∂P < ENNReal.ofReal ε2 := by
    simpa only [rsum_eq_riemannSum] using hL2
  have hη1 : ENNReal.ofReal (η / 2) ≠ 0 := by
    simpa using (show 0 < η / 2 by positivity)
  refine (lintegral_le_of_lintegral_sq_le P hη1 ENNReal.ofReal_ne_top).trans ?_
  have hdiv : (∫⁻ ω, ‖Z (unifPart T g i) ω - rsum S T g κ M i ω‖ₑ ^ 2 ∂P) / ENNReal.ofReal (η / 2) ≤
      ENNReal.ofReal (η / 2) := by
    calc _ ≤ ENNReal.ofReal ε2 / ENNReal.ofReal (η / 2) := by gcongr
      _ = ENNReal.ofReal (ε2 / (η / 2)) :=
          (ENNReal.ofReal_div_of_pos (show 0 < η / 2 by positivity)).symm
      _ = ENNReal.ofReal (η / 2) := by
          congr 1
          rw [hε2]; field_simp; ring
  calc ENNReal.ofReal (η / 2) + _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
        add_le_add le_rfl hdiv
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end HRS.Uniform.Q45
