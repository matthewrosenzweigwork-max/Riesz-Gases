import HRS.Uniform.Q45Blocks2

/-!
# Q45: comparison of two block transforms (Lindeberg for block-constant integrands)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {m q : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
lemma taylorRem_integrable {p : ℕ} {X : Ω → ℝ^p} (hX : MemLp X 2 P) (H L : ℝ) (hH : 0 ≤ H)
    (hL : 0 ≤ L) [IsFiniteMeasure P] : Integrable (fun ω => taylorRem H L (X ω)) P := by
  refine Integrable.mono' ((hX.norm.integrable_sq).const_mul H)
    ((continuous_taylorRem H L).comp_aestronglyMeasurable hX.aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  have h0 : 0 ≤ taylorRem H L (X ω) := taylorRem_nonneg hH hL _
  simp only [Real.norm_eq_abs, abs_of_nonneg h0]
  exact taylorRem_le_left H L _

lemma taylorRem_mono {p p' : ℕ} {c : ℝ} (hc : 0 ≤ c) {H L : ℝ} (hH : 0 ≤ H) (hL : 0 ≤ L)
    {v : ℝ^p} {w : ℝ^p'} (h : ‖v‖ ≤ c * ‖w‖) :
    taylorRem H L v ≤ taylorRem (H * c ^ 2) (L * c ^ 3) w := by
  unfold taylorRem
  refine min_le_min ?_ ?_
  · calc H * ‖v‖ ^ 2 ≤ H * (c * ‖w‖) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h 2) hH
      _ = H * c ^ 2 * ‖w‖ ^ 2 := by ring
  · calc L * ‖v‖ ^ 3 ≤ L * (c * ‖w‖) ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h 3) hL
      _ = L * c ^ 3 * ‖w‖ ^ 3 := by ring

/-- Cells of the partition with `Nb * (ℓ+1)` pieces lie inside blocks. -/
lemma cell_in_block {T : ℝ} (hT : 0 ≤ T) {Nb : ℕ} (hNb : 1 ≤ Nb) (ℓ j : ℕ) (hj : j < Nb * (ℓ + 1)) :
    ∃ k < Nb, rr Nb T k ≤ unifPart T (Nb * (ℓ + 1)) j ∧
      unifPart T (Nb * (ℓ + 1)) (j + 1) ≤ rr Nb T (k + 1) := by
  refine ⟨j / (ℓ + 1), ?_, ?_, ?_⟩
  · exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos ℓ)).2 (by linarith [mul_comm Nb (ℓ + 1)])
  · have h1 : j / (ℓ + 1) * (ℓ + 1) ≤ j := Nat.div_mul_le_self _ _
    have hNb' : (0 : ℝ) < Nb := by exact_mod_cast hNb
    have hl' : (0 : ℝ) < ℓ + 1 := by positivity
    unfold rr unifPart
    rw [div_le_div_iff₀ hNb' (by positivity)]
    have : ((j / (ℓ + 1) : ℕ) : ℝ) * (ℓ + 1) ≤ j := by exact_mod_cast h1
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right this hT]
  · have h1 : j + 1 ≤ (j / (ℓ + 1) + 1) * (ℓ + 1) := by
      have := Nat.lt_div_mul_add (a := j) (b := ℓ + 1) (Nat.succ_pos ℓ)
      nlinarith [Nat.div_add_mod j (ℓ + 1), Nat.mod_lt j (Nat.succ_pos ℓ)]
    have hNb' : (0 : ℝ) < Nb := by exact_mod_cast hNb
    have hl' : (0 : ℝ) < ℓ + 1 := by positivity
    unfold rr unifPart
    rw [div_le_div_iff₀ (by positivity) hNb']
    have : ((j + 1 : ℕ) : ℝ) ≤ ((j / (ℓ + 1) + 1 : ℕ) : ℝ) * (ℓ + 1) := by exact_mod_cast h1
    push_cast at this ⊢
    nlinarith [mul_le_mul_of_nonneg_right this hT]


section Tendsto

variable {ℱ : Filtration ℝ mΩ} {T : ℝ} {Nb : ℕ} {A : ℕ → Matrix (Fin m) (Fin q) ℝ}
  {N : ℝ → Ω → ℝ^q} {Sq : ℝ → Ω → Matrix (Fin q) (Fin q) ℝ}

lemma blockProc_tendsto (hT : 0 < T) (hNb : 1 ≤ Nb) {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ k (u : Fin q → ℝ), ((A k).mulVec u) ⬝ᵥ ((A k).mulVec u) ≤ c ^ 2 * (u ⬝ᵥ u))
    (hN : IsVectorMartingaleWithCovariation P ℱ T N Sq) (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) :
    Tendsto (fun ℓ : ℕ => ∑ k ∈ Finset.range (Nb * (ℓ + 1)),
      ∫ ω, taylorRem H L (blockProc A Nb T N (unifPart T (Nb * (ℓ + 1)) (k + 1)) ω -
        blockProc A Nb T N (unifPart T (Nb * (ℓ + 1)) k) ω) ∂P) atTop (𝓝 0) := by
  have hnn : Tendsto (fun ℓ : ℕ => Nb * (ℓ + 1)) atTop atTop := by
    refine tendsto_atTop_mono (fun ℓ => ?_) (tendsto_add_atTop_nat 1)
    nlinarith
  have hbase := (martingale_lindeberg_tendsto P ℱ T hT.le N Sq hN (H * c ^ 2) (L * c ^ 3)
    (by positivity) (by positivity)).comp hnn
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbase
    (fun ℓ => Finset.sum_nonneg fun j _ => integral_nonneg fun ω => taylorRem_nonneg hH hL _)
    (fun ℓ => ?_)
  refine Finset.sum_le_sum fun j hj => ?_
  have hjl := Finset.mem_range.1 hj
  obtain ⟨k, hk, h1, h3⟩ := cell_in_block hT.le hNb ℓ j hjl
  have hτ0 : 0 ≤ unifPart T (Nb * (ℓ + 1)) j := unifPart_nonneg hT.le _ _
  have hτm : unifPart T (Nb * (ℓ + 1)) j ≤ unifPart T (Nb * (ℓ + 1)) (j + 1) :=
    unifPart_mono hT.le _ (Nat.le_succ j)
  have hτT : unifPart T (Nb * (ℓ + 1)) (j + 1) ≤ T :=
    unifPart_le hT.le (Nat.succ_le_of_lt hjl)
  have hmem0 : unifPart T (Nb * (ℓ + 1)) j ∈ Set.Icc (0 : ℝ) T := ⟨hτ0, hτm.trans hτT⟩
  have hmem1 : unifPart T (Nb * (ℓ + 1)) (j + 1) ∈ Set.Icc (0 : ℝ) T := ⟨hτ0.trans hτm, hτT⟩
  have hint : Integrable (fun ω => taylorRem (H * c ^ 2) (L * c ^ 3)
      (N (unifPart T (Nb * (ℓ + 1)) (j + 1)) ω - N (unifPart T (Nb * (ℓ + 1)) j) ω)) P :=
    taylorRem_integrable P ((hN.sq_int _ hmem1).sub (hN.sq_int _ hmem0)) _ _ (by positivity)
      (by positivity)
  refine integral_mono_of_nonneg (ae_of_all _ fun ω => taylorRem_nonneg hH hL _) hint
    (ae_of_all _ fun ω => ?_)
  show taylorRem H L (blockProc A Nb T N (unifPart T (Nb * (ℓ + 1)) (j + 1)) ω -
      blockProc A Nb T N (unifPart T (Nb * (ℓ + 1)) j) ω) ≤ _
  rw [blockProc_cell (A := A) hT.le hNb N hk h1 hτm h3 ω]
  exact taylorRem_mono hc hH hL (norm_actCLM_le (A k) hc (hA k) _)

end Tendsto

end HRS.Uniform.Q45
