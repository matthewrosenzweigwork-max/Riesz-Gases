import HRS.Sections.Q17Aux6

/-!
# Q17 projection 4: tensor powers and the final `projection_strong` (relocated proof)

Strong convergence of `P_L^{⊗j}` on the projective tensor power `projTensor B j`, from
elementary tensors (continuity of the elementary-tensor map) by density, using `‖P_L‖ ≤ 1`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.Sec7

variable {d : ℕ}

section Q17Tensor

set_option maxSynthPendingDepth 3

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- The elementary-tensor map `v ↦ x₁ ⊗ ⋯ ⊗ x_j` as a continuous `j`-linear map. -/
def q17_elemML (j : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin j => B) (TensorDual B j) :=
  MultilinearMap.mkContinuous
    { toFun := fun v => elemTensor v
      map_update_add' := fun m i x y => by
        apply ContinuousLinearMap.ext
        intro M
        show M (Function.update m i (x + y)) = M (Function.update m i x) + M (Function.update m i y)
        exact M.map_update_add m i x y
      map_update_smul' := fun m i c x => by
        apply ContinuousLinearMap.ext
        intro M
        show M (Function.update m i (c • x)) = c • M (Function.update m i x)
        exact M.map_update_smul m i c x }
    1 (fun v => by
      have hC : (0 : ℝ) ≤ 1 * ∏ i, ‖v i‖ := by positivity
      refine ContinuousLinearMap.opNorm_le_bound _ hC (fun M => ?_)
      have h := ContinuousMultilinearMap.le_opNorm M v
      show ‖M v‖ ≤ (1 * ∏ i, ‖v i‖) * ‖M‖
      calc ‖M v‖ ≤ ‖M‖ * ∏ i, ‖v i‖ := h
        _ = (1 * ∏ i, ‖v i‖) * ‖M‖ := by ring)

theorem q17_elemML_apply (j : ℕ) (v : Fin j → B) : q17_elemML (B := B) j v = elemTensor v := rfl

theorem q17_precomp_norm (j : ℕ) (P : B →L[ℝ] B) (hP : ‖P‖ ≤ 1) : ‖tensorPow j P‖ ≤ 1 := by
  unfold tensorPow
  set g := ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ) (fun _ : Fin j => P)
    with hg_def
  have hg : ‖g‖ ≤ 1 := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le ℝ (fun _ : Fin j => P)).trans ?_
    simpa using pow_le_one₀ (norm_nonneg P) hP
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => ?_)
  rw [one_mul]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u) (fun M => ?_)
  have h1 : (ContinuousLinearMap.precomp ℝ g u) M = u (g M) := rfl
  rw [h1]
  calc ‖u (g M)‖ ≤ ‖u‖ * ‖g M‖ := u.le_opNorm _
    _ ≤ ‖u‖ * (‖g‖ * ‖M‖) := mul_le_mul_of_nonneg_left (g.le_opNorm M) (norm_nonneg _)
    _ ≤ ‖u‖ * (1 * ‖M‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg (norm_nonneg _)) (norm_nonneg _)
    _ = ‖u‖ * ‖M‖ := by ring

theorem q17_tensorPow_elem (j : ℕ) (P : B →L[ℝ] B) (v : Fin j → B) :
    tensorPow j P (elemTensor v) = elemTensor (fun i => P (v i)) := by
  ext M
  rfl

theorem q17_tensorPow_tendsto_elem (P : ℕ → (B →L[ℝ] B))
    (hconv : ∀ x, Tendsto (fun L => P L x) atTop (𝓝 x)) (j : ℕ) (v : Fin j → B) :
    Tendsto (fun L => tensorPow j (P L) (elemTensor v)) atTop (𝓝 (elemTensor v)) := by
  simp_rw [q17_tensorPow_elem]
  have hc : Tendsto (fun L => fun i => P L (v i)) atTop (𝓝 v) :=
    tendsto_pi_nhds.2 fun i => hconv (v i)
  have := ((q17_elemML (B := B) j).cont.tendsto v).comp hc
  exact this

theorem q17_tensorPow_tendsto_span (P : ℕ → (B →L[ℝ] B))
    (hconv : ∀ x, Tendsto (fun L => P L x) atTop (𝓝 x)) (j : ℕ) (u : TensorDual B j)
    (hu : u ∈ Submodule.span ℝ (Set.range (elemTensor (B := B) (k := j)))) :
    Tendsto (fun L => tensorPow j (P L) u) atTop (𝓝 u) := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact q17_tensorPow_tendsto_elem P hconv j v
  | zero =>
    simp only [map_zero]
    exact tendsto_const_nhds
  | add x y _ _ hx hy =>
    simp only [map_add]
    exact hx.add hy
  | smul c x _ hx =>
    simp only [map_smul]
    exact hx.const_smul c

theorem q17_tensorPow_tendsto (P : ℕ → (B →L[ℝ] B)) (hP : ∀ L, ‖P L‖ ≤ 1)
    (hconv : ∀ x, Tendsto (fun L => P L x) atTop (𝓝 x)) (j : ℕ) (v : TensorDual B j)
    (hv : v ∈ projTensor B j) :
    Tendsto (fun L => tensorPow j (P L) v) atTop (𝓝 v) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcl : v ∈ closure ((Submodule.span ℝ (Set.range (elemTensor (B := B) (k := j))) :
      Set (TensorDual B j))) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hv
  obtain ⟨u, hu, hvu⟩ := Metric.mem_closure_iff.1 hcl (ε / 3) (by positivity)
  have hu' : u ∈ Submodule.span ℝ (Set.range (elemTensor (B := B) (k := j))) := hu
  have hpu := q17_tensorPow_tendsto_span P hconv j u hu'
  rw [Metric.tendsto_nhds] at hpu
  filter_upwards [hpu (ε / 3) (by positivity)] with L hL
  have hnorm : ‖tensorPow j (P L)‖ ≤ 1 := q17_precomp_norm j (P L) (hP L)
  have hvu' : dist (tensorPow j (P L) v) (tensorPow j (P L) u) ≤ dist v u := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    calc ‖tensorPow j (P L) (v - u)‖ ≤ ‖tensorPow j (P L)‖ * ‖v - u‖ :=
          (tensorPow j (P L)).le_opNorm _
      _ ≤ 1 * ‖v - u‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ = ‖v - u‖ := one_mul _
  have hvu'' : dist v u < ε / 3 := hvu
  calc dist (tensorPow j (P L) v) v
      ≤ dist (tensorPow j (P L) v) (tensorPow j (P L) u) + dist (tensorPow j (P L) u) v :=
        dist_triangle _ _ _
    _ ≤ dist (tensorPow j (P L) v) (tensorPow j (P L) u) + (dist (tensorPow j (P L) u) u +
        dist u v) := by
        gcongr
        exact dist_triangle _ _ _
    _ < ε := by
        rw [dist_comm u v] at *
        linarith [hL, hvu'', hvu']

end Q17Tensor

/-- The projection of `Remark 7.10` is strongly convergent on the path space. -/
theorem q17_projPoly_tendsto {m T : ℝ} (hT : 0 < T) (w : PathSpace d m T) :
    Tendsto (fun L : ℕ => projPoly m T hT.le L w) atTop (𝓝 w) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hwc : Continuous (q17_wf w) := (q17_wf w).continuous
  have hK : IsCompact (Set.range (q17_wf w)) := isCompact_range hwc
  obtain ⟨L₀, hL₀⟩ := q17_unif_proj hK (ε / 4) (by positivity)
  have hu := Metric.uniformContinuous_iff.1 (CompactSpace.uniformContinuous_of_continuous hwc)
    (ε / 4) (by positivity)
  obtain ⟨δ, hδ, hδu⟩ := hu
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℕ, T / δ < K1 := exists_nat_gt _
  filter_upwards [eventually_ge_atTop (max L₀ K1)] with L hL
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hLK : K1 ≤ L := le_trans (le_max_right _ _) hL
  have hpow : T / (2 : ℝ) ^ L < δ := by
    have hL2 : (L : ℝ) < (2 : ℝ) ^ L := by exact_mod_cast Nat.lt_two_pow_self
    have hK1' : (K1 : ℝ) ≤ L := by exact_mod_cast hLK
    have hTK : T < K1 * δ := (div_lt_iff₀ hδ).1 hK1
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
    rw [div_lt_iff₀ h2pos]
    nlinarith
  have hK2 : ∀ p q : Set.Icc (0 : ℝ) T, dist p q < δ → ‖q17_wf w p - q17_wf w q‖ < ε / 4 :=
    fun p q hpq => by
      rw [← dist_eq_norm]
      exact hδu hpq
  have hnorm : ‖projPoly m T hT.le L w - w‖ ≤ ε / 4 + ε / 4 := by
    refine (ContinuousMap.norm_le
      (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from projPoly m T hT.le L w - w)
      (by positivity)).2 ?_
    intro t
    have e : (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from projPoly m T hT.le L w - w) t =
        (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from projPoly m T hT.le L w) t -
          q17_wf w t := rfl
    rw [e]
    exact q17_proj_pointwise hT L w (ε / 4) (ε / 4) δ hpow (fun x hx => hL₀ L hL0 x hx) hK2 t
  rw [dist_eq_norm]
  linarith

end HRS.Sec7
