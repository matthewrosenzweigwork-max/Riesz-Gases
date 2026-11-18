import HRS.MS.R2InterpAux1

/-!
# S10.2 (worker S102), part 2: the projections `P_L` of `OscPath` (Hermite truncation + polygonal interpolation)

`Q_L u = ` truncation of `u ∈ B_m` to the Hermite indices of degree `≤ L` (a contraction of `ℓ²` converging strongly to the identity),
`s102_Pj L` = polygonal interpolation of `Q_L` on the dyadic grid; the whole-space analogue of `HRS.Sec7.projection_strong`
(`HRS/Sections/Q17Aux8.lean`).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.R2Interp

open HRS HRS.Sec7 HRS.Whole

variable {d : ℕ} {m : ℝ}

open Classical in
/-- The coordinates of the truncation. -/
def s102_truncSeq (L : ℕ) (u : OscDual d m) : MultiIndex d → ℝ :=
  fun α => if α.degree ≤ L then OscDual.coord u α else 0

theorem s102_truncSeq_mem (L : ℕ) (u : OscDual d m) : Memℓp (s102_truncSeq L u) 2 := by
  rw [memℓp_two_iff]
  refine Summable.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => ?_) (OscDual.coord_sq_summable' u)
  unfold s102_truncSeq
  split_ifs
  · exact le_rfl
  · simp [sq_nonneg]

/-- The Hermite truncation. -/
def s102_trunc (L : ℕ) (u : OscDual d m) : OscDual d m :=
  (⟨s102_truncSeq L u, s102_truncSeq_mem L u⟩ : lp (fun _ : MultiIndex d => ℝ) 2)

theorem s102_coord_trunc (L : ℕ) (u : OscDual d m) (α : MultiIndex d) :
    OscDual.coord (s102_trunc L u) α = if α.degree ≤ L then OscDual.coord u α else 0 := rfl

theorem s102_ext {u v : OscDual d m} (h : ∀ α, OscDual.coord u α = OscDual.coord v α) : u = v :=
  lp.ext (funext h)

theorem s102_trunc_add (L : ℕ) (u v : OscDual d m) :
    s102_trunc L (u + v) = s102_trunc L u + s102_trunc L v := by
  apply s102_ext
  intro α
  rw [OscDual.coord_add, s102_coord_trunc, s102_coord_trunc, s102_coord_trunc, OscDual.coord_add]
  split_ifs <;> simp

theorem s102_trunc_smul (L : ℕ) (c : ℝ) (u : OscDual d m) :
    s102_trunc L (c • u) = c • s102_trunc L u := by
  apply s102_ext
  intro α
  rw [OscDual.coord_smul, s102_coord_trunc, s102_coord_trunc, OscDual.coord_smul]
  split_ifs <;> simp

theorem s102_norm_trunc_le (L : ℕ) (u : OscDual d m) : ‖s102_trunc L u‖ ≤ ‖u‖ := by
  rw [OscDual.norm_eq_coord, OscDual.norm_eq_coord]
  refine Real.sqrt_le_sqrt ?_
  refine Summable.tsum_le_tsum (fun α => ?_)
    (by simpa [OscDual.coord] using lp_two_summable (ι := MultiIndex d) (s102_trunc L u))
    (OscDual.coord_sq_summable' u)
  rw [s102_coord_trunc]
  split_ifs
  · exact le_rfl
  · simp [sq_nonneg]

/-- The truncation as a contraction of `B_m`. -/
def s102_truncCLM (L : ℕ) : OscDual d m →L[ℝ] OscDual d m :=
  LinearMap.mkContinuous
    { toFun := s102_trunc L
      map_add' := s102_trunc_add L
      map_smul' := fun c u => by simpa using s102_trunc_smul L c u } 1
    (fun u => by simpa using s102_norm_trunc_le L u)

theorem s102_truncCLM_apply (L : ℕ) (u : OscDual d m) : s102_truncCLM L u = s102_trunc L u := rfl

theorem s102_truncCLM_norm_le (L : ℕ) : ‖(s102_truncCLM L : OscDual d m →L[ℝ] OscDual d m)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem s102_trunc_tendsto (u : OscDual d m) :
    Tendsto (fun L : ℕ => s102_trunc L u) atTop (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ L : ℕ, ‖s102_trunc L u - u‖ =
      Real.sqrt (∑' α : MultiIndex d, (OscDual.coord (s102_trunc L u - u) α) ^ 2) :=
    fun L => OscDual.norm_eq_coord _
  simp_rw [hnorm]
  have h0 : Tendsto (fun L : ℕ => ∑' α : MultiIndex d, (OscDual.coord (s102_trunc L u - u) α) ^ 2)
      atTop (𝓝 (∑' α : MultiIndex d, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (OscDual.coord_sq_summable' u) (fun α => ?_)
      (Filter.Eventually.of_forall (fun L α => ?_))
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop α.degree] with L hL
      rw [sub_eq_add_neg, show (-u) = (-1 : ℝ) • u by simp, OscDual.coord_add, OscDual.coord_smul,
        s102_coord_trunc, if_pos hL]
      simp
    · rw [sub_eq_add_neg, show (-u) = (-1 : ℝ) • u by simp, OscDual.coord_add, OscDual.coord_smul,
        s102_coord_trunc]
      split_ifs <;> simp <;> positivity
  rw [tsum_zero] at h0
  have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
  rw [Real.sqrt_zero] at h1
  exact h1

/-- The projections `P_L` of the path space. -/
def s102_Pj (T : ℝ) (hT : 0 < T) (L : ℕ) : OscPath d m T →L[ℝ] OscPath d m T :=
  s102_poly (E := OscDual d m) hT (fun L => s102_truncCLM L) (fun L => s102_truncCLM_norm_le L) L

theorem s102_Pj_apply (T : ℝ) (hT : 0 < T) (L : ℕ) (w : OscPath d m T) (t : Set.Icc (0 : ℝ) T) :
    OscPath.at' (s102_Pj T hT L w) t =
      ∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i •
        s102_trunc L (OscPath.at' w (Set.projIcc 0 T hT.le (i * T / 2 ^ L))) := rfl

/-- The whole-space `projection_strong`: contractions, strong convergence, and convergence of the tensor powers on `projTensor`. -/
theorem s102_projection_strong (m T : ℝ) (hT : 0 < T) :
    (∀ L, ‖(s102_Pj T hT L : OscPath d m T →L[ℝ] OscPath d m T)‖ ≤ 1) ∧
    (∀ w : OscPath d m T, Tendsto (fun L => s102_Pj T hT L w) atTop (𝓝 w)) ∧
    ∀ (j : ℕ) (v : TensorDual (OscPath d m T) j), v ∈ projTensor (OscPath d m T) j →
      Tendsto (fun L => tensorPow j (s102_Pj T hT L) v) atTop (𝓝 v) := by
  have h1 : ∀ L, ‖(s102_Pj T hT L : OscPath d m T →L[ℝ] OscPath d m T)‖ ≤ 1 :=
    fun L => s102_poly_norm_le (E := OscDual d m) hT _ _ L
  have h2 : ∀ w : OscPath d m T, Tendsto (fun L => s102_Pj T hT L w) atTop (𝓝 w) :=
    fun w => s102_poly_tendsto (E := OscDual d m) hT (fun L => s102_truncCLM L)
      (fun L => s102_truncCLM_norm_le L) (fun x => s102_trunc_tendsto x) w
  exact ⟨h1, h2, fun j v hv => q17_tensorPow_tendsto (fun L => s102_Pj T hT L) h1 h2 j v hv⟩

end HRS.MS.R2Interp

end
