import HRS.MS.CovMeasAux21

/-!
# S10.1 (worker S101B), part 22: coordinates of the reconstruction and the evaluation `OscDual.eval` on finite combinations

`s101_eval_combo`: `u(Σ c_α φ_α) = Σ c_α coord_α u`.  `s101_recon_coord`: for `y ∈ C([0,T];𝒦)` and `t ∈ [0,T]`
`coord_α ((𝒯 y)(t)) = ⟨y(T), P_{t,α}⟩ + ⟨y(t), Q_α⟩` with `P_{t,α} = (e_α, 1_{[0,t]}e_α, -e_α)`, `Q_α = (0,0,e_α)`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9

variable {d : ℕ} {m T : ℝ}

lemma s101_eval_combo (u : OscDual d m) (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    OscDual.eval u (fun x => ∑ α ∈ S, c α * oscTestFun m α x) = ∑ α ∈ S, c α * OscDual.coord u α := by
  classical
  have hc : ∀ β, Whole.hermiteCoeff (fun x => ∑ α ∈ S, c α * oscTestFun m α x) β =
      ∑ α ∈ S, c α * Whole.hermiteCoeff (oscTestFun m α) β := by
    intro β
    unfold Whole.hermiteCoeff
    simp_rw [Finset.sum_mul]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun α _ => ?_
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [mul_assoc]
    · intro α _
      have := (integrable_hermiteFunD_mul α β).const_mul (c α * oscEigenvalue d α ^ (-(m / 2)))
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [oscTestFun]; ring
  unfold OscDual.eval
  simp_rw [hc, Finset.mul_sum]
  have hs : ∀ α ∈ S, Summable fun β => OscDual.hermiteCoeff u β *
      (c α * Whole.hermiteCoeff (oscTestFun m α) β) := by
    intro α _
    refine summable_of_ne_finset_zero (s := {α}) fun β hβ => ?_
    have : β ≠ α := by simpa using hβ
    rw [hermiteCoeff_oscTestFun]
    simp [this.symm]
  rw [Summable.tsum_finsetSum hs]
  refine Finset.sum_congr rfl fun α _ => ?_
  have e : ∀ β, OscDual.hermiteCoeff u β * (c α * Whole.hermiteCoeff (oscTestFun m α) β) =
      c α * (OscDual.hermiteCoeff u β * Whole.hermiteCoeff (oscTestFun m α) β) := fun β => by ring
  simp_rw [e]
  rw [tsum_mul_left]
  have := OscDual.eval_oscTestFun u α
  unfold OscDual.eval at this
  rw [this]

/-- `P_{t,α} = (e_α, 1_{[0,t]} e_α, -e_α)`. -/
def s101P (m T t : ℝ) (α : MultiIndex d) : KSpace d m T :=
  KSpace.mk (s101e m α) (s101Ind m T t (s101e m α)) (-(s101e m α))

/-- `Q_α = (0, 0, e_α)`. -/
def s101Q (m T : ℝ) (α : MultiIndex d) : KSpace d m T := KSpace.mk 0 0 (s101e m α)

theorem s101_recon_coord (hT : 0 ≤ T) (y : PathSp T (KSpace d m T)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (α : MultiIndex d) :
    OscDual.coord (r2PathAt (s56_reconCLM hT y : OscPath d m T) t) α =
      inner ℝ (pcm y ⟨T, hT, le_rfl⟩) (s101P m T t α) + inner ℝ (pcm y ⟨t, ht⟩) (s101Q m T α) := by
  have hrec := s56_reconCLM_apply hT y ⟨t, ht⟩
  have e0 : r2PathAt (s56_reconCLM hT y : OscPath d m T) t =
      (pcm y ⟨T, hT, le_rfl⟩).evalA t - (pcm y ⟨T, hT, le_rfl⟩).B + (pcm y ⟨t, ht⟩).B := by
    unfold r2PathAt
    rw [dif_pos ht]
    exact hrec
  rw [e0]
  set x : KSpace d m T := pcm y ⟨T, hT, le_rfl⟩ with hx
  have hyt : pcm y ⟨t, ht⟩ = KSpace.mk (pcm y ⟨t, ht⟩).A₀ (pcm y ⟨t, ht⟩).A' (pcm y ⟨t, ht⟩).B := rfl
  have h1 : inner ℝ (pcm y ⟨T, hT, le_rfl⟩) (s101P m T t α) =
      OscDual.coord x.A₀ α + inner ℝ (s101e m α) (∫ s in Icc (0 : ℝ) t, (x.A' : ℝ → OscDual d m) s
        ∂(volume.restrict (Icc (0 : ℝ) T))) - OscDual.coord x.B α := by
    have hxy : pcm y ⟨T, hT, le_rfl⟩ = x := rfl
    have hinner : inner ℝ x (s101P m T t α) = inner ℝ x.A₀ (s101e m α) +
        inner ℝ x.A' (s101Ind m T t (s101e m α)) + inner ℝ x.B (-(s101e m α)) :=
      s101_inner_mk x.A₀ x.B x.A' _ (s101e m α) (-(s101e m α))
    rw [hxy, hinner, real_inner_comm (s101e m α) x.A₀, s101_inner_e x.A₀, real_inner_comm (s101Ind m T t (s101e m α)) x.A',
      s101_inner_Ind, inner_neg_right, real_inner_comm (s101e m α) x.B, s101_inner_e x.B]
    ring
  have h2 : inner ℝ (pcm y ⟨t, ht⟩) (s101Q m T α) = OscDual.coord (pcm y ⟨t, ht⟩).B α := by
    rw [hyt]
    unfold s101Q
    rw [s101_inner_mk, inner_zero_right, inner_zero_right, zero_add, zero_add]
    rw [real_inner_comm, s101_inner_e]
    rfl
  rw [h1, h2]
  have hint : Integrable (fun s => (x.A' : ℝ → OscDual d m) s) (volume.restrict (Icc (0 : ℝ) t)) :=
    (u9_integrableOn x.A').mono_set (Icc_subset_Icc_right ht.2)
  have e3 : OscDual.coord ((pcm y ⟨T, hT, le_rfl⟩).evalA t) α =
      OscDual.coord x.A₀ α + inner ℝ (s101e m α) (∫ s in Icc (0 : ℝ) t, (x.A' : ℝ → OscDual d m) s) := by
    unfold KSpace.evalA
    rw [min_eq_left ht.2, ← s101_inner_e]
    show inner ℝ (s101e m α) (x.A₀ + ∫ s in Icc (0 : ℝ) t, (x.A' : ℝ → OscDual d m) s) = _
    rw [inner_add_right, s101_inner_e]
  have e4 : (∫ s in Icc (0 : ℝ) t, (x.A' : ℝ → OscDual d m) s ∂(volume.restrict (Icc (0 : ℝ) T))) =
      ∫ s in Icc (0 : ℝ) t, (x.A' : ℝ → OscDual d m) s := by
    rw [Measure.restrict_restrict measurableSet_Icc, Set.inter_eq_left.2 (Icc_subset_Icc_right ht.2)]
  have hadd : ∀ (u v : OscDual d m), OscDual.coord (u + v) α = OscDual.coord u α + OscDual.coord v α :=
    fun u v => rfl
  rw [e4, hadd, s101_coord_sub, e3]

end HRS.MS.CovMeas
