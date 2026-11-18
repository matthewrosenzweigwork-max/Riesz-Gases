import HRS.MC.CepH2Aux1

/-!
# CEPH2, helper 2: integrals over the cell of diagonally periodic functions
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

theorem cep_diag_ne_zero [NeZero N] : cep_diag N ≠ 0 := by
  intro h
  have := congrArg (fun v : Ch N => v 0) h
  simp [cep_diag_apply] at this

/-- `m ↦ m d` identifies `ℤ` with the lattice. -/
def h2_latEquiv (N : ℕ) [NeZero N] : ℤ ≃ ↥(h2_lat N) :=
  Equiv.ofBijective (fun m : ℤ => (⟨m • cep_diag N, AddSubgroup.zsmul_mem_zmultiples _ _⟩ : ↥(h2_lat N)))
    ⟨fun m m' h => by
      have h0 := congrArg (fun g : ↥(h2_lat N) => (g : Ch N) 0) h
      simpa [cep_diag_apply] using h0,
     fun g => by
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 g.2
      exact ⟨k, Subtype.ext hk⟩⟩

theorem h2_latEquiv_apply [NeZero N] (m : ℤ) : ((h2_latEquiv N m : ↥(h2_lat N)) : Ch N) = m • cep_diag N := rfl

theorem h2_zsmul_diag (m : ℤ) : m • cep_diag N = (m : ℝ) • cep_diag N := by
  simp [Int.cast_smul_eq_zsmul]

/-- Unfolding: `∫_E F = ∫_cell ∑_m F(· + m d)`. -/
theorem h2_lintegral_unfold [NeZero N] {F : Ch N → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ x in cep_cell N, ∑' m : ℤ, F (x + (m : ℝ) • cep_diag N) := by
  rw [h2_isFD.lintegral_eq_tsum'']
  rw [← (h2_latEquiv N).tsum_eq]
  rw [lintegral_tsum]
  · refine tsum_congr fun m => ?_
    congr 1
    funext x
    show F ((h2_latEquiv N m : Ch N) + x) = F (x + (m : ℝ) • cep_diag N)
    rw [h2_latEquiv_apply, h2_zsmul_diag, add_comm]
  · intro m
    exact (hF.comp (measurable_add_const _)).aemeasurable

/-- Periodic functions are invariant under the lattice. -/
theorem h2_periodic_zsmul {f : Ch N → ℝ} (hper : ∀ x, f (x + cep_diag N) = f x) (m : ℤ) (x : Ch N) :
    f (x + m • cep_diag N) = f x := by
  induction m using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    have : x + ((n : ℤ) + 1) • cep_diag N = (x + (n : ℤ) • cep_diag N) + cep_diag N := by
      rw [add_smul, one_smul, add_assoc]
    rw [this, hper, ih]
  | pred n ih =>
    have : x + (-(n : ℤ) - 1) • cep_diag N + cep_diag N = x + (-(n : ℤ)) • cep_diag N := by
      rw [sub_smul, one_smul]; abel
    have h2 := hper (x + (-(n : ℤ) - 1) • cep_diag N)
    rw [this, ih] at h2
    exact h2.symm

theorem h2_periodic_real {f : Ch N → ℝ} (hper : ∀ x, f (x + cep_diag N) = f x) (m : ℝ) (hm : ∃ k : ℤ, (k : ℝ) = m)
    (x : Ch N) : f (x + m • cep_diag N) = f x := by
  obtain ⟨k, rfl⟩ := hm
  rw [← h2_zsmul_diag]; exact h2_periodic_zsmul hper k x

/-- Translation invariance of cell integrals of periodic functions. -/
theorem h2_setIntegral_translate [NeZero N] {f : Ch N → ℝ} (hper : ∀ x, f (x + cep_diag N) = f x) (a : Ch N) :
    ∫ x in cep_cell N, f (x + a) = ∫ x in cep_cell N, f x := by
  have hFD2 : IsAddFundamentalDomain (h2_lat N) (a +ᵥ cep_cell N) volume := h2_isFD.vadd_of_comm a
  have hinv : ∀ (g : ↥(h2_lat N)) (x : Ch N), f (g +ᵥ x) = f x := by
    intro g x
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 g.2
    change f ((g : Ch N) + x) = f x
    rw [← hk, add_comm]
    exact h2_periodic_zsmul hper k x
  have h1 := h2_isFD.setIntegral_eq hFD2 hinv
  rw [h1]
  have h2 : (a +ᵥ cep_cell N) = (fun x => a + x) '' cep_cell N := by
    rw [← Set.image_vadd]; rfl
  rw [h2]
  have := (measurePreserving_add_left (volume : Measure (Ch N)) a).setIntegral_image_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding f (cep_cell N)
  refine Eq.trans ?_ this.symm
  refine setIntegral_congr_fun h2_cell_measurable fun x _ => ?_
  show f (x + a) = f (a + x)
  rw [add_comm]

theorem h2_reduce_mem_cell [NeZero N] (x : Ch N) : cep_reduce x ∈ cep_cell N := by
  simp only [cep_reduce, cep_cell, Set.mem_ofPred_eq, PiLp.sub_apply, PiLp.smul_apply, cep_diag_apply, smul_eq_mul,
    mul_one]
  constructor
  · linarith [Int.floor_le (x 0)]
  · linarith [Int.lt_floor_add_one (x 0)]

theorem h2_reduce_eq [NeZero N] (x : Ch N) : cep_reduce x = x + ((-⌊x 0⌋ : ℤ) : ℝ) • cep_diag N := by
  simp [cep_reduce, sub_eq_add_neg, neg_smul]

theorem h2_perp_reduce [NeZero N] (x : Ch N) : h2_perp (cep_reduce x) = h2_perp x := by
  rw [h2_reduce_eq, h2_perp_add_diag]

theorem h2_periodic_reduce [NeZero N] {g : Ch N → ℝ} (hper : ∀ x, g (x + cep_diag N) = g x) (x : Ch N) :
    g (cep_reduce x) = g x := by
  rw [h2_reduce_eq, ← h2_zsmul_diag]; exact h2_periodic_zsmul hper _ x

theorem h2_tube_subset [NeZero N] (R : ℝ) :
    cep_cell N ∩ {x | ‖h2_perp x‖ ≤ R} ⊆ Metric.closedBall (0 : Ch N) (R + Real.sqrt N * (1 + R)) := by
  intro x ⟨hx, hxR⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (h2_cell_norm_le hx).trans ?_
  have : ‖h2_perp x‖ ≤ R := hxR
  have hs := Real.sqrt_nonneg (N : ℝ)
  nlinarith

theorem h2_volume_tube_lt_top [NeZero N] (R : ℝ) :
    volume (cep_cell N ∩ {x | ‖h2_perp x‖ ≤ R}) < ⊤ :=
  (measure_mono (h2_tube_subset R)).trans_lt measure_closedBall_lt_top

/-- A continuous periodic function is bounded on every tube `‖P⊥ x‖ ≤ R`. -/
theorem h2_bdd_tube [NeZero N] {G : Type*} [NormedAddCommGroup G] {g : Ch N → G} (hg : Continuous g)
    (hper : ∀ x, g (x + cep_diag N) = g x) (R : ℝ) : ∃ C : ℝ, ∀ x, ‖h2_perp x‖ ≤ R → ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Ch N) (R + Real.sqrt N * (1 + R))).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨C, fun x hx => ?_⟩
  have h1 : cep_reduce x ∈ Metric.closedBall (0 : Ch N) (R + Real.sqrt N * (1 + R)) :=
    h2_tube_subset R ⟨h2_reduce_mem_cell x, by simpa [h2_perp_reduce] using hx⟩
  have h2 : g (cep_reduce x) = g x := by
    rw [h2_reduce_eq, ← h2_zsmul_diag]
    have hz : ∀ (m : ℤ) (y : Ch N), g (y + m • cep_diag N) = g y := by
      intro m
      induction m using Int.induction_on with
      | zero => intro y; simp
      | succ n ih => intro y; rw [add_smul, one_smul, ← add_assoc, hper, ih]
      | pred n ih =>
        intro y
        have h3 := hper (y + (-(n : ℤ) - 1) • cep_diag N)
        have : y + (-(n : ℤ) - 1) • cep_diag N + cep_diag N = y + (-(n : ℤ)) • cep_diag N := by
          rw [sub_smul, one_smul]; abel
        rw [this, ih] at h3
        exact h3.symm
    exact hz _ x
  rw [← h2]; exact hC _ h1

end HRS.MC.CepH2
