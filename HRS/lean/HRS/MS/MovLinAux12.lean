import HRS.MS.MovLinAux11

/-!
# MOV-LIN, part 3: smoothing of the global flow with arbitrary loss on the scale `OscSpace d r`

Namespace `HRS.MS.MovLin`, helpers `movlin_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.

* `movlin_j_comp`, `movlin_j_inj`: the embeddings `j` compose and are injective.
* `movlin_smooth1`: one step, loss `b < 2 - a`, `0 < t ≤ 1` (from `mov2c_smoothing`).
* `movlin_smooth`: loss `σ - ρ` arbitrary (`ρ ≤ σ` real, also negative levels), `‖z‖ ≤ C t^{-(σ-ρ)/2} ‖x‖`, by splitting
  the time interval in halves and using the semigroup law `mov2d_G_add` and level compatibility `mov2d_G_compat`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1

variable {d : ℕ}

section Smooth

lemma movlin_j_comp {r r1 r2 : ℝ} (h2 : r2 ≤ r) (h1 : r1 ≤ r2) (z : OscSpace d r) :
    mov2d_j h1 (mov2d_j h2 z) = mov2d_j (h1.trans h2) z := by
  apply lp.ext
  funext α
  change OscSpace.coord (mov2d_j h1 (mov2d_j h2 z)) α = OscSpace.coord (mov2d_j (h1.trans h2) z) α
  rw [mov2d_j_coord h1, mov2d_j_coord h2, mov2d_j_coord (h1.trans h2), ← mul_assoc,
    ← Real.rpow_add (oscEv_pos α)]
  congr 2; ring

lemma movlin_j_inj {r r' : ℝ} (h : r' ≤ r) {x y : OscSpace d r} (hxy : mov2d_j h x = mov2d_j h y) : x = y := by
  apply lp.ext
  funext α
  have := congrArg (fun z => OscSpace.coord z α) hxy
  simp only [mov2d_j_coord h] at this
  have hp : oscEigenvalue d α ^ ((r' - r) / 2) ≠ 0 := (Real.rpow_pos_of_pos (oscEv_pos α) _).ne'
  exact mul_left_cancel₀ hp this

variable {s : ℝ} {β q : ℝ} {ρ : Euc d → ℝ}

lemma movlin_G_bound1 (H : Mov2dTh d s β q ρ) (r : ℝ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖mov2d_G H r t‖ ≤ N := by
  obtain ⟨N, hN⟩ := mov2d_G_bound H r 1
  exact ⟨max N 0, le_max_right _ _, fun t ht => (hN t ht).trans (le_max_left _ _)⟩

lemma movlin_smooth1 (H : Mov2dTh d s β q ρ) {ρ' σ : ℝ} (h : ρ' ≤ σ) (hb : σ - ρ' < 2 - movA d s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : OscSpace d ρ', ∃ z : OscSpace d σ,
      mov2d_j h z = mov2d_G H ρ' t x ∧ ‖z‖ ≤ C * t ^ (-((σ - ρ') / 2)) * ‖x‖ := by
  have hT0 : (0 : ℝ) < ((0 : ℕ) : ℝ) + 1 := by norm_num
  obtain ⟨Tn, L⟩ := (mov2d_TT_spec H 0).1 ρ'
  obtain ⟨ha0, ha2⟩ := mov2d_a_bounds d H.hd H.hsd
  obtain ⟨C, hC0, hC⟩ := mov2c_smoothing (mov2d_hyp' H hT0) ha0 ha2 hT0 h hb L
  refine ⟨C, hC0, fun t ht x => ?_⟩
  have ht' : t ∈ Set.Ioc (0 : ℝ) (((0 : ℕ) : ℝ) + 1) := by simpa using ht
  obtain ⟨z, hz1, hz2⟩ := hC t ht' x
  refine ⟨z, ?_, hz2⟩
  have e : mov2d_G H ρ' t = mov2d_TT H 0 ρ' t := mov2d_G_eq H ρ' (n := 0) ⟨ht.1.le, by simpa using ht.2⟩
  rw [e]
  exact hz1

lemma movlin_smooth_aux (H : Mov2dTh d s β q ρ) (n : ℕ) : ∀ {ρ' σ : ℝ} (h : ρ' ≤ σ),
    σ ≤ ρ' + n * ((2 - movA d s) / 2) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : OscSpace d ρ', ∃ z : OscSpace d σ,
      mov2d_j h z = mov2d_G H ρ' t x ∧ ‖z‖ ≤ C * t ^ (-((σ - ρ') / 2)) * ‖x‖ := by
  obtain ⟨ha0, ha2⟩ := mov2d_a_bounds d H.hd H.hsd
  have hθ : 0 < (2 - movA d s) / 2 := by linarith
  induction n with
  | zero =>
    intro ρ' σ h hσ
    have hσ' : σ = ρ' := le_antisymm (by simpa using hσ) h
    subst hσ'
    obtain ⟨N, hN0, hN⟩ := movlin_G_bound1 H σ
    refine ⟨N, hN0, fun t ht x => ⟨mov2d_G H σ t x, ?_, ?_⟩⟩
    · rw [mov2d_j_refl]; rfl
    · simp only [sub_self, zero_div, neg_zero, Real.rpow_zero, mul_one]
      exact ((mov2d_G H σ t).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hN t ⟨ht.1.le, ht.2⟩) (norm_nonneg _))
  | succ n ih =>
    intro ρ' σ h hσ
    by_cases hs1 : σ - ρ' ≤ (2 - movA d s) / 2
    · exact movlin_smooth1 H h (by linarith)
    · push_neg at hs1
      set μ : ℝ := ρ' + (2 - movA d s) / 2 with hμ
      have hρμ : ρ' ≤ μ := by linarith
      have hμσ : μ ≤ σ := by linarith
      obtain ⟨C1, hC10, hC1⟩ := movlin_smooth1 H hρμ (by linarith)
      obtain ⟨C2, hC20, hC2⟩ := ih hμσ (by push_cast at hσ; linarith)
      set E : ℝ := (σ - ρ') / 2 with hE
      have hE0 : 0 ≤ E := by rw [hE]; linarith
      set K : ℝ := ((2 : ℝ)⁻¹) ^ (-E) with hK
      have hK0 : 0 ≤ K := Real.rpow_nonneg (by norm_num) _
      refine ⟨C1 * C2 * K, by positivity, fun t ht x => ?_⟩
      have ht2 : t / 2 ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      obtain ⟨z1, hz11, hz12⟩ := hC1 (t / 2) ht2 x
      obtain ⟨z2, hz21, hz22⟩ := hC2 (t / 2) ht2 z1
      refine ⟨z2, ?_, ?_⟩
      · have e1 : mov2d_G H ρ' t x = mov2d_G H ρ' (t / 2) (mov2d_G H ρ' (t / 2) x) := by
          rw [← mov2d_G_add H ρ' (by linarith [ht.1] : (0 : ℝ) ≤ t / 2) (by linarith [ht.1] : (0 : ℝ) ≤ t / 2)]
          congr 1; ring
        rw [e1, ← hz11, ← mov2d_G_compat H hρμ (by linarith [ht.1] : (0 : ℝ) ≤ t / 2) z1, ← hz21,
          movlin_j_comp hμσ hρμ z2]
      · have hpw : (t / 2) ^ (-((σ - μ) / 2)) * (t / 2) ^ (-((μ - ρ') / 2)) = t ^ (-E) * K := by
          rw [← Real.rpow_add (by linarith [ht.1])]
          have : -((σ - μ) / 2) + -((μ - ρ') / 2) = -E := by rw [hE]; ring
          rw [this, div_eq_mul_inv, Real.mul_rpow ht.1.le (by norm_num)]
        calc ‖z2‖ ≤ C2 * (t / 2) ^ (-((σ - μ) / 2)) * ‖z1‖ := hz22
          _ ≤ C2 * (t / 2) ^ (-((σ - μ) / 2)) * (C1 * (t / 2) ^ (-((μ - ρ') / 2)) * ‖x‖) := by
              exact mul_le_mul_of_nonneg_left hz12 (mul_nonneg hC20 (Real.rpow_nonneg (by linarith [ht.1]) _))
          _ = C1 * C2 * ((t / 2) ^ (-((σ - μ) / 2)) * (t / 2) ^ (-((μ - ρ') / 2))) * ‖x‖ := by ring
          _ = C1 * C2 * K * t ^ (-((σ - ρ') / 2)) * ‖x‖ := by rw [hpw, hE]; ring

/-- **Smoothing with arbitrary loss** on the scale: for `ρ' ≤ σ` real, `0 < t ≤ 1`,
`G_{ρ'}(t) x = j z` with `z ∈ Σ^σ`, `‖z‖ ≤ C t^{-(σ-ρ')/2} ‖x‖`. -/
theorem movlin_smooth (H : Mov2dTh d s β q ρ) {ρ' σ : ℝ} (h : ρ' ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : OscSpace d ρ', ∃ z : OscSpace d σ,
      mov2d_j h z = mov2d_G H ρ' t x ∧ ‖z‖ ≤ C * t ^ (-((σ - ρ') / 2)) * ‖x‖ := by
  obtain ⟨ha0, ha2⟩ := mov2d_a_bounds d H.hd H.hsd
  have hθ : 0 < (2 - movA d s) / 2 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_ge ((σ - ρ') / ((2 - movA d s) / 2))
  refine movlin_smooth_aux H n h ?_
  have := (div_le_iff₀ hθ).1 hn
  linarith

end Smooth

end HRS.MS.MovLin
