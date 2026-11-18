import HRS.MC.CepE2PropsAux1

/-!
# Packet CEPE2PROPS, auxiliary 2: periodicity, the descent lemma for `C^{1,1}` functions, bounds on the alcove
-/

open Set Filter Topology
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE2Props

open HRS.MC.CepE1 HRS.MC.CepE2

variable {N : ℕ}

theorem cepe2p_per_int {β : Type*} {f : Ch N → β} (h : ∀ z, f (z + cep_diag N) = f z) (z : Ch N) (m : ℤ) :
    f (z + (m : ℝ) • cep_diag N) = f z := by
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have : z + ((i + 1 : ℤ) : ℝ) • cep_diag N = (z + (i : ℝ) • cep_diag N) + cep_diag N := by
      push_cast; rw [add_smul, one_smul]; abel
    push_cast at ih
    rw [this, h, ih]
  | pred i ih =>
    have : z + ((-(i : ℤ) - 1 : ℤ) : ℝ) • cep_diag N + cep_diag N = z + ((-(i : ℤ) : ℤ) : ℝ) • cep_diag N := by
      push_cast; rw [sub_smul, one_smul]; abel
    rw [← h, this, ih]

theorem cepe2p_grad_per {Ψ : Ch N → ℝ} (hΨper : ∀ z, Ψ (z + cep_diag N) = Ψ z) (z : Ch N) :
    gradient Ψ (z + cep_diag N) = gradient Ψ z := by
  have hf : Ψ = fun x => Ψ (x + cep_diag N) := funext fun x => (hΨper x).symm
  unfold gradient
  rw [show fderiv ℝ Ψ z = fderiv ℝ (fun x => Ψ (x + cep_diag N)) z from by rw [← hf],
    fderiv_comp_add_right]

/-- Descent lemma for `C^{1,1}` functions. -/
theorem cepe2p_descent {Ψ : Ch N → ℝ} {L : ℝ≥0} (hΨ : ContDiff ℝ 1 Ψ)
    (hL : LipschitzWith L (gradient Ψ)) (p z : Ch N) :
    Ψ p + inner ℝ (gradient Ψ p) (z - p) - (L : ℝ) / 2 * ‖z - p‖ ^ 2 ≤ Ψ z := by
  set v := z - p with hv
  set φ : ℝ → ℝ := fun s => Ψ (p + s • v) - Ψ p - s * inner ℝ (gradient Ψ p) v +
    (L : ℝ) / 2 * ‖v‖ ^ 2 * s ^ 2 with hφ
  have hder : ∀ s : ℝ, HasDerivAt φ
      (inner ℝ (gradient Ψ (p + s • v)) v - inner ℝ (gradient Ψ p) v + (L : ℝ) * ‖v‖ ^ 2 * s) s := by
    intro s
    have hline : HasDerivAt (fun s : ℝ => p + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add p
    have hΨd : HasFDerivAt Ψ (InnerProductSpace.toDual ℝ (Ch N) (gradient Ψ (p + s • v))) (p + s • v) :=
      ((hΨ.differentiable one_ne_zero) (p + s • v)).hasGradientAt.hasFDerivAt
    have h1 := hΨd.comp_hasDerivAt s hline
    rw [InnerProductSpace.toDual_apply_apply] at h1
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (gradient Ψ p) v) (inner ℝ (gradient Ψ p) v) s := by
      simpa using (hasDerivAt_id s).mul_const (inner ℝ (gradient Ψ p) v)
    have h3 : HasDerivAt (fun s : ℝ => (L : ℝ) / 2 * ‖v‖ ^ 2 * s ^ 2) ((L : ℝ) * ‖v‖ ^ 2 * s) s := by
      have := (hasDerivAt_pow 2 s).const_mul ((L : ℝ) / 2 * ‖v‖ ^ 2)
      convert this using 1
      push_cast; ring
    have := ((h1.sub_const (Ψ p)).sub h2).add h3
    convert this using 1
    funext x
    simp [hφ, Function.comp]
  have hmono : MonotoneOn φ (Ici (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun s _ => (hder s).continuousAt.continuousWithinAt)
      (fun s _ => (hder s).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    rw [interior_Ici] at hs
    have hs0 : 0 < s := hs
    rw [(hder s).deriv]
    have hlip := hL.dist_le_mul (p + s • v) p
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs0] at hlip
    have hcs : -(‖gradient Ψ (p + s • v) - gradient Ψ p‖ * ‖v‖) ≤
        inner ℝ (gradient Ψ (p + s • v) - gradient Ψ p) v := by
      have := abs_real_inner_le_norm (gradient Ψ (p + s • v) - gradient Ψ p) v
      linarith [neg_abs_le (inner ℝ (gradient Ψ (p + s • v) - gradient Ψ p) v)]
    rw [inner_sub_left] at hcs
    have : (L : ℝ) * (s * ‖v‖) * ‖v‖ ≥ ‖gradient Ψ (p + s • v) - gradient Ψ p‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
    nlinarith
  have h01 := hmono (Set.mem_Ici.2 le_rfl) (show (1 : ℝ) ∈ Ici (0 : ℝ) by simp) zero_le_one
  have e0 : φ 0 = 0 := by simp [hφ]
  have e1 : φ 1 = Ψ z - Ψ p - inner ℝ (gradient Ψ p) v + (L : ℝ) / 2 * ‖v‖ ^ 2 := by
    simp only [hφ, one_smul, one_mul, one_pow, mul_one]
    rw [show p + v = z by rw [hv]; abel]
  rw [e0, e1] at h01
  linarith

/-- `Ψ` and `∇Ψ` are bounded on the alcove. -/
theorem cepe2p_bound_alcove [NeZero N] {Ψ : Ch N → ℝ} {L : ℝ≥0} (hΨ : ContDiff ℝ 1 Ψ)
    (hL : LipschitzWith L (gradient Ψ)) (hΨper : ∀ z, Ψ (z + cep_diag N) = Ψ z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ cep_Alcove N, |Ψ p| ≤ B ∧ ‖gradient Ψ p‖ ≤ B := by
  set K : Set (Ch N) := (fun f : Fin N → ℝ => (WithLp.toLp 2 f : Ch N)) ''
    (Set.pi univ fun _ => Icc (0 : ℝ) 2) with hK
  have hKc : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  obtain ⟨C1, hC1⟩ := hKc.exists_bound_of_continuousOn hΨ.continuous.continuousOn
  obtain ⟨C2, hC2⟩ := hKc.exists_bound_of_continuousOn hL.continuous.continuousOn
  refine ⟨max (max C1 C2) 0, le_max_right _ _, fun p hp => ?_⟩
  set m : ℤ := -⌊p 0⌋ with hm
  set q : Ch N := p + (m : ℝ) • cep_diag N with hq
  have hqA : q ∈ cep_Alcove N := (cepe2p_alcove_add_iff p _).2 hp
  have hq0 : q 0 = p 0 - ⌊p 0⌋ := by
    rw [hq, cepe2p_add_smul_diag_apply, hm]; push_cast; ring
  have hq0a : 0 ≤ q 0 := by rw [hq0]; linarith [Int.floor_le (p 0)]
  have hq0b : q 0 < 1 := by rw [hq0]; linarith [Int.lt_floor_add_one (p 0)]
  have hqK : q ∈ K := by
    refine ⟨WithLp.ofLp q, fun k _ => ⟨?_, ?_⟩, rfl⟩
    · rcases eq_or_lt_of_le (Fin.zero_le k) with h | h
      · rw [← h]; exact hq0a
      · exact hq0a.trans (hqA.1 0 k h).le
    · have := hqA.2 0 k
      show q k ≤ 2
      linarith
  have e1 : Ψ q = Ψ p := cepe2p_per_int hΨper p m
  have e2 : gradient Ψ q = gradient Ψ p := cepe2p_per_int (cepe2p_grad_per hΨper) p m
  have b1 := hC1 q hqK
  have b2 := hC2 q hqK
  rw [e1, Real.norm_eq_abs] at b1
  rw [e2] at b2
  exact ⟨b1.trans (le_max_of_le_left (le_max_left _ _)),
    b2.trans (le_max_of_le_left (le_max_right _ _))⟩

end HRS.MC.CepE2Props
