import HRS.Equilibrium.Parametrix.Packets
import HRS.Equilibrium.Parametrix.PX5AuxA

/-!
# Prop 4.13 parametrix, packet PX5: the size bounds of `ψ^loc`

`Px5Bnds`: the three pointwise bounds of `PsiSize` (and `C²` smoothness off the diagonal), closed
under sums; every conormal class with the weight condition `Px5W` satisfies them; and `ψ^loc_n`
satisfies them with constant `C |f|_{m+2}`.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

structure Px5Bnds (s K : ℝ) (ψ : Torus d → Torus d → ℝ) : Prop where
  smooth2 : ContDiffOn ℝ 2 (lift2 ψ) (offDiag d)
  size : ∀ x y, x ≠ y → |ψ x y| ≤ K * px5T s 0 (rTrunc x y)
  grad : ∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
    K * px5T s 1 (rTrunc (Torus.mk p.1) (Torus.mk p.2))
  hess : ∀ p ∈ offDiag d, ‖iteratedFDeriv ℝ 2 (lift2 ψ) p‖ ≤
    K * px5T s 2 (rTrunc (Torus.mk p.1) (Torus.mk p.2))

theorem px5_rTrunc_nonneg (x y : Torus d) : 0 ≤ rTrunc x y :=
  le_min zero_le_one (Real.sqrt_nonneg _)

theorem Px5Bnds.zero (s : ℝ) : Px5Bnds s 0 (fun _ _ : Torus d => (0 : ℝ)) where
  smooth2 := by
    have : lift2 (fun _ _ : Torus d => (0 : ℝ)) = fun _ => 0 := rfl
    rw [this]; exact contDiffOn_const
  size := by intro x y _; simp
  grad := by
    intro p _
    have : lift2 (fun _ _ : Torus d => (0 : ℝ)) = fun _ => 0 := rfl
    rw [this]; simp
  hess := by
    intro p _
    have : lift2 (fun _ _ : Torus d => (0 : ℝ)) = fun _ => 0 := rfl
    rw [this]; simp [iteratedFDeriv_const_of_ne]

theorem Px5Bnds.add {K₁ K₂ : ℝ} {ψ₁ ψ₂ : Torus d → Torus d → ℝ} (h₁ : Px5Bnds s K₁ ψ₁)
    (h₂ : Px5Bnds s K₂ ψ₂) : Px5Bnds s (K₁ + K₂) (fun x y => ψ₁ x y + ψ₂ x y) := by
  have hsum : lift2 (fun x y => ψ₁ x y + ψ₂ x y) = lift2 ψ₁ + lift2 ψ₂ := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsum]; exact h₁.smooth2.add h₂.smooth2
  · intro x y hxy
    have e := add_mul K₁ K₂ (px5T s 0 (rTrunc x y))
    calc |ψ₁ x y + ψ₂ x y| ≤ |ψ₁ x y| + |ψ₂ x y| := abs_add_le _ _
      _ ≤ K₁ * px5T s 0 (rTrunc x y) + K₂ * px5T s 0 (rTrunc x y) :=
          add_le_add (h₁.size x y hxy) (h₂.size x y hxy)
      _ = _ := e.symm
  · intro p hp
    have hq : (offDiag d) ∈ 𝓝 p := isOpen_offDiag.mem_nhds hp
    have hd1 : DifferentiableAt ℝ (lift2 ψ₁) p :=
      (h₁.smooth2.contDiffAt hq).differentiableAt (by simp)
    have hd2 : DifferentiableAt ℝ (lift2 ψ₂) p :=
      (h₂.smooth2.contDiffAt hq).differentiableAt (by simp)
    rw [hsum, fderiv_add hd1 hd2]
    calc ‖fderiv ℝ (lift2 ψ₁) p + fderiv ℝ (lift2 ψ₂) p‖
        ≤ ‖fderiv ℝ (lift2 ψ₁) p‖ + ‖fderiv ℝ (lift2 ψ₂) p‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (h₁.grad p hp) (h₂.grad p hp)
      _ = _ := (add_mul _ _ _).symm
  · intro p hp
    have hq : (offDiag d) ∈ 𝓝 p := isOpen_offDiag.mem_nhds hp
    have hc1 : ContDiffAt ℝ 2 (lift2 ψ₁) p := h₁.smooth2.contDiffAt hq
    have hc2 : ContDiffAt ℝ 2 (lift2 ψ₂) p := h₂.smooth2.contDiffAt hq
    rw [hsum, iteratedFDeriv_add_apply hc1 hc2]
    calc ‖iteratedFDeriv ℝ 2 (lift2 ψ₁) p + iteratedFDeriv ℝ 2 (lift2 ψ₂) p‖
        ≤ ‖iteratedFDeriv ℝ 2 (lift2 ψ₁) p‖ + ‖iteratedFDeriv ℝ 2 (lift2 ψ₂) p‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (h₁.hess p hp) (h₂.hess p hp)
      _ = _ := (add_mul _ _ _).symm

theorem Px5Bnds.of_conormal {τ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B Cw : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : ConormalL τ b m B F) (hm : 2 ≤ m) (hB : 0 ≤ B) (hCw0 : 0 ≤ Cw) (hCw : Px5W s τ b Cw) :
    Px5Bnds s (16 * (B * (1 + Cw))) F := by
  have hBC : 0 ≤ B * (1 + Cw) := by positivity
  have hdb := fun (k : ℕ) (hk : k ≤ 2) p hp => px5_deriv_bound hF hB hCw0 hCw (k := k) hk (by omega) p hp
  refine ⟨hF.smooth.of_le (by exact_mod_cast hm), ?_, ?_, ?_⟩
  · intro x y hxy
    have hp : ((Torus.rep x, Torus.rep y) : Euc d × Euc d) ∈ offDiag d := by
      show Torus.mk (Torus.rep x) ≠ Torus.mk (Torus.rep y)
      rw [Torus.mk_rep, Torus.mk_rep]; exact hxy
    have h := hdb 0 (by norm_num) _ hp
    rw [norm_iteratedFDeriv_zero] at h
    simp only [Torus.mk_rep] at h
    have e : lift2 F (Torus.rep x, Torus.rep y) = F x y := by simp [lift2, Torus.mk_rep]
    rw [e, Real.norm_eq_abs] at h
    have hT := px5T_ge_one s 0 (px5_rTrunc_nonneg x y)
    calc |F x y| ≤ 4 ^ 0 * (B * (1 + Cw)) * px5T s 0 (rTrunc x y) := h
      _ ≤ 16 * (B * (1 + Cw)) * px5T s 0 (rTrunc x y) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          nlinarith
  · intro p hp
    have h := hdb 1 (by norm_num) p hp
    have e : ‖fderiv ℝ (lift2 F) p‖ = ‖iteratedFDeriv ℝ 1 (lift2 F) p‖ := by
      have := (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := lift2 F) (x := p) (n := 0))
      rw [norm_iteratedFDeriv_zero] at this
      exact this
    rw [e]
    have hT := px5T_ge_one s 1 (px5_rTrunc_nonneg (Torus.mk p.1) (Torus.mk p.2))
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    nlinarith
  · intro p hp
    have h := hdb 2 le_rfl p hp
    have hT := px5T_ge_one s 2 (px5_rTrunc_nonneg (Torus.mk p.1) (Torus.mk p.2))
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    nlinarith

theorem Px5Bnds.psiSize {K : ℝ} {ψ : Torus d → Torus d → ℝ} (h : Px5Bnds s K ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) : PsiSize s K ψ :=
  ⟨hsm, h.size, h.grad, h.hess⟩

/-- `ψ^loc_n` satisfies the bounds with constant `C |f|_{m+2}` (`2 n ≤ m`). -/
theorem px5_psi_bnds (H : ParxHyp d s V β ρ) (m : ℕ) :
    ∀ n : ℕ, 2 * n ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Px5Bnds s (C * posSeminorm (m + 2) f) (parxPsi d s V β ρ f n) := by
  have hs0 : 0 < s := by
    have h2 : (2 : ℝ) ≤ d := by exact_mod_cast H.two_le
    rw [H.crit]; linarith
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨0, le_rfl, fun f hf => ?_⟩
    have e : parxPsi d s V β ρ f 0 = fun _ _ => 0 := by
      funext x y; simp [parxPsi]
    rw [e, zero_mul]
    exact Px5Bnds.zero s
  | succ n ih =>
    intro hn
    obtain ⟨C1, hC1, h1⟩ := ih (by omega)
    obtain ⟨C2, hC2, h2⟩ := parxN_conormal H m n (by omega)
    obtain ⟨Cw, hCw0, hCw, hmn⟩ : ∃ Cw : ℝ, 0 ≤ Cw ∧
        Px5W s (s - (n : ℝ) / 2 - 2)
          (fun c => 0 + if s - (n : ℝ) / 2 - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0) Cw ∧ True := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        exact ⟨1, zero_le_one, px5W_sharp hs0, trivial⟩
      · obtain ⟨Cw, hCw0, hCw⟩ := px5W_coarse (s := s) (τ := s - (n : ℝ) / 2 - 2)
          (by
            have : (1 : ℝ) ≤ n := by exact_mod_cast hpos
            linarith)
          (fun c => 0 + if s - (n : ℝ) / 2 - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0)
          (fun c => by split_ifs <;> simp)
        exact ⟨Cw, hCw0, hCw, trivial⟩
    refine ⟨C1 + 16 * (C2 * (1 + Cw)), by positivity, fun f hf => ?_⟩
    have hB0 : 0 ≤ C2 * posSeminorm (m + 2) f := mul_nonneg hC2 (posSeminorm_nonneg' _ _)
    have hN := Px5Bnds.of_conormal (h2 f hf) (by omega) hB0 hCw0 hCw
    have hsum := (h1 f hf).add hN
    have e : parxPsi d s V β ρ f (n + 1) = fun x y => parxPsi d s V β ρ f n x y +
        newtonOp d β ρ (parxR d s V β ρ f n) x y := by
      funext x y; simp [parxPsi, Finset.sum_range_succ]
    rw [e]
    have e2 : C1 * posSeminorm (m + 2) f + 16 * (C2 * posSeminorm (m + 2) f * (1 + Cw)) =
        (C1 + 16 * (C2 * (1 + Cw))) * posSeminorm (m + 2) f := by ring
    rw [← e2]
    exact hsum

end HRS.Parx

end
