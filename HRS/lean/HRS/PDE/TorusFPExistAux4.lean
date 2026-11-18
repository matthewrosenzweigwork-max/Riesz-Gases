import HRS.PDE.TorusFPExistAux3

/-!
# D1 existence, helper 4: the solution operator on smooth data
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

section SolOp

variable (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)

/-- The chosen classical backward solution with terminal time `T` and smooth terminal datum `ψ`. -/
def d1_sol (T : ℝ) (ψ : Torus n → ℝ) : ℝ → Torus n → ℝ :=
  open Classical in
  if h : 0 < T ∧ Torus.IsSmooth ψ then
    Classical.choose (d1_backward_classical hn hκ hU h.1 h.2)
  else fun _ _ => 0

theorem d1_sol_spec {T : ℝ} (hT : 0 < T) {ψ : Torus n → ℝ} (hψ : Torus.IsSmooth ψ) :
    D1BackwardSolution κ (d1_gradDrift U) T ψ (d1_sol hn hκ hU T ψ) := by
  unfold d1_sol
  rw [dif_pos ⟨hT, hψ⟩]
  exact Classical.choose_spec (d1_backward_classical hn hκ hU hT hψ)

/-- The solution operator `ψ ↦ U^{0,t} ψ` on smooth data. -/
def d1_P (t : ℝ) (ψ : Torus n → ℝ) (x : Torus n) : ℝ :=
  open Classical in
  if 0 < t then d1_sol hn hκ hU t ψ 0 x else ψ x

theorem d1_P_eq {T : ℝ} (hT : 0 < T) {ψ : Torus n → ℝ} (hψ : Torus.IsSmooth ψ)
    {f : ℝ → Torus n → ℝ} (hf : D1BackwardSolution κ (d1_gradDrift U) T ψ f) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) (x : Torus n) : d1_P hn hκ hU t ψ x = f (T - t) x := by
  unfold d1_P
  rcases ht.1.eq_or_lt with rfl | ht0
  · simp [hf.terminal]
  · rw [if_pos ht0]
    have hs := hf.shift ht0 ht.2
    have h2 := d1_sol_spec hn hκ hU ht0 hψ
    have := d1_backward_unique hκ ht0 h2 hs 0 ⟨le_rfl, ht0.le⟩ x
    rw [this]
    simp


theorem d1_P_lincomb {t : ℝ} (ht : 0 ≤ t) {ψ₁ ψ₂ : Torus n → ℝ} (h₁ : Torus.IsSmooth ψ₁)
    (h₂ : Torus.IsSmooth ψ₂) (a c : ℝ) (x : Torus n) :
    d1_P hn hκ hU t (fun x => a * ψ₁ x + c * ψ₂ x) x =
      a * d1_P hn hκ hU t ψ₁ x + c * d1_P hn hκ hU t ψ₂ x := by
  have hT : 0 < t + 1 := by linarith
  have htT : t ∈ Set.Icc 0 (t + 1) := ⟨ht, by linarith⟩
  have s1 := d1_sol_spec hn hκ hU hT h₁
  have s2 := d1_sol_spec hn hκ hU hT h₂
  have s3 := s1.lincomb s2 a c
  rw [d1_P_eq hn hκ hU hT (d1_isSmooth_comb a c h₁ h₂) s3 htT,
    d1_P_eq hn hκ hU hT h₁ s1 htT, d1_P_eq hn hκ hU hT h₂ s2 htT]

theorem d1_P_const {t : ℝ} (ht : 0 ≤ t) (c : ℝ) (x : Torus n) :
    d1_P hn hκ hU t (fun _ => c) x = c := by
  have hT : 0 < t + 1 := by linarith
  have htT : t ∈ Set.Icc 0 (t + 1) := ⟨ht, by linarith⟩
  rw [d1_P_eq hn hκ hU hT (d1_isSmooth_const c)
    (D1BackwardSolution.const κ (d1_gradDrift U) (t + 1) c) htT]

theorem d1_P_abs_le {t : ℝ} (ht : 0 ≤ t) {ψ₁ ψ₂ : Torus n → ℝ} (h₁ : Torus.IsSmooth ψ₁)
    (h₂ : Torus.IsSmooth ψ₂) {c : ℝ} (hc : ∀ x, |ψ₁ x - ψ₂ x| ≤ c) (x : Torus n) :
    |d1_P hn hκ hU t ψ₁ x - d1_P hn hκ hU t ψ₂ x| ≤ c := by
  have hT : 0 < t + 1 := by linarith
  have htT : t ∈ Set.Icc 0 (t + 1) := ⟨ht, by linarith⟩
  have s1 := d1_sol_spec hn hκ hU hT h₁
  have s2 := d1_sol_spec hn hκ hU hT h₂
  rw [d1_P_eq hn hκ hU hT h₁ s1 htT, d1_P_eq hn hκ hU hT h₂ s2 htT]
  exact d1_backward_abs_le hκ hT s1 s2 hc _ ⟨by linarith [htT.2], by linarith [htT.1]⟩ x

theorem d1_P_nonneg {t : ℝ} (ht : 0 ≤ t) {ψ : Torus n → ℝ} (hψ : Torus.IsSmooth ψ)
    (h0 : ∀ x, 0 ≤ ψ x) (x : Torus n) : 0 ≤ d1_P hn hκ hU t ψ x := by
  have hT : 0 < t + 1 := by linarith
  have htT : t ∈ Set.Icc 0 (t + 1) := ⟨ht, by linarith⟩
  have s1 := d1_sol_spec hn hκ hU hT hψ
  rw [d1_P_eq hn hκ hU hT hψ s1 htT]
  exact d1_backward_nonneg hκ hT s1 h0 _ ⟨by linarith [htT.2], by linarith [htT.1]⟩ x

theorem d1_P_continuous {t : ℝ} (ht : 0 ≤ t) {ψ : Torus n → ℝ} (hψ : Torus.IsSmooth ψ) :
    Continuous (d1_P hn hκ hU t ψ) := by
  have hT : 0 < t + 1 := by linarith
  have htT : t ∈ Set.Icc 0 (t + 1) := ⟨ht, by linarith⟩
  have s1 := d1_sol_spec hn hκ hU hT hψ
  have hmem : (t + 1) - t ∈ Set.Icc (0 : ℝ) (t + 1) := ⟨by linarith, by linarith⟩
  have hc : Continuous fun x : Torus n => d1_sol hn hκ hU (t + 1) ψ ((t + 1) - t) x :=
    s1.continuous_joint.comp (Continuous.prodMk continuous_const continuous_id : Continuous fun x : Torus n =>
      ((⟨(t + 1) - t, hmem⟩ : Set.Icc (0 : ℝ) (t + 1)), x))
  refine hc.congr fun x => ?_
  exact (d1_P_eq hn hκ hU hT hψ s1 htT x).symm

end SolOp

end HRS
