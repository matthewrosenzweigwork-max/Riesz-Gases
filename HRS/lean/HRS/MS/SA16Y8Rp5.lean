import HRS.MS.SA16Y8Rp4

/-!
# S.A.16 (SA16Y8) Rp5: point-evaluation functionals of the `C²` representative (classical clause, K4, part 1)

`sa16y8_eval0/1/2`: for `x, v, w` there is a bounded linear functional `ℓ` on `W^{m,p}` with `ℓ z = u x`, `fderiv u x v`, `D2 u x v w` for every `C²`
representative `u` of `z` (so that the weak continuity of `τ ↦ F τ` applies to the jets of the representative).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16 HRS.Whole.AppendixA.Phase2SA16R
open Phase2SA16Transfer Phase2SA16Evolution

section Rp5
variable {d : ℕ}

lemma sa16y8_add_fd (a b : ccSub d) (x : Euc d) :
    fderiv ℝ (a + b).1 x = fderiv ℝ a.1 x + fderiv ℝ b.1 x := by
  have : (a + b).1 = fun y => a.1 y + b.1 y := rfl
  rw [this]
  exact fderiv_add ((a.2.1.differentiable (by simp)) x) ((b.2.1.differentiable (by simp)) x)

lemma sa16y8_smul_fd (c : ℝ) (a : ccSub d) (x : Euc d) :
    fderiv ℝ (c • a).1 x = c • fderiv ℝ a.1 x := by
  have : (c • a).1 = fun y => c • a.1 y := rfl
  rw [this]
  exact fderiv_const_smul ((a.2.1.differentiable (by simp)) x) c

lemma sa16y8_add_D2 (a b : ccSub d) (x : Euc d) :
    sa16y8_D2 (a + b).1 x = sa16y8_D2 a.1 x + sa16y8_D2 b.1 x := by
  have h1 : fderiv ℝ (a + b).1 = fun y => fderiv ℝ a.1 y + fderiv ℝ b.1 y := funext (sa16y8_add_fd a b)
  have hda : Differentiable ℝ (fderiv ℝ a.1) :=
    ((a.2.1.fderiv_right (m := ∞) (by simp)).differentiable (by simp))
  have hdb : Differentiable ℝ (fderiv ℝ b.1) :=
    ((b.2.1.fderiv_right (m := ∞) (by simp)).differentiable (by simp))
  unfold sa16y8_D2
  rw [h1]
  exact fderiv_add (hda x) (hdb x)

lemma sa16y8_smul_D2 (c : ℝ) (a : ccSub d) (x : Euc d) :
    sa16y8_D2 (c • a).1 x = c • sa16y8_D2 a.1 x := by
  have h1 : fderiv ℝ (c • a).1 = fun y => c • fderiv ℝ a.1 y := funext (sa16y8_smul_fd c a)
  have hda : Differentiable ℝ (fderiv ℝ a.1) :=
    ((a.2.1.fderiv_right (m := ∞) (by simp)).differentiable (by simp))
  unfold sa16y8_D2
  rw [h1]
  exact fderiv_const_smul (hda x) c

/-- a continuous representative is unique -/
lemma sa16y8_rep_unique {m : ℕ} {p : ℝ} [Fact (2 ≤ p)] {z : WmpSpace d m p} {u u' : Euc d → ℝ}
    (hu : Continuous u) (hu' : Continuous u') (h : wrep d m p z =ᵐ[volume] u) (h' : wrep d m p z =ᵐ[volume] u') :
    u = u' :=
  (hu.ae_eq_iff_eq volume hu').1 (h.symm.trans h')

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
theorem sa16y8_eval (d m : ℕ) (hd : 1 ≤ d) (p : ℝ) [Fact (2 ≤ p)] (hmp : 2 + (d : ℝ) / p < m) (x v w : Euc d) :
    (∃ ℓ : WmpSpace d m p →L[ℝ] ℝ, ∀ (z : WmpSpace d m p) (u : Euc d → ℝ), ContDiff ℝ 2 u →
      wrep d m p z =ᵐ[volume] u → ℓ z = u x) ∧
    (∃ ℓ : WmpSpace d m p →L[ℝ] ℝ, ∀ (z : WmpSpace d m p) (u : Euc d → ℝ), ContDiff ℝ 2 u →
      wrep d m p z =ᵐ[volume] u → ℓ z = fderiv ℝ u x v) ∧
    (∃ ℓ : WmpSpace d m p →L[ℝ] ℝ, ∀ (z : WmpSpace d m p) (u : Euc d → ℝ), ContDiff ℝ 2 u →
      wrep d m p z =ᵐ[volume] u → ℓ z = sa16y8_D2 u x v w) := by
  obtain ⟨C, α, hC, hα, hB⟩ := sa16y8_bounds d m hd p hmp
  -- common: the representative along a sequence
  have hseq : ∀ z : WmpSpace d m p, ∃ φ : ℕ → ccSub d,
      Tendsto (fun n => sa16r_Jcc d m p (φ n)) atTop (𝓝 z) := by
    intro z
    obtain ⟨xs, hxr, hxt⟩ := mem_closure_iff_seq_limit.1 ((sa16r_Jcc_dense d m p) z)
    choose φ hφ using hxr
    refine ⟨φ, ?_⟩
    have e : (fun n => sa16r_Jcc d m p (φ n)) = xs := funext hφ
    rw [e]; exact hxt
  refine ⟨?_, ?_, ?_⟩
  · -- order 0
    let A : ccSub d →ₗ[ℝ] ℝ :=
      { toFun := fun φ => φ.1 x
        map_add' := fun a b => rfl
        map_smul' := fun c a => rfl }
    obtain ⟨T, -, hT, -⟩ := sa16r_ext_abstract (sa16r_Jcc d m p) (sa16r_Jcc_dense d m p) A hC.le
      (fun φ => by simpa [A, Real.norm_eq_abs] using (hB φ).1 x)
    refine ⟨T, fun z u hu hae => ?_⟩
    obtain ⟨φ, hJn⟩ := hseq z
    obtain ⟨u₁, h1, h2, -, -, -, -, hp0, -, -⟩ := sa16y8_rep_seq d m p hC hα hB z φ hJn
    have hu1 : u₁ = u := sa16y8_rep_unique h1.continuous hu.continuous h2 hae
    have hlim : Tendsto (fun n => T (sa16r_Jcc d m p (φ n))) atTop (𝓝 (T z)) := (T.continuous.tendsto z).comp hJn
    have hlim2 : Tendsto (fun n => T (sa16r_Jcc d m p (φ n))) atTop (𝓝 (u₁ x)) := by
      refine (hp0 x).congr (fun n => ?_)
      rw [hT]
      rfl
    rw [← hu1]
    exact tendsto_nhds_unique hlim hlim2
  · -- order 1
    let A : ccSub d →ₗ[ℝ] ℝ :=
      { toFun := fun φ => fderiv ℝ φ.1 x v
        map_add' := fun a b => by
          show fderiv ℝ (a + b).1 x v = fderiv ℝ a.1 x v + fderiv ℝ b.1 x v
          rw [sa16y8_add_fd]; rfl
        map_smul' := fun c a => by
          show fderiv ℝ (c • a).1 x v = c * fderiv ℝ a.1 x v
          rw [sa16y8_smul_fd]; rfl }
    obtain ⟨T, -, hT, -⟩ := sa16r_ext_abstract (sa16r_Jcc d m p) (sa16r_Jcc_dense d m p) A (c := C * ‖v‖)
      (by positivity)
      (fun φ => by
        calc ‖A φ‖ = ‖fderiv ℝ φ.1 x v‖ := rfl
          _ ≤ ‖fderiv ℝ φ.1 x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ (C * ‖sa16r_Jcc d m p φ‖) * ‖v‖ := mul_le_mul_of_nonneg_right ((hB φ).2.1 x) (norm_nonneg _)
          _ = C * ‖v‖ * ‖sa16r_Jcc d m p φ‖ := by ring)
    refine ⟨T, fun z u hu hae => ?_⟩
    obtain ⟨φ, hJn⟩ := hseq z
    obtain ⟨u₁, h1, h2, -, -, -, -, -, hp1, -⟩ := sa16y8_rep_seq d m p hC hα hB z φ hJn
    have hu1 : u₁ = u := sa16y8_rep_unique h1.continuous hu.continuous h2 hae
    have hlim : Tendsto (fun n => T (sa16r_Jcc d m p (φ n))) atTop (𝓝 (T z)) := (T.continuous.tendsto z).comp hJn
    have hc : Continuous (fun L : Euc d →L[ℝ] ℝ => L v) := (ContinuousLinearMap.apply ℝ ℝ v).continuous
    have hlim2 : Tendsto (fun n => T (sa16r_Jcc d m p (φ n))) atTop (𝓝 (fderiv ℝ u₁ x v)) := by
      refine ((hc.tendsto _).comp (hp1 x)).congr (fun n => ?_)
      simp only [Function.comp_apply]
      rw [hT]
      rfl
    rw [← hu1]
    exact tendsto_nhds_unique hlim hlim2
  · -- order 2
    let A : ccSub d →ₗ[ℝ] ℝ :=
      { toFun := fun φ => sa16y8_D2 φ.1 x v w
        map_add' := fun a b => by
          show sa16y8_D2 (a + b).1 x v w = sa16y8_D2 a.1 x v w + sa16y8_D2 b.1 x v w
          rw [sa16y8_add_D2]; rfl
        map_smul' := fun c a => by
          show sa16y8_D2 (c • a).1 x v w = c * sa16y8_D2 a.1 x v w
          rw [sa16y8_smul_D2]; rfl }
    obtain ⟨T, -, hT, -⟩ := sa16r_ext_abstract (sa16r_Jcc d m p) (sa16r_Jcc_dense d m p) A (c := C * ‖v‖ * ‖w‖)
      (by positivity)
      (fun φ => by
        calc ‖A φ‖ = ‖sa16y8_D2 φ.1 x v w‖ := rfl
          _ ≤ ‖sa16y8_D2 φ.1 x v‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ (‖sa16y8_D2 φ.1 x‖ * ‖v‖) * ‖w‖ := by
              gcongr; exact ContinuousLinearMap.le_opNorm _ _
          _ ≤ ((C * ‖sa16r_Jcc d m p φ‖) * ‖v‖) * ‖w‖ := by
              gcongr; exact (hB φ).2.2.1 x
          _ = C * ‖v‖ * ‖w‖ * ‖sa16r_Jcc d m p φ‖ := by ring)
    refine ⟨T, fun z u hu hae => ?_⟩
    obtain ⟨φ, hJn⟩ := hseq z
    obtain ⟨u₁, h1, h2, -, -, -, -, -, -, hp2⟩ := sa16y8_rep_seq d m p hC hα hB z φ hJn
    have hu1 : u₁ = u := sa16y8_rep_unique h1.continuous hu.continuous h2 hae
    have hlim : Tendsto (fun n => T (sa16r_Jcc d m p (φ n))) atTop (𝓝 (T z)) := (T.continuous.tendsto z).comp hJn
    have hlim2 : Tendsto (fun n => T (sa16r_Jcc d m p (φ n))) atTop (𝓝 (sa16y8_D2 u₁ x v w)) := by
      refine (hp2 x v w).congr (fun n => ?_)
      rw [hT]
      rfl
    rw [← hu1]
    exact tendsto_nhds_unique hlim hlim2

end Rp5

end HRS.Whole.AppendixA.Phase2SA16Q
