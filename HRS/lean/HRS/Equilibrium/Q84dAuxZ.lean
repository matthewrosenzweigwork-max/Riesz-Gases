/-
# HRS.Equilibrium.Q84dAuxZ — packet Q84d: killed/symmetrised kernels (generic lemmas)
-/
import HRS.Equilibrium.Q84dAuxY

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

open Classical in
/-- The symmetrised pair kernel, set to `0` on `E × 𝕋 ∪ 𝕋 × E ∪ diagonal`. -/
def Jtil (E : Set (Torus d)) (Jh : Torus d → Torus d → ℝ) (x y : Torus d) : ℝ :=
  if x ∈ E ∨ y ∈ E ∨ x = y then 0 else (1 / 2) * (Jh x y + Jh y x)

theorem q84d_measurable_Jtil {E : Set (Torus d)} (hE : MeasurableSet E) {Jh : Torus d → Torus d → ℝ}
    (hJ : Measurable (fun p : Torus d × Torus d => Jh p.1 p.2)) :
    Measurable (fun p : Torus d × Torus d => Jtil E Jh p.1 p.2) := by
  classical
  unfold Jtil
  have hset : MeasurableSet {p : Torus d × Torus d | p.1 ∈ E ∨ p.2 ∈ E ∨ p.1 = p.2} :=
    (measurable_fst hE).union ((measurable_snd hE).union (measurableSet_eq_fun measurable_fst measurable_snd))
  have hJ' : Measurable (fun p : Torus d × Torus d => Jh p.2 p.1) := q84d_measurable_swap_arg hJ
  exact Measurable.ite hset measurable_const (measurable_const.mul (hJ.add hJ'))

theorem q84d_Jtil_symm (E : Set (Torus d)) (Jh : Torus d → Torus d → ℝ) (x y : Torus d) :
    Jtil E Jh x y = Jtil E Jh y x := by
  classical
  unfold Jtil
  have : (x ∈ E ∨ y ∈ E ∨ x = y) ↔ (y ∈ E ∨ x ∈ E ∨ y = x) := by
    constructor <;> rintro (h | h | h) <;> simp [h, eq_comm]
  by_cases h : x ∈ E ∨ y ∈ E ∨ x = y
  · rw [if_pos h, if_pos (this.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (this.2 h')), add_comm]

theorem q84d_Jtil_eq {E : Set (Torus d)} {Jh : Torus d → Torus d → ℝ} {x y : Torus d}
    (hx : x ∉ E) (hy : y ∉ E) (hxy : x ≠ y) :
    Jtil E Jh x y = (1 / 2) * (Jh x y + Jh y x) := by
  classical
  unfold Jtil
  rw [if_neg]
  rintro (h | h | h)
  · exact hx h
  · exact hy h
  · exact hxy h

theorem q84d_Jtil_zero {E : Set (Torus d)} {Jh : Torus d → Torus d → ℝ} {x y : Torus d}
    (h : x ∈ E ∨ y ∈ E ∨ x = y) : Jtil E Jh x y = 0 := by
  classical
  unfold Jtil
  rw [if_pos h]

/-- Properties of the modified pair kernel `𝒥̃ψ`. -/
theorem q84d_Jtil_props (hd : 1 ≤ d) {ρ : Torus d → ℝ} (hρs : SmoothPosDensity ρ)
    {E : Set (Torus d)} (hE : MeasurableSet E) (hE0 : (volume : Measure (Torus d)) E = 0)
    {J Jh : Torus d → Torus d → ℝ} (hJsymm : IsSymmPair J)
    (hJh : Measurable (fun p : Torus d × Torus d => Jh p.1 p.2))
    (hgood : ∀ x y : Torus d, x ∉ E → y ∉ E → x ≠ y → J x y = Jh x y)
    (hcan : IsCanonicalPair (withDensityReal ρ) J) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x y, x ≠ y → |J x y| ≤ K * wEnv s x y) :
    Measurable (fun p : Torus d × Torus d => Jtil E Jh p.1 p.2) ∧ IsSymmPair (Jtil E Jh) ∧
      IsCanonicalPair (withDensityReal ρ) (Jtil E Jh) ∧
      (∀ x y, x ≠ y → |Jtil E Jh x y| ≤ K * wEnv s x y) ∧
      (∀ x y : Torus d, x ∉ E → y ∉ E → x ≠ y → Jtil E Jh x y = J x y) := by
  have hgood' : ∀ x y : Torus d, x ∉ E → y ∉ E → x ≠ y → Jtil E Jh x y = J x y := by
    intro x y hx hy hxy
    rw [q84d_Jtil_eq hx hy hxy, ← hgood x y hx hy hxy, ← hgood y x hy hx hxy.symm, hJsymm y x]
    ring
  refine ⟨q84d_measurable_Jtil hE hJh, q84d_Jtil_symm E Jh, ?_, ?_, hgood'⟩
  · intro x
    by_cases hx : x ∈ E
    · have : Jtil E Jh x = fun _ => 0 := funext fun y => q84d_Jtil_zero (Or.inl hx)
      rw [this]
      exact ⟨integrable_zero _ _ _, by simp⟩
    · have hae : ∀ᵐ y ∂(withDensityReal ρ), Jtil E Jh x y = J x y := by
        have h0 : ∀ᵐ y ∂(volume : Measure (Torus d)), y ∉ E ∧ y ≠ x := by
          refine (ae_iff.2 ?_)
          have : {y : Torus d | ¬(y ∉ E ∧ y ≠ x)} ⊆ E ∪ {x} := by
            intro y hy
            by_contra h
            simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at h
            exact hy ⟨h.1, h.2⟩
          exact measure_mono_null this (by
            rw [measure_union_null_iff]; exact ⟨hE0, volume_singleton_torus hd x⟩)
        filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le h0] with y hy
        exact hgood' x y hx hy.1 hy.2.symm
      refine ⟨(hcan x).1.congr (hae.mono fun y hy => hy.symm), ?_⟩
      rw [integral_congr_ae hae]
      exact (hcan x).2
  · intro x y hxy
    by_cases h : x ∈ E ∨ y ∈ E ∨ x = y
    · rw [q84d_Jtil_zero h, abs_zero]
      exact mul_nonneg hK0 (zero_le_one.trans (PairCorrAux.one_le_wEnv s x y))
    · push Not at h
      rw [hgood' x y h.1 h.2.1 hxy]
      exact hK x y hxy

end HRS.Q84d

end
