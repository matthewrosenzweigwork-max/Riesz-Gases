/-
# HRS.Equilibrium.Q84dAuxAC — packet Q84d: properties of the modified triple kernel `G̃_ψ`
-/
import HRS.Equilibrium.Q84dAuxAB

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_measurable_Gtil (hsd : s < d) (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ)
    {E : Set (Torus d)} (hE : MeasurableSet E) {Jh : Torus d → Torus d → ℝ}
    (hJ : Measurable (fun p : Torus d × Torus d => Jh p.1 p.2)) :
    Measurable (fun p : Torus d × Torus d × Torus d => Gtil d s ρ ψ E Jh p.1 p.2.1 p.2.2) := by
  classical
  have h1 : Measurable (fun p : Torus d × Torus d × Torus d => p.1) := measurable_fst
  have h2 : Measurable (fun p : Torus d × Torus d × Torus d => p.2.1) := measurable_fst.comp measurable_snd
  have h3 : Measurable (fun p : Torus d × Torus d × Torus d => p.2.2) := measurable_snd.comp measurable_snd
  have hG : ∀ (a b c : Torus d × Torus d × Torus d → Torus d), Measurable a → Measurable b →
      Measurable c → Measurable (fun p => GsurK d s ρ ψ Jh (a p) (b p) (c p)) :=
    fun a b c ha hb hc => q84d_measurable_GsurK hsd ρ ψ hJ ha hb hc
  have hset : MeasurableSet {p : Torus d × Torus d × Torus d |
      p.1 ∈ E ∨ p.2.1 ∈ E ∨ p.2.2 ∈ E ∨ p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2} :=
    (h1 hE).union ((h2 hE).union ((h3 hE).union ((measurableSet_eq_fun h1 h2).union
      ((measurableSet_eq_fun h1 h3).union (measurableSet_eq_fun h2 h3)))))
  have hsum : Measurable (fun p : Torus d × Torus d × Torus d =>
      GsurK d s ρ ψ Jh p.1 p.2.1 p.2.2 + GsurK d s ρ ψ Jh p.2.1 p.1 p.2.2 +
      GsurK d s ρ ψ Jh p.1 p.2.2 p.2.1 + GsurK d s ρ ψ Jh p.2.2 p.1 p.2.1 +
      GsurK d s ρ ψ Jh p.2.1 p.2.2 p.1 + GsurK d s ρ ψ Jh p.2.2 p.2.1 p.1) :=
    (((((hG _ _ _ h1 h2 h3).add (hG _ _ _ h2 h1 h3)).add (hG _ _ _ h1 h3 h2)).add
      (hG _ _ _ h3 h1 h2)).add (hG _ _ _ h2 h3 h1)).add (hG _ _ _ h3 h2 h1)
  unfold Gtil
  exact Measurable.ite hset measurable_const (measurable_const.mul hsum)

theorem q84d_Gtil_symm (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ) (E : Set (Torus d))
    (Jh : Torus d → Torus d → ℝ) : IsSymmTriple (Gtil d s ρ ψ E Jh) := by
  classical
  intro x y z
  constructor
  · unfold Gtil
    have hc : (x ∈ E ∨ y ∈ E ∨ z ∈ E ∨ x = y ∨ x = z ∨ y = z) ↔
        (y ∈ E ∨ x ∈ E ∨ z ∈ E ∨ y = x ∨ y = z ∨ x = z) := by
      constructor <;> rintro (h | h | h | h | h | h) <;> simp [h, eq_comm]
    by_cases h : x ∈ E ∨ y ∈ E ∨ z ∈ E ∨ x = y ∨ x = z ∨ y = z
    · rw [if_pos h, if_pos (hc.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]; ring
  · unfold Gtil
    have hc : (x ∈ E ∨ y ∈ E ∨ z ∈ E ∨ x = y ∨ x = z ∨ y = z) ↔
        (x ∈ E ∨ z ∈ E ∨ y ∈ E ∨ x = z ∨ x = y ∨ z = y) := by
      constructor <;> rintro (h | h | h | h | h | h) <;> simp [h, eq_comm]
    by_cases h : x ∈ E ∨ y ∈ E ∨ z ∈ E ∨ x = y ∨ x = z ∨ y = z
    · rw [if_pos h, if_pos (hc.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]; ring

theorem q84d_Gtil_props (hd1 : 1 ≤ d) {ρ : Torus d → ℝ} {ψ : Torus d → Torus d → ℝ}
    (hsd : s < d) (hsymm : IsSymmPair ψ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) {E : Set (Torus d)}
    (hE0 : (volume : Measure (Torus d)) E = 0) {Jh : Torus d → Torus d → ℝ}
    (hgood : ∀ x y : Torus d, x ∉ E → y ∉ E → x ≠ y → Jpair d s ρ ψ x y = Jh x y)
    (hcan : IsCanonicalTriple (withDensityReal ρ) (Gpsi d s ρ ψ)) {KG : ℝ} (hKG0 : 0 ≤ KG)
    (hG : ∀ x y z : Torus d, x ≠ y → x ≠ z → y ≠ z → |Gpsi d s ρ ψ x y z| ≤
      KG * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z)) :
    IsCanonicalTriple (withDensityReal ρ) (Gtil d s ρ ψ E Jh) ∧
      (∀ x y z : Torus d, x ≠ y → x ≠ z → y ≠ z → |Gtil d s ρ ψ E Jh x y z| ≤
        KG * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z)) := by
  classical
  have hw0 : ∀ a b : Torus d, 0 ≤ wEnv s a b := fun a b => zero_le_one.trans (PairCorrAux.one_le_wEnv s a b)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    by_cases h : x ∈ E ∨ y ∈ E
    · have : Gtil d s ρ ψ E Jh x y = fun _ => 0 := by
        funext z
        unfold Gtil
        rw [if_pos]
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      rw [this]
      exact ⟨integrable_zero _ _ _, by simp⟩
    · push Not at h
      have hae : ∀ᵐ z ∂(withDensityReal ρ), Gtil d s ρ ψ E Jh x y z = Gpsi d s ρ ψ x y z := by
        have h0 : ∀ᵐ z ∂(volume : Measure (Torus d)), z ∉ E ∧ z ≠ x ∧ z ≠ y := by
          refine (ae_iff.2 ?_)
          have : {z : Torus d | ¬(z ∉ E ∧ z ≠ x ∧ z ≠ y)} ⊆ E ∪ ({x} ∪ {y}) := by
            intro z hz
            by_contra hn
            simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hn
            exact hz ⟨hn.1, hn.2.1, hn.2.2⟩
          exact measure_mono_null this (by
            rw [measure_union_null_iff, measure_union_null_iff]
            exact ⟨hE0, volume_singleton_torus hd1 x, volume_singleton_torus hd1 y⟩)
        filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le h0] with z hz
        exact q84d_Gtil_eq hsymm hsm hsd hgood h.1 h.2 hz.1 hxy hz.2.1.symm hz.2.2.symm
      obtain ⟨hi, hint⟩ := hcan x y hxy
      refine ⟨hi.congr (hae.mono fun z hz => hz.symm), ?_⟩
      rw [integral_congr_ae hae]
      exact hint
  · intro x y z hxy hxz hyz
    by_cases h : x ∈ E ∨ y ∈ E ∨ z ∈ E
    · have : Gtil d s ρ ψ E Jh x y z = 0 := by
        unfold Gtil
        rw [if_pos]
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      rw [this, abs_zero]
      exact mul_nonneg hKG0 (add_nonneg (add_nonneg (mul_nonneg (hw0 _ _) (hw0 _ _))
        (mul_nonneg (hw0 _ _) (hw0 _ _))) (mul_nonneg (hw0 _ _) (hw0 _ _)))
    · push Not at h
      rw [q84d_Gtil_eq hsymm hsm hsd hgood h.1 h.2.1 h.2.2 hxy hxz hyz]
      exact hG x y z hxy hxz hyz

end HRS.Q84d

end
