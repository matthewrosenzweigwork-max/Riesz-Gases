import HRS.MC.S7E3aAux3
import HRS.MC.S7E3aAux5
import HRS.MC.S7E1

/-!
# Packets `s7_E3a/b`, file 6: the lower bound `E Q^2 >= (1-4 eta)/2 ||h°||^2 - 2 N S^2`

Exact second moment of the finite sections (`E S_L^2 = (1/2) sum H_ij H_kl C_ik C_jl`), the finite-dimensional
lower bound of file 5 (with the tail of `1 - C` of file 3 and the row bound `S`), and passage to the `L^2` limit.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix

noncomputable section

namespace HRS.MC.Sec7.E3Aux6

open HRS HRS.Sec7

variable {d : ℕ} {ρ : Torus d → ℝ}

section Var

variable {s β : ℝ} {e : ℕ → Torus d → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {G : ℕ → Ω → ℝ}

theorem e3_sec_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (hρ : SmoothPosDensity ρ) (he : IsONBL2Zero (withDensityReal ρ) e)
    (hG : s7_GaussData d s β ρ e P G) (H : ℕ → ℕ → ℝ) (hH : ∀ i j, H i j = H j i) (L : ℕ) :
    ∫ ω, ((1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))) ^ 2 ∂P =
      (1 / 2 : ℝ) * ∑ i : Fin L, ∑ j : Fin L, ∑ k : Fin L, ∑ l : Fin L, H i j * H k l *
        (susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e k) *
          susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e j) (e l)) := by
  set C : ℕ → ℕ → ℝ := fun x y => susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e x) (e y)
    with hCdef
  have hpt : ∀ ω, (1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j * (G i ω * G j ω - C i j) =
      ∑ p : Fin L × Fin L, ((1 / 2 : ℝ) * H p.1 p.2) * (G p.1 ω * G p.2 ω - C p.1 p.2) := by
    intro ω
    simp only [Finset.sum_range, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hblock := E1.e1_var_block_eq hd hs0 hsd hβ hρ he hG L (fun i j => (1 / 2 : ℝ) * H i j)
  show ∫ ω, ((1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j * (G i ω * G j ω - C i j)) ^ 2 ∂P = _
  simp_rw [hpt]
  rw [hblock]
  have hB : ∑ i : Fin L, ∑ j : Fin L, ∑ k : Fin L, ∑ l : Fin L, H i j * H k l * (C i l * C j k) =
      ∑ i : Fin L, ∑ j : Fin L, ∑ k : Fin L, ∑ l : Fin L, H i j * H k l * (C i k * C j l) := by
    rw [E0b.e0b_sum_swap_kl]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hH (l : ℕ) (k : ℕ)]
  have hexp : ∑ i : Fin L, ∑ j : Fin L, ∑ k : Fin L, ∑ l : Fin L, (1 / 2 : ℝ) * H i j * ((1 / 2 : ℝ) * H k l) *
      (C i k * C j l + C i l * C j k) =
      (1 / 2 : ℝ) * ∑ i : Fin L, ∑ j : Fin L, ∑ k : Fin L, ∑ l : Fin L, H i j * H k l * (C i k * C j l) := by
    have : ∀ i j k l : Fin L, (1 / 2 : ℝ) * H i j * ((1 / 2 : ℝ) * H k l) * (C i k * C j l + C i l * C j k) =
        (1 / 4 : ℝ) * (H i j * H k l * (C i k * C j l)) + (1 / 4 : ℝ) * (H i j * H k l * (C i l * C j k)) := by
      intros; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hB]
    ring
  exact hexp

end Var


theorem e3_lower_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (hρ : SmoothPosDensity ρ) {e : ℕ → Torus d → ℝ} (he : IsONBL2Zero (withDensityReal ρ) e)
    {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (G : ℕ → Ω → ℝ), s7_GaussData d s β ρ e P G →
      ∀ (h : Torus d → Torus d → ℝ), Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
      MemLp (Function.uncurry h) 2 ((withDensityReal ρ).prod (withDensityReal ρ)) →
      ∀ {S : ℝ}, (∀ i L : ℕ, ∑ k ∈ Finset.range L, (E0b.e0bH ρ e h i k) ^ 2 ≤ S ^ 2) →
      ∀ Q : Ω → ℝ, AEMeasurable Q P → s7_IsChaosLimit d s β ρ e P G h Q →
        (1 - 4 * η) / 2 * s7_hcNorm2 d ρ h - 2 * N * S ^ 2 ≤ ∫ ω, Q ω ^ 2 ∂P := by
  obtain ⟨N, hN⟩ := E3Aux3.e3_cov_tail hd hs0 hsd hβ hρ he hη
  obtain ⟨c, hc0, hc1, hall⟩ := E1Aux1.e1a_cov_bounds hd hs0 hsd hβ hρ
  refine ⟨N, fun {Ω} _ P _ G hG h hm hsymm hL2 {S} hS Q hQ hchaos => ?_⟩
  have hprob := isProb_withDensityReal hρ.density
  have hG4 := E0b.e0b_memLp4 (e := e) (ρ := ρ) (s := s) (β := β) hG
  set H : ℕ → ℕ → ℝ := E0b.e0bH ρ e h with hHdef
  have hHs : ∀ i j, H i j = H j i := E1.e1_H_symm hρ he hsymm hL2
  set S' : ℕ → Ω → ℝ := fun L ω => (1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
    H i j * (G i ω * G j ω -
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) with hSdef
  have hSm : ∀ L, MemLp (S' L) 2 P := by
    intro L
    refine MemLp.const_mul ?_ _
    refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => ?_
    exact (E0b.e0b_X_memLp2 hG4 _ i j).const_mul _
  have hS0 : ∀ L, ∫ ω, S' L ω ∂P = 0 := by
    intro L
    have hX : ∀ i j : ℕ, Integrable (fun ω => H i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))) P := fun i j =>
      ((E0b.e0b_X_memLp2 hG4 _ i j).integrable one_le_two).const_mul _
    simp only [hSdef]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hX i j]
    have : ∀ i ∈ Finset.range L, ∫ ω, ∑ j ∈ Finset.range L, H i j * (G i ω * G j ω -
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) ∂P = 0 := by
      intro i _
      rw [integral_finsetSum _ fun j _ => hX i j]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [integral_const_mul]
      have hm0 : ∫ ω, (G i ω * G j ω -
          susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) ∂P = 0 := by
        have hGG : Integrable (fun ω => G i ω * G j ω) P :=
          ((hG4 i).mul (hG4 j) (r := 2)).integrable one_le_two
        rw [integral_sub hGG (integrable_const _), E1.e1_mean_pair hG hd hs0 hsd hβ hρ he i j]
        simp
      rw [hm0, mul_zero]
    rw [Finset.sum_eq_zero this, mul_zero]
  have hpars := E1Aux3.e1c_parseval (μ := withDensityReal ρ) he hm hL2
  set T : ℝ := ∫ z : Torus d × Torus d, canonicalCenter (withDensityReal ρ) h z.1 z.2 ^ 2
    ∂((withDensityReal ρ).prod (withDensityReal ρ)) with hT
  have ht : Tendsto (fun L : ℕ => ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j ^ 2)
      atTop (𝓝 T) := by
    have h1 : Tendsto (fun N : ℕ => Finset.range N ×ˢ Finset.range N) atTop atTop := by
      refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun p => ?_)
      · exact Finset.product_subset_product (Finset.range_mono hab) (Finset.range_mono hab)
      · exact ⟨max p.1 p.2 + 1, by
          simp only [Finset.mem_product, Finset.mem_range]; omega⟩
    have h2 := hpars.comp h1
    refine Tendsto.congr (fun N => ?_) h2
    simp only [Function.comp_apply]
    exact Finset.sum_product' (s := Finset.range N) (t := Finset.range N) (f := fun i j => H i j ^ 2)
  -- the section bounds
  have hsec : ∀ L, (1 / 2 : ℝ) * ((1 - 4 * η) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j ^ 2 -
        4 * N * S ^ 2) ≤ ∫ ω, S' L ω ^ 2 ∂P ∧
      ∫ ω, S' L ω ^ 2 ∂P ≤ 1 / 2 * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j ^ 2 := by
    intro L
    refine ⟨?_, (E1.e1_sec_bounds hd hs0 hsd hβ hρ he hG hc0 (fun n => (hall he n).1)
      (fun n => (hall he n).2) H hHs L).2⟩
    have hEq := e3_sec_eq hd hs0 hsd hβ hρ he hG H hHs L
    simp only [hSdef]
    rw [hEq]
    have hCpsd := E0a.s7e_cov_psd hd hs0 hsd hβ hρ he L
    have hBpsd : ((1 : Matrix (Fin L) (Fin L) ℝ) - Matrix.of fun i j : Fin L =>
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)).PosSemidef := by
      simpa using (hall he L).1
    have hmat := E3Aux5.e3_matrix_lower hη.le hBpsd hCpsd (fun y hy => hN L y hy)
      (fun i j : Fin L => H i j) (fun i j => hHs i j) (S := S) (fun i => by
        have := hS i L
        rw [Finset.sum_range] at this
        exact this)
    have hsq : ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j ^ 2 = ∑ i : Fin L, ∑ j : Fin L, H i j ^ 2 := by
      simp only [Finset.sum_range]
    rw [hsq]
    simp only [Matrix.of_apply] at hmat
    linarith
  have hQ2 := E1Aux4.e1d_limit S' hSm hS0 Q hQ hchaos
    (fun L => (1 / 2 : ℝ) * ((1 - 4 * η) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j ^ 2 -
        4 * N * S ^ 2))
    (fun L => 1 / 2 * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j ^ 2)
    (((ht.const_mul (1 - 4 * η)).sub_const (4 * N * S ^ 2)).const_mul _) (ht.const_mul _) hsec
  have := hQ2.2.2.1
  show (1 - 4 * η) / 2 * T - 2 * N * S ^ 2 ≤ _
  linarith

end HRS.MC.Sec7.E3Aux6

end
