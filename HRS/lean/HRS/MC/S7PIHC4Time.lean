import HRS.MC.S7PIHC3Space

/-!
# Packet piH, `C^{1,2}` extension, part 4: the time derivative of the extension
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIH

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

variable {q : ℕ}

theorem S7PIH_hasDerivWithinAt_of_notMem {f : ℝ → ℝ} {s : Set ℝ} {x : ℝ} (h : x ∉ closure s) (f' : ℝ) :
    HasDerivWithinAt f f' s x :=
  hasDerivWithinAt_iff_hasFDerivWithinAt.2 (HasFDerivWithinAt.of_notMem_closure h)

variable {a b : ℝ} {A S : ℝ → Matrix (Fin q) (Fin q) ℝ} {G : EuclideanSpace ℝ (Fin q) → ℝ}

/-- The time derivative of the extension is `W (ρ t)`. -/
theorem S7PIH_ext_hasDerivAt (hab : a ≤ b)
    (hA : ∀ i j, ContinuousOn (fun v => A v i j) (Set.Icc a b))
    (hApsd : ∀ v ∈ Set.Icc a b, (A v).PosSemidef) (hSb : (S b).PosSemidef)
    (hS : ∀ u ∈ Set.Icc a b, ∀ i j, S u i j = S b i j + ∫ v in Set.Ioc u b, A v i j)
    (hG : MemCb 4 G) (c : EuclideanSpace ℝ (Fin q)) (t : ℝ) :
    HasDerivAt (fun r => S7PIH_ext a b A S G r c)
      (S7PIH_Wphi (fun i j => A (S7PIH_rho a b t) i j) (gaussHeat S G (S7PIH_rho a b t)) c) t := by
  set Wf : ℝ → ℝ := fun r => S7PIH_Wphi (fun i j => A r i j) (gaussHeat S G r) c with hWf
  have hG2 : MemCb 2 G := S7PIH_cb_mono hG (by norm_num)
  have hpde : ∀ r ∈ Set.Icc a b, HasDerivWithinAt (fun s => gaussHeat S G s c) (Wf r)
      (Set.Icc a b) r := by
    intro r hr
    have := s7_PIH_heat_pde_proof a b hab A S hA hApsd hSb hS G hG2 c r hr
    have hW : Wf r = -(1 / 2) * ∑ i, ∑ j, A r i j *
        ∫ x, iteratedFDeriv ℝ 2 G (c + x) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]
          ∂(multivariateGaussian 0 (S r)) := by
      simp only [hWf, S7PIH_Wphi]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      congr 1
      exact S7PIH_heat_D2_eval (multivariateGaussian 0 (S r)) hG2 c _
    rw [hW]; exact this
  have e1 : ∀ r, r ≤ a → S7PIH_ext a b A S G r c = gaussHeat S G a c + (r - a) * Wf a := by
    intro r hr
    simp only [S7PIH_ext, S7PIH_rho_of_le hab hr, hWf]
  have e2 : ∀ r ∈ Set.Icc a b, S7PIH_ext a b A S G r c = gaussHeat S G r c := by
    intro r hr
    simp only [S7PIH_ext, S7PIH_rho_of_mem hr, sub_self, zero_mul, add_zero]
  have e3 : ∀ r, b ≤ r → S7PIH_ext a b A S G r c = gaussHeat S G b c + (r - b) * Wf b := by
    intro r hr
    simp only [S7PIH_ext, S7PIH_rho_of_ge hab hr, hWf]
  have hg : ∀ (r0 : ℝ) (r : ℝ), HasDerivAt (fun r => gaussHeat S G r0 c + (r - r0) * Wf r0) (Wf r0) r :=
    fun r0 r => by
      have := (((hasDerivAt_id r).sub_const r0).mul_const (Wf r0)).const_add (gaussHeat S G r0 c)
      simpa using this
  have hP1 : HasDerivWithinAt (fun r => S7PIH_ext a b A S G r c) (Wf (S7PIH_rho a b t)) (Set.Iic a) t := by
    by_cases ht : t ≤ a
    · rw [S7PIH_rho_of_le hab ht]
      exact (hg a t).hasDerivWithinAt.congr (fun r hr => e1 r hr) (e1 t ht)
    · exact S7PIH_hasDerivWithinAt_of_notMem (by rwa [isClosed_Iic.closure_eq]) _
  have hP2 : HasDerivWithinAt (fun r => S7PIH_ext a b A S G r c) (Wf (S7PIH_rho a b t)) (Set.Icc a b) t := by
    by_cases ht : t ∈ Set.Icc a b
    · rw [S7PIH_rho_of_mem ht]
      exact (hpde t ht).congr (fun r hr => e2 r hr) (e2 t ht)
    · exact S7PIH_hasDerivWithinAt_of_notMem (by rwa [isClosed_Icc.closure_eq]) _
  have hP3 : HasDerivWithinAt (fun r => S7PIH_ext a b A S G r c) (Wf (S7PIH_rho a b t)) (Set.Ici b) t := by
    by_cases ht : b ≤ t
    · rw [S7PIH_rho_of_ge hab ht]
      exact (hg b t).hasDerivWithinAt.congr (fun r hr => e3 r hr) (e3 t ht)
    · exact S7PIH_hasDerivWithinAt_of_notMem (by rwa [isClosed_Ici.closure_eq]) _
  have hU : Set.Iic a ∪ Set.Icc a b ∪ Set.Ici b = Set.univ := by
    ext r
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc, Set.mem_Ici, Set.mem_univ, iff_true]
    by_cases h1 : r ≤ a
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : b ≤ r
      · exact Or.inr h2
      · exact Or.inl (Or.inr ⟨not_le.1 h1 |>.le, not_le.1 h2 |>.le⟩)
  have := (hP1.union hP2).union hP3
  rw [hU, hasDerivWithinAt_univ] at this
  exact this

end HRS.MC.Sec7.S7PIH

end
