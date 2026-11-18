import HRS.MC.S7PIHC1Deriv

/-!
# Packet piH, `C^{1,2}` extension, part 2: the Taylor-1 extension and its spatial regularity
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIH

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

variable {q : ℕ}

/-- Projection of the time on `[a,b]`. -/
def S7PIH_rho (a b r : ℝ) : ℝ := max a (min r b)

theorem S7PIH_rho_cont (a b : ℝ) : Continuous (S7PIH_rho a b) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem S7PIH_rho_mem {a b : ℝ} (hab : a ≤ b) (r : ℝ) : S7PIH_rho a b r ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

theorem S7PIH_rho_of_mem {a b r : ℝ} (hr : r ∈ Set.Icc a b) : S7PIH_rho a b r = r := by
  unfold S7PIH_rho
  rw [min_eq_left hr.2, max_eq_right hr.1]

theorem S7PIH_rho_of_le {a b r : ℝ} (hab : a ≤ b) (hr : r ≤ a) : S7PIH_rho a b r = a := by
  unfold S7PIH_rho
  rw [max_eq_left ((min_le_left _ _).trans hr)]

theorem S7PIH_rho_of_ge {a b r : ℝ} (hab : a ≤ b) (hr : b ≤ r) : S7PIH_rho a b r = b := by
  unfold S7PIH_rho
  rw [min_eq_right hr, max_eq_right hab]

/-- The Taylor-1 extension in time of the heat function. -/
def S7PIH_ext (a b : ℝ) (A S : ℝ → Matrix (Fin q) (Fin q) ℝ) (G : EuclideanSpace ℝ (Fin q) → ℝ)
    (r : ℝ) (c : EuclideanSpace ℝ (Fin q)) : ℝ :=
  gaussHeat S G (S7PIH_rho a b r) c + (r - S7PIH_rho a b r) *
    S7PIH_Wphi (fun i j => A (S7PIH_rho a b r) i j) (gaussHeat S G (S7PIH_rho a b r)) c

section Hyp

variable {a b : ℝ} {A S : ℝ → Matrix (Fin q) (Fin q) ℝ}

theorem S7PIH_heat_cd4 (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 4 G) (r : ℝ) : ContDiff ℝ 4 (gaussHeat S G r) :=
  S7PIH_heat_contDiff (multivariateGaussian 0 (S r)) (by norm_num) hG

/-- joint continuity of the evaluations of the derivatives of the heat function along `ρ`. -/
theorem S7PIH_cont_iter (hab : a ≤ b)
    (hA : ∀ i j, ContinuousOn (fun v => A v i j) (Set.Icc a b))
    (hApsd : ∀ v ∈ Set.Icc a b, (A v).PosSemidef) (hSb : (S b).PosSemidef)
    (hS : ∀ u ∈ Set.Icc a b, ∀ i j, S u i j = S b i j + ∫ v in Set.Ioc u b, A v i j)
    {G : EuclideanSpace ℝ (Fin q) → ℝ} (hG : MemCb 4 G) {j : ℕ} (hj : j ≤ 4)
    (m : Fin j → EuclideanSpace ℝ (Fin q)) :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin q) =>
      iteratedFDeriv ℝ j (gaussHeat S G (S7PIH_rho a b p.1)) p.2 m) := by
  have hcont := S7PIH_heat_cont_ab hab hA hApsd hSb hS hG hj
  have hpair : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin q) => (S7PIH_rho a b p.1, p.2) :=
    ((S7PIH_rho_cont a b).comp continuous_fst).prodMk continuous_snd
  have := hcont.comp_continuous hpair (fun p => ⟨S7PIH_rho_mem hab p.1, Set.mem_univ _⟩)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => EuclideanSpace ℝ (Fin q)) ℝ m).continuous.comp this

theorem S7PIH_cont_A (hab : a ≤ b) (hA : ∀ i j, ContinuousOn (fun v => A v i j) (Set.Icc a b))
    (i j : Fin q) : Continuous (fun r : ℝ => A (S7PIH_rho a b r) i j) :=
  (hA i j).comp_continuous (S7PIH_rho_cont a b) (S7PIH_rho_mem hab)

end Hyp

end HRS.MC.Sec7.S7PIH

end
