import HRS.Commutator.Torus.NRSTAux3
import HRS.Kernel.Riesz

/-!
# NRS-T, part 4: the Fourier-side form of the commutator (algebra)

`S = ∑_j ∑_k (2πi k_j) ĝ(k) (V_j * A)(k) conj(A)(k) = - pr A (v·∇(g*A))`.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace HRS.Commutator.TorusNote.NRST

open HRS

variable {d : ℕ}

lemma enorm_neg (k : Lattice d) : Lattice.enorm (-k) = Lattice.enorm k := by
  unfold Lattice.enorm
  have : Lattice.toEuc (-k) = -Lattice.toEuc k := by
    ext i; simp [Lattice.toEuc]
  rw [this, norm_neg]

lemma rieszCoeff_neg (s : ℝ) (k : Lattice d) : rieszCoeff d s (-k) = rieszCoeff d s k := by
  unfold rieszCoeff
  by_cases h : k = 0
  · simp [h]
  · have h' : -k ≠ 0 := neg_ne_zero.2 h
    simp [h, h', enorm_neg]

lemma pr_eq_sum_of_subset (f g : TPA d) {T : Finset (Lattice d)} (hT : f.coeff.support ⊆ T) :
    pr f g = ∑ k ∈ T, f.coeff k * g.coeff (-k) := by
  rw [pr_eq_sum]
  refine Finset.sum_subset hT fun k _ hk => ?_
  have : f.coeff k = 0 := by simpa using hk
  simp [this]

/-- The multiplier `ĝ(k)` (convolution with the periodic Riesz kernel). -/
def Rg (d : ℕ) (s : ℝ) (f : TPA d) : TPA d := mulSeq (fun k => ((rieszCoeff d s k : ℝ) : ℂ)) f

lemma coeff_Rg (s : ℝ) (f : TPA d) (k : Lattice d) :
    (Rg d s f).coeff k = ((rieszCoeff d s k : ℝ) : ℂ) * f.coeff k := by
  simp [Rg]

lemma supp_Rg_subset (s : ℝ) (f : TPA d) : (Rg d s f).coeff.support ⊆ f.coeff.support :=
  supp_mulSeq_subset _ f

lemma Rg_dd (s : ℝ) (a : Fin d) (f : TPA d) : Rg d s (dd a f) = dd a (Rg d s f) := by
  rw [← AddMonoidAlgebra.coeff_inj]
  ext k
  simp only [coeff_Rg, coeff_dd]
  ring

lemma pr_Rg (s : ℝ) (f g : TPA d) : pr (Rg d s f) g = pr f (Rg d s g) := by
  classical
  set T : Finset (Lattice d) := f.coeff.support ∪ g.coeff.support.image Neg.neg with hT
  have h1 : pr (Rg d s f) g = ∑ k ∈ T, (Rg d s f).coeff k * g.coeff (-k) :=
    pr_eq_sum_of_subset _ _ ((supp_Rg_subset s f).trans Finset.subset_union_left)
  have h2 : pr f (Rg d s g) = ∑ k ∈ T, f.coeff k * (Rg d s g).coeff (-k) := by
    rw [pr_eq_sum_of_subset f _ (Finset.subset_union_left : f.coeff.support ⊆ T)]
  rw [h1, h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_Rg, coeff_Rg, rieszCoeff_neg]
  ring

/-- `S_j = - pr A (V_j * ∂_j (g * A))`. -/
lemma fourier_side_j (s : ℝ) (j : Fin d) (V A : TPA d) :
    ∑ k ∈ (V * A).coeff.support, ((2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) *
        ((rieszCoeff d s k : ℝ) : ℂ)) * ((V * A).coeff k * A.coeff (-k)) =
      - pr A (V * dd j (Rg d s A)) := by
  have h1 : pr (dd j (Rg d s (V * A))) A =
      ∑ k ∈ (V * A).coeff.support, ((2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) *
        ((rieszCoeff d s k : ℝ) : ℂ)) * ((V * A).coeff k * A.coeff (-k)) := by
    rw [pr_eq_sum_of_subset _ _ ((supp_dd_subset j _).trans (supp_Rg_subset s _))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_dd, coeff_Rg]
    ring
  rw [← h1, pr_dd, pr_Rg, ← Rg_dd]
  have : pr (V * A) (Rg d s (dd j A)) = pr A (V * Rg d s (dd j A)) := by
    unfold pr; congr 1; ring
  rw [this, Rg_dd]

lemma isRealT_Rg (s : ℝ) {A : TPA d} (hA : IsRealT A) : IsRealT (Rg d s A) := by
  intro k
  rw [coeff_Rg, coeff_Rg, rieszCoeff_neg, hA k, map_mul, Complex.conj_ofReal]

end HRS.Commutator.TorusNote.NRST
