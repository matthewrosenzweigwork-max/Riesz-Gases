/-
# HRS.Equilibrium.Q84eAuxJ — packet Q84e: the modified kernels with an explicit uniform constant

`q84d_modified_kernels` hides the size constant `K` of `B_t`, `G_t` in an existential; here the
same construction (verbatim proof) exposes `K = C_u K₁` with `C_u` independent of `(f, K₁, ψ)`, as
needed for the constants in the final bound of `normal_form`.
-/
import HRS.Equilibrium.Q84dStationary

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84e

open HRS.Q84d

variable {d : ℕ} {s : ℝ}

theorem q84e_modified_kernels_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ), Torus.IsSmooth f →
      IsPairCorrector d s V β ρ f K₁ ψ →
      IsCanonicalTriple (withDensityReal ρ) (Gpsi d s ρ ψ) →
      ∃ (Jt Bt : Torus d → Torus d → ℝ) (Gt : Torus d → Torus d → Torus d → ℝ),
      (Measurable (fun p : Torus d × Torus d => Jt p.1 p.2) ∧ IsSymmPair Jt ∧
        IsCanonicalPair (withDensityReal ρ) Jt ∧
        ∀ x y, x ≠ y → |Jt x y| ≤ K₁ * wEnv s x y) ∧
      (Measurable (fun p : Torus d × Torus d => Bt p.1 p.2) ∧ IsSymmPair Bt ∧
        ∀ x y, x ≠ y → |Bt x y| ≤ (Cu * K₁) * wEnv s x y ^ 2) ∧
      (Measurable (fun p : Torus d × Torus d × Torus d => Gt p.1 p.2.1 p.2.2) ∧ IsSymmTriple Gt ∧
        IsCanonicalTriple (withDensityReal ρ) Gt ∧
        ∀ x y z, x ≠ y → x ≠ z → y ≠ z → |Gt x y z| ≤
          (Cu * K₁) * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z)) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ᵐ X ∂(canonicalGibbs (periodicRiesz d s) V N β),
        errStat d s ρ (N := N) ψ X =
          -(2 / (N : ℝ)) * Fstat (N := N) Jt X + (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum Gt X -
            (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered Bt X := by
  obtain ⟨C, hC⟩ := Q84a.q84a_estimates hd hcrit β hβ V hV ρ hρ hρs
  refine ⟨|C|, abs_nonneg _, fun f K₁ ψ hf hψ hGcan => ?_⟩
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hcrit]; linarith
  have hK₁ := q84d_K_nonneg hd hcrit hψ
  have hsm := hψ.size.smooth
  have hsymm := hψ.symm
  obtain ⟨hG, hB⟩ := hC f K₁ ψ hf hψ
  obtain ⟨E, Jh, hE, hE0, hJh, hgood⟩ := q84d_jpair_modification (by omega) hsd hρs hf hψ
  have hJsymm : IsSymmPair (Jpair d s ρ ψ) := fun x y => Q84.q84_Jpair_symm hsymm x y
  obtain ⟨hJm, hJs, hJc, hJb, hJeq⟩ := q84d_Jtil_props (s := s) (by omega) hρs hE hE0 hJsymm hJh hgood
    hψ.jpair_canonical hK₁ hψ.jpair_bound
  have hK : 0 ≤ |C| * K₁ := mul_nonneg (abs_nonneg _) hK₁
  have hB' : ∀ x y : Torus d, x ≠ y → |Bpsi d s ρ ψ x y| ≤ (|C| * K₁) * wEnv s x y ^ 2 := fun x y hxy =>
    (hB x y hxy).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hK₁) (by positivity))
  have hG' : ∀ x y z : Torus d, x ≠ y → x ≠ z → y ≠ z → |Gpsi d s ρ ψ x y z| ≤
      (|C| * K₁) * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z) := by
    intro x y z hxy hxz hyz
    have w0 : ∀ a b : Torus d, 0 ≤ wEnv s a b := fun a b => zero_le_one.trans (PairCorrAux.one_le_wEnv s a b)
    exact (hG x y z hxy hxz hyz).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hK₁)
      (add_nonneg (add_nonneg (mul_nonneg (w0 _ _) (w0 _ _)) (mul_nonneg (w0 _ _) (w0 _ _)))
        (mul_nonneg (w0 _ _) (w0 _ _))))
  obtain ⟨hBm, hBs, hBb, hBeq⟩ := q84d_Btil_props hsd hsymm hsm hK hB'
  obtain ⟨hGc, hGb⟩ := q84d_Gtil_props (s := s) (by omega) hsd hsymm hsm hE0 hgood hGcan hK hG'
  refine ⟨Jtil E Jh, Btil d s ρ ψ, Gtil d s ρ ψ E Jh, ⟨hJm, hJs, hJc, hJb⟩,
    ⟨hBm, hBs, hBb⟩, ⟨q84d_measurable_Gtil hsd ρ ψ hE hJh, q84d_Gtil_symm ρ ψ E Jh, hGc, hGb⟩, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  filter_upwards [q84d_gibbs_ac.ae_le (q84d_ae_not_collision (N := N) (d := d) (by omega)),
    q84d_ae_not_mem_null (V := V) (β := β) (N := N) hE0 (periodicRiesz d s)] with X hX hXE
  have hXne : ∀ a b : Fin N, a ≠ b → X a ≠ X b := fun a b hab hXab => hX ⟨a, b, hab, hXab⟩
  have e1 : pairSumOrdered (Jpair d s ρ ψ) X = pairSumOrdered (Jtil E Jh) X := by
    unfold pairSumOrdered
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    exact (hJeq _ _ (hXE i) (hXE j) (hXne i j (Finset.ne_of_mem_erase hj).symm)).symm
  have e2 : tripleSum (Gpsi d s ρ ψ) X = tripleSum (Gtil d s ρ ψ E Jh) X := by
    unfold tripleSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    exact (q84d_Gtil_eq hsymm hsm hsd hgood (hXE i) (hXE j) (hXE k) (hXne i j hji.symm)
      (hXne i k hki.symm) (hXne j k hkj.symm)).symm
  have e3 : pairSumOrdered (Bpsi d s ρ ψ) X = pairSumOrdered (Btil d s ρ ψ) X := by
    unfold pairSumOrdered
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    exact (hBeq _ _ (hXne i j (Finset.ne_of_mem_erase hj).symm)).symm
  unfold errStat Fstat
  rw [e1, e2, e3]


end HRS.Q84e

end
