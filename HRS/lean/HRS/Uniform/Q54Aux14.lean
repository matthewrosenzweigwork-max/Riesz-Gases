import HRS.Uniform.Q54Aux13

/-!
# Q54, part 14: function-level Hölder estimate and invariance of `Dom J`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

theorem prop_dom (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ) (hJ : mStar d ≤ J)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s J R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {φ : Torus d → ℝ}
    (hφ : Dom J φ) {u : ℝ} (hu : u ∈ Set.Icc 0 t) : Dom J (propagator D μ u t φ) := by
  obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical hd s hs0 hsd J hJ R MB Λ VB
  obtain ⟨-, -, h3, -⟩ := hmain D ν₀ T μ hA t ht φ hφ.1 hφ.2
  have hJ1 : 1 ≤ J := by have := ClassicalPart.three_le_mStar d; omega
  exact ⟨(prop_facts hd s hs0 hsd J hJ R MB Λ VB D ν₀ T μ hA ht hφ hu).2, (h3 J hJ1 le_rfl u hu).1⟩

theorem prop_hold (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB)
    (hBμ : 0 ≤ Bμ) (hBV : 0 ≤ BV) (a : ℝ) (hK : (d : ℝ) + |a| + 4 ≤ K) (ν₀ νM : ℝ) (hν₀ : 0 < ν₀)
    (J : ℕ) (hJa : a + 2 < J) (hJ3 : (3 : ℝ) < J) (hJm : mStar d ≤ J) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ (R : Regime) (MB' Λ VB ν₁ : ℝ) (D : DynData d) (T : ℝ)
      (μ : ℝ → Torus d → ℝ), AdjointData s J R MB' Λ VB D ν₁ T μ →
      (∀ r ∈ Set.Icc (0 : ℝ) T, GenHyp d s K MB Bμ BV D (μ r)) → ν₀ ≤ D.invβ → D.invβ ≤ νM →
      ∀ {φ : Torus d → ℝ}, Dom J φ → ∀ {u t : ℝ}, 0 ≤ u → u ≤ t → 0 < t → t ≤ T →
        MemSobolev a (fun x => propagator D μ u t φ x - φ x) ∧
          sobolevNorm a (fun x => propagator D μ u t φ x - φ x) ^ 2 ≤
            B * sobolevNorm (a + 2) φ ^ 2 * (t - u) * Real.exp (A * (t - u)) := by
  obtain ⟨A, B, hA0, hB0, hH⟩ := forward_hold s hsd K MB Bμ BV hMB hBμ hBV a hK ν₀ νM hν₀
  refine ⟨A, B, hA0, hB0, fun R MB' Λ VB ν₁ D T μ hA hG hν hνM φ hφ u t hu hut ht0 htT => ?_⟩
  have hJ1 : 1 ≤ J := by
    have : (3 : ℝ) < J := hJ3
    exact_mod_cast (by linarith : (1 : ℝ) ≤ J)
  have htm : t ∈ Set.Ioc 0 T := ⟨ht0, htT⟩
  have hutm : u ∈ Set.Icc 0 t := ⟨hu, hut⟩
  have hJd : (d : ℝ) / 2 < J := by
    have := mStar_gt d
    have : (mStar d : ℝ) ≤ J := by exact_mod_cast hJm
    linarith
  have hφa : MemSobolev a φ := MFAdjoint.memSobolev_mono_idx (m := J) hφ.2 (by linarith)
  have hφa2 : MemSobolev (a + 2) φ := MFAdjoint.memSobolev_mono_idx (m := J) hφ.2 (by linarith)
  obtain ⟨hprop, hpc⟩ := prop_facts hd s hs0 hsd J hJm R MB' Λ VB D ν₁ T μ hA htm hφ hutm
  obtain ⟨C₀, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd J hJ1 R MB' Λ VB
  have hφc : MemHs (J : ℝ) (coeffOf φ) := (hsNormSq_coeffOf (J : ℝ) φ hφ.2).1
  obtain ⟨hsol, hw, -⟩ := hspec D ν₁ T μ hA t htm (coeffOf φ) hφc
  set F := propagatorCoeff D μ J t (coeffOf φ) with hF
  have hcA : ContinuousInHs (a + 2) F t := forward_strong_continuity (J : ℝ) t F hw (a + 2) hJa
  have hA1 : AdjointData s 1 R MB' Λ VB D ν₁ T μ := StabAux.adjointData_mono hJ1 hA
  have hcm : ContinuousInHs (((1 : ℕ) : ℝ) + 2) F t :=
    forward_strong_continuity (J : ℝ) t F hw _ (by push_cast; linarith)
  have hτ : t - u ∈ Set.Icc (0 : ℝ) t := ⟨by linarith, by linarith⟩
  have hen := hH D T μ 1 R MB' Λ VB ν₁ hA1 hG hν hνM t htm (coeffOf φ) F hsol hcA hcm (t - u) hτ
  obtain ⟨hreal, hsum⟩ := pc_data hd s hs0 hsd J hJ1 hJd R MB' Λ VB D ν₁ T μ hA htm hφ hτ
  have hcoef : coeffOf (propagator D μ u t φ) = F (t - u) := by
    rw [hprop]; exact coeffOf_toFun _ hreal hsum
  have hcd : Continuous (fun x => propagator D μ u t φ x - φ x) := hpc.sub hφ.1
  have hcoefd : coeffOf (fun x => propagator D μ u t φ x - φ x) = fun k => F (t - u) k - coeffOf φ k := by
    have := coeffOf_lin hpc hφ.1 1 (-1)
    have e : (fun x => propagator D μ u t φ x - φ x) =
        fun x => (1 : ℝ) * propagator D μ u t φ x + (-1 : ℝ) * φ x := by funext x; ring
    rw [e, this, hcoef]
    funext k; push_cast; ring
  have hmemA2 : MemHs (a + 2) (F (t - u)) := hcA.1 (t - u) hτ
  have hmemφ2 : MemHs (a + 2) (coeffOf φ) := (hsNormSq_coeffOf (a + 2) φ hφa2).1
  have hmemd : MemHs a (F (t - u) - coeffOf φ) :=
    (memHs_sub hmemA2 hmemφ2).mono (by linarith)
  have hMS : MemSobolev a (fun x => propagator D μ u t φ x - φ x) :=
    memSobolev_of_memHs a _ (ClassicalAux.memLp_two_of_continuous hcd) (by
      rw [hcoefd]; exact hmemd)
  refine ⟨hMS, ?_⟩
  have e1 := (hsNormSq_coeffOf a _ hMS).2
  have e2 := (hsNormSq_coeffOf (a + 2) φ hφa2).2
  rw [hcoefd] at e1
  rw [← e1, ← e2]
  exact hen

end HRS.Uniform.Q54
