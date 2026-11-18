import HRS.Uniform.Q54Aux9
import HRS.Uniform.Q54Aux10
import HRS.PDE.MeanFieldAdjointWiring

/-!
# Q54, part 11: the adjoint propagator at a real Sobolev level (function level)

For adjoint data of level `J` on every window `[0,T]` (`AdjointData`), coefficient decay of the coefficient path
(`GenHyp`) and `φ` continuous in `H^J`:

* `prop_eq_toFun`: `U^{u,t}φ = toFun (propagatorCoeff … (t-u))` (Proposition 3.9);
* `propagator_quasi`: `‖U^{u,t}φ‖_{H^a} ≤ e^{C (t-u)} ‖φ‖_{H^a}` for every real `a` with `a + 2 < J`
  (`d + |a| + 4 ≤ K`), `C` independent of `T` (the real-index energy inequality).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

/-- the class of functions on which the propagator is considered. -/
def Dom (J : ℕ) (φ : Torus d → ℝ) : Prop := Continuous φ ∧ MemSobolev (J : ℝ) φ

theorem mStar_gt (d : ℕ) : (d : ℝ) / 2 + 2 < (mStar d : ℝ) := by
  unfold mStar
  push_cast
  have := Nat.lt_floor_add_one ((d : ℝ) / 2)
  linarith

theorem prop_facts (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ) (hJ : mStar d ≤ J)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s J R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {φ : Torus d → ℝ}
    (hφ : Dom J φ) {u : ℝ} (hu : u ∈ Set.Icc 0 t) :
    propagator D μ u t φ = (fun x => toFun (propagatorCoeff D μ J t (coeffOf φ) (t - u)) x) ∧
      Continuous (propagator D μ u t φ) := by
  obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical hd s hs0 hsd J hJ R MB Λ VB
  obtain ⟨h1, hpe, -, -⟩ := hmain D ν₀ T μ hA t ht φ hφ.1 hφ.2
  refine ⟨hpe u hu, ?_⟩
  rw [hpe u hu]
  have := h1.c2 u hu
  exact ClassicalAux.continuous_of_isCk (ClassicalAux.isCk_of_le (by norm_num) this)

theorem propagator_quasi (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB)
    (hBμ : 0 ≤ Bμ) (hBV : 0 ≤ BV) (a : ℝ) (hK : (d : ℝ) + |a| + 4 ≤ K) (ν₀ : ℝ) (hν₀ : 0 < ν₀)
    (J : ℕ) (hJa : a + 2 < J) (hJ3 : (3 : ℝ) < J) (hJm : mStar d ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : Regime) (MB' Λ VB ν₁ : ℝ) (D : DynData d) (T : ℝ) (μ : ℝ → Torus d → ℝ),
      AdjointData s J R MB' Λ VB D ν₁ T μ →
      (∀ r ∈ Set.Icc (0 : ℝ) T, GenHyp d s K MB Bμ BV D (μ r)) → ν₀ ≤ D.invβ →
      ∀ {φ : Torus d → ℝ}, Dom J φ → ∀ {u t : ℝ}, 0 ≤ u → u ≤ t → 0 < t → t ≤ T →
        MemSobolev a (propagator D μ u t φ) ∧
          sobolevNorm a (propagator D μ u t φ) ≤ Real.exp (C * (t - u)) * sobolevNorm a φ := by
  obtain ⟨C, hC, hE⟩ := forward_energy_bound s hsd K MB Bμ BV hMB hBμ hBV a hK ν₀ hν₀
  refine ⟨C, hC, fun R MB' Λ VB ν₁ D T μ hA hG hν φ hφ u t hu hut ht0 htT => ?_⟩
  have hJ1 : 1 ≤ J := by
    have : (3 : ℝ) < J := hJ3
    exact_mod_cast (by linarith : (1 : ℝ) ≤ J)
  have htm : t ∈ Set.Ioc 0 T := ⟨ht0, htT⟩
  have hutm : u ∈ Set.Icc 0 t := ⟨hu, hut⟩
  have hφa : MemSobolev a φ := MFAdjoint.memSobolev_mono_idx (m := J) hφ.2 (by linarith)
  have hJd : (d : ℝ) / 2 < J := by
    have := mStar_gt d
    have : (mStar d : ℝ) ≤ J := by exact_mod_cast hJm
    linarith
  obtain ⟨hprop, hpc⟩ := prop_facts hd s hs0 hsd J hJm R MB' Λ VB D ν₁ T μ hA htm hφ hutm
  -- the forward solution
  obtain ⟨C₀, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd J hJ1 R MB' Λ VB
  have hφc : MemHs (J : ℝ) (coeffOf φ) := (hsNormSq_coeffOf (J : ℝ) φ hφ.2).1
  obtain ⟨hsol, hw, -⟩ := hspec D ν₁ T μ hA t htm (coeffOf φ) hφc
  set F := propagatorCoeff D μ J t (coeffOf φ) with hF
  have hcA : ContinuousInHs (a + 2) F t := forward_strong_continuity (J : ℝ) t F hw (a + 2) hJa
  have hA1 : AdjointData s 1 R MB' Λ VB D ν₁ T μ := StabAux.adjointData_mono hJ1 hA
  have hcm : ContinuousInHs (((1 : ℕ) : ℝ) + 2) F t :=
    forward_strong_continuity (J : ℝ) t F hw _ (by push_cast; linarith)
  have hτ : t - u ∈ Set.Icc (0 : ℝ) t := ⟨by linarith, by linarith⟩
  have hen := hE D T μ 1 R MB' Λ VB ν₁ hA1 hG hν t htm (coeffOf φ) F hsol hcA hcm (t - u) hτ
  -- real and summable coefficients
  have hre0 : IsRealCoeff (coeffOf φ) := isRealCoeff_coeffOf φ (hφ.2.1.integrable one_le_two)
  have hreal := ClassicalPart.propagatorCoeff_real hd s hs0 hsd J hJ1 R MB' Λ VB D ν₁ T μ hA t htm
    (coeffOf φ) hφc hre0 (t - u) hτ
  have hmemJ : MemHs (J : ℝ) (F (t - u)) := hw.1 _ hτ
  have hsum : Summable fun k => ‖F (t - u) k‖ := summable_norm_of_memHs (J : ℝ) hJd _ hmemJ
  have hcoef : coeffOf (propagator D μ u t φ) = F (t - u) := by
    rw [hprop]; exact coeffOf_toFun _ hreal hsum
  have hmemA : MemHs a (F (t - u)) := (hcA.1 (t - u) hτ).mono (by linarith)
  have hMS : MemSobolev a (propagator D μ u t φ) :=
    memSobolev_of_memHs a _ (ClassicalAux.memLp_two_of_continuous hpc) (by rw [hcoef]; exact hmemA)
  refine ⟨hMS, ?_⟩
  have e1 := (hsNormSq_coeffOf a _ hMS).2
  have e2 := (hsNormSq_coeffOf a φ hφa).2
  rw [hcoef] at e1
  have hsq : sobolevNorm a (propagator D μ u t φ) ^ 2 ≤ (Real.exp (C * (t - u)) * sobolevNorm a φ) ^ 2 := by
    rw [← e1, mul_pow, ← e2, ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (C * (t - u)) = 2 * C * (t - u) := by push_cast; ring
    rw [this]
    exact hen
  exact le_of_sq_le_sq hsq (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))

end HRS.Uniform.Q54
