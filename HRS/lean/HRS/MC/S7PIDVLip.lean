import HRS.MC.S7PIECont

/-!
# Packet PI-D, sub-packet V (helper): time Lipschitz bound of the propagator with target `H^{m'}`

`pie_lip_coeff` / `pie_lip_fun` (S7PIELip) give the target `H^1`; for the Hölder estimate of `V^{t,u}` from `E_{m-1}` to
`E_m` one needs the target `H^{m'}` with `m' ≥ 1` an integer and source `H^{m'+2}`:
`‖U^{r,t}φ - φ‖_{H^{m'}} ≤ K (t - r) ‖φ‖_{H^{m'+2}}`.  The proof is the one of `pie_lip_coeff` / `pie_lip_fun` with the weight
index `1` replaced by `m'` (the generator maps `H^{m'+2} → H^{m'}`, `forwardGen_hsNorm_le`).
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDV

open HRS HRS.PDE HRS.A33 HRS.MC.Sec7.PIE

variable {d : ℕ}

/-- Coefficient-level time regularity with target `H^m`: `‖F(τ) - φ‖_{H^m} ≤ K τ ‖φ‖_{H^{m+2}}`. -/
lemma S7PIDV_lip_coeff (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (R : PDE.Regime)
    (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s (m + 2) R MB Λ VB D ν₀ T μ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Ioc 0 T, ∀ φc : Coeff d, MemHs ((m + 2 : ℕ) : ℝ) φc →
      ∀ τ ∈ Set.Icc 0 t, MemHs (m : ℝ) (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc τ - φc) ∧
        PDE.hsNorm (m : ℝ) (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc τ - φc) ≤
          K * τ * PDE.hsNorm ((m + 2 : ℕ) : ℝ) φc := by
  classical
  obtain ⟨C, hC, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd (m + 2) (by omega) R MB Λ VB
  have hAm := StabAux.adjointData_mono (by omega : m ≤ m + 2) hA
  obtain ⟨c, hc, hgen⟩ := MFAdjoint.forwardGen_hsNorm_le hd hs0 hsd m MB Λ VB D hA.hs hA.hM hAm.hV
  set lam : ℝ := R.lambdaM C ν₀ (thetaOrder d s) with hlam
  refine ⟨c * Real.exp (|lam| * T), mul_nonneg hc (Real.exp_pos _).le, fun t ht φc hφ τ hτ => ?_⟩
  obtain ⟨hsol, hw, hb⟩ := hspec D ν₀ T μ hA t ht φc hφ
  set F := propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc with hF
  set G : ℝ → Coeff d := fun σ => forwardGen D (μ (t - σ)) (F σ) with hG
  have hτt : τ ≤ t := hτ.2
  have hn0 : 0 ≤ PDE.hsNorm ((m + 2 : ℕ) : ℝ) φc := Real.sqrt_nonneg _
  have hE : 0 ≤ c * Real.exp (|lam| * T) * PDE.hsNorm ((m + 2 : ℕ) : ℝ) φc :=
    mul_nonneg (mul_nonneg hc (Real.exp_pos _).le) hn0
  have hGσ : ∀ σ ∈ Set.Icc (0 : ℝ) t, MemHs (m : ℝ) (G σ) ∧
      PDE.hsNorm (m : ℝ) (G σ) ≤ c * Real.exp (|lam| * T) * PDE.hsNorm ((m + 2 : ℕ) : ℝ) φc := by
    intro σ hσ
    have hrT : t - σ ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
    obtain ⟨h1, h2⟩ := hgen (μ (t - σ)) (hAm.hμ.prob _ hrT) (hAm.hμ.smooth _ hrT) (hAm.hμ.bound _ hrT)
      (F σ) (hw.1 σ hσ)
    refine ⟨h1, h2.trans ?_⟩
    have hFb := hb σ hσ
    calc c * PDE.hsNorm ((m + 2 : ℕ) : ℝ) (F σ)
        ≤ c * (Real.exp (lam * σ) * PDE.hsNorm ((m + 2 : ℕ) : ℝ) φc) :=
          mul_le_mul_of_nonneg_left hFb hc
      _ ≤ c * (Real.exp (|lam| * T) * PDE.hsNorm ((m + 2 : ℕ) : ℝ) φc) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hn0) hc
          calc lam * σ ≤ |lam| * σ := mul_le_mul_of_nonneg_right (le_abs_self _) hσ.1
            _ ≤ |lam| * T := mul_le_mul_of_nonneg_left (by linarith [hσ.2, ht.2]) (abs_nonneg _)
      _ = _ := by ring
  have hint : ∀ k, IntervalIntegrable (fun σ => G σ k) MeasureTheory.volume 0 τ := fun k => by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
    exact (hsol.integrable k).mono_set (Set.Icc_subset_Icc_right hτt)
  have hGs : ∀ σ ∈ Set.Icc (0 : ℝ) τ, ∀ S : Finset (Lattice d),
      ∑ k ∈ S, PDE.sobWeight (m : ℝ) k * ‖G σ k‖ ^ 2 ≤
        (c * Real.exp (|lam| * T) * PDE.hsNorm ((m + 2 : ℕ) : ℝ) φc) ^ 2 := by
    intro σ hσ S
    obtain ⟨hmem, hnorm⟩ := hGσ σ ⟨hσ.1, hσ.2.trans hτt⟩
    calc ∑ k ∈ S, PDE.sobWeight (m : ℝ) k * ‖G σ k‖ ^ 2
        ≤ ∑' k, PDE.sobWeight (m : ℝ) k * ‖G σ k‖ ^ 2 :=
          hmem.sum_le_tsum S fun k _ => mul_nonneg (PDE.sobWeight_pos _ k).le (sq_nonneg _)
      _ = PDE.hsNorm (m : ℝ) (G σ) ^ 2 := by
          unfold PDE.hsNorm PDE.hsNormSq
          rw [Real.sq_sqrt (tsum_nonneg fun k => mul_nonneg (PDE.sobWeight_pos _ k).le (sq_nonneg _))]
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hnorm 2
  obtain ⟨h1, h2⟩ := pie_lip_abstract (m : ℝ) F G φc hτ.1 hE hint hGs (fun k => hsol.eq k τ hτ)
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  ring

/-- Function-level time regularity with target `H^m`: `‖U^{r,t}φ - φ‖_{H^m} ≤ K (t - r) ‖φ‖_{H^{m+2}}`. -/
lemma S7PIDV_lip_fun {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (m : ℕ) (hm : 1 ≤ m)
    (H : PIEHyp (m + 2) D μ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Ioc 0 T, ∀ r ∈ Set.Icc 0 t, ∀ φ : Torus d → ℝ, Dom (m + 2) φ →
      MemSobolev (m : ℝ) (fun x => propagator D μ r t φ x - φ x) ∧
        sobolevNorm (m : ℝ) (fun x => propagator D μ r t φ x - φ x) ≤
          K * (t - r) * sobolevNorm ((m + 2 : ℕ) : ℝ) φ := by
  classical
  obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
  have h3 := ClassicalPart.three_le_mStar d
  obtain ⟨K, hK, hlip⟩ := S7PIDV_lip_coeff hd D.hs0 D.hsd m hm Rg MB Λ VB D ν₀ T μ hA
  obtain ⟨C0, Cs, hC0, hCs, hmain⟩ := adjoint_torus_classical hd D.s D.hs0 D.hsd (m + 2) hJ Rg MB Λ VB
  have hmd : (d : ℝ) / 2 < ((m + 2 : ℕ) : ℝ) := by
    have := (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    have h4 : (3 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ m + 2)
    have h5 : (d : ℝ) / 2 < (mStar d : ℝ) := by
      unfold mStar
      have := Nat.lt_floor_add_one ((d : ℝ) / 2)
      push_cast; linarith
    have h6 : (mStar d : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast hJ
    linarith
  refine ⟨K, hK, fun t ht r hr φ hφ => ?_⟩
  obtain ⟨-, hpe, -, -⟩ := hmain D ν₀ T μ hA t ht φ hφ.1 hφ.2
  obtain ⟨hcm, -⟩ := hsNormSq_coeffOf (((m + 2 : ℕ) : ℝ)) φ hφ.2
  have hre : IsRealCoeff (coeffOf φ) :=
    isRealCoeff_coeffOf φ (ClassicalAux.integrable_of_continuous hφ.1)
  have hreal := ClassicalPart.propagatorCoeff_real hd D.s D.hs0 D.hsd (m + 2) (by omega) Rg MB Λ VB D ν₀ T μ hA
    t ht (coeffOf φ) hcm hre
  obtain ⟨Cp, hCp, hspec⟩ := propagatorCoeff_spec hd D.s D.hs0 D.hsd (m + 2) (by omega) Rg MB Λ VB
  obtain ⟨-, hw, -⟩ := hspec D ν₀ T μ hA t ht (coeffOf φ) hcm
  have hτ : t - r ∈ Set.Icc (0 : ℝ) t := ClassicalAux.mem_Icc_sub t hr
  set F := propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t (coeffOf φ) (t - r) with hF
  have hFm : MemHs (((m + 2 : ℕ) : ℝ)) F := hw.1 _ hτ
  have hFs : Summable fun k => ‖F k‖ := summable_norm_of_memHs _ hmd _ hFm
  have hφs : Summable fun k => ‖coeffOf φ k‖ := summable_norm_of_memHs _ hmd _ hcm
  have hdre : IsRealCoeff (F - coeffOf φ) := fun k => by
    have hF' : F (-k) = starRingEnd ℂ (F k) := hreal _ hτ k
    simp only [Pi.sub_apply, map_sub, hF', hre k]
  have hfun : (fun x => propagator D μ r t φ x - φ x) = toFun (F - coeffOf φ) := by
    have e1 : propagator D μ r t φ = toFun F := hpe r hr
    have e2 : toFun (F - coeffOf φ) = fun x => toFun F x - toFun (coeffOf φ) x :=
      ClassicalPart.toFun_sub_fun ((ClassicalPart.WS_zero_iff _).2 hFs) ((ClassicalPart.WS_zero_iff _).2 hφs)
    rw [e2, toFun_coeffOf φ hφ.1 hφs, e1]
  have hds : Summable fun k => ‖(F - coeffOf φ) k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_sub_le _ _) (hFs.add hφs)
  obtain ⟨h1, h2⟩ := hlip t ht (coeffOf φ) hcm (t - r) hτ
  obtain ⟨hS, hEq⟩ := ClassicalPart.memSobolev_toFun hds h1 hdre
  rw [hfun]
  refine ⟨hS, ?_⟩
  rw [hEq, ClassicalPart.sobolevNorm_eq_hsNorm hφ.2]
  exact h2

end HRS.MC.Sec7.S7PIDV

end
