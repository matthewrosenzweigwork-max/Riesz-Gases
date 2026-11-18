import HRS.MC.S7PIDVLipMat
import HRS.MC.S7PIEVcont

/-!
# Packet E213I1: translation-uniform leaf lemmas for the propagator matrix (Theorem 2.13)

The constants of the packet PI-E / PI-D leaves (`pie_level_bound`, `pie_finBd`, `pie_finBd_real`, `pie_Vbound`,
`S7PIDV_lip_coeff`, `S7PIDV_lip_fun`, `S7PIDV_lipMat`) are produced by `adjoint_torus_classical`,
`propagatorCoeff_spec` and `forwardGen_hsNorm_le` before the density path `μ`.  Here the same proofs are
restated with the constant obtained BEFORE `μ`: for a fixed `D`, bundle `(Rg, MB, Λ, VB, ν₀)` and horizon `G`,
the constant holds for every `μ` with `AdjointData D.s J Rg MB Λ VB D ν₀ G μ`.
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213I

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDV

variable {d : ℕ}

/-- integer-level bound for the propagator, constant before `μ` -/
lemma e213i_level_bound (hd : 1 ≤ d) (J : ℕ) (hJ : mStar d ≤ J) (D : DynData d)
    (Rg : PDE.Regime) (MB Λ VB ν₀ G : ℝ) (n : ℕ) (hn1 : 1 ≤ n) (hnJ : n ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : ℝ → Torus d → ℝ, AdjointData D.s J Rg MB Λ VB D ν₀ G μ →
      ∀ t ∈ Set.Ioc 0 G, ∀ u ∈ Set.Icc 0 t, ∀ φ : Torus d → ℝ, Dom J φ →
      MemSobolev (n : ℝ) (propagator D μ u t φ) ∧
        sobolevNorm (n : ℝ) (propagator D μ u t φ) ≤ C * sobolevNorm (n : ℝ) φ := by
  obtain ⟨C0, Cs, hC0, hCs, hmain⟩ := adjoint_torus_classical hd D.s D.hs0 D.hsd J hJ Rg MB Λ VB
  set lam : ℝ := Rg.lambdaM (Cs n) ν₀ (thetaOrder d D.s) with hlam
  refine ⟨Real.exp (|lam| * G), (Real.exp_pos _).le, fun μ hA t ht u hu φ hφ => ?_⟩
  obtain ⟨-, -, hb, -⟩ := hmain D ν₀ G μ hA t ht φ hφ.1 hφ.2
  obtain ⟨h1, h2⟩ := hb n hn1 hnJ u hu
  refine ⟨h1, h2.trans ?_⟩
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) ?_
  · calc lam * (t - u) ≤ |lam| * (t - u) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith [hu.2])
      _ ≤ |lam| * G := mul_le_mul_of_nonneg_left (by linarith [hu.1, ht.2]) (abs_nonneg _)
  · unfold sobolevNorm; exact Real.sqrt_nonneg _

/-- finite-section bound of the propagator matrix at an integer level, constant before `μ` -/
lemma e213i_finBd (hd : 1 ≤ d) (J : ℕ) (hJ : mStar d ≤ J) (D : DynData d)
    (Rg : PDE.Regime) (MB Λ VB ν₀ G : ℝ) (n : ℕ) (hn1 : 1 ≤ n) (hnJ : n ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : ℝ → Torus d → ℝ, AdjointData D.s J Rg MB Λ VB D ν₀ G μ →
      ∀ t ∈ Set.Ioc 0 G, ∀ u ∈ Set.Icc 0 t,
      pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) (n : ℝ)) C := by
  classical
  obtain ⟨C, hC, hbd0⟩ := e213i_level_bound hd J hJ D Rg MB Λ VB ν₀ G n hn1 hnJ
  refine ⟨C, hC, fun μ hA t ht u hu K J' x => ?_⟩
  have H : PIEHyp J D μ G := ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩
  have hbd := hbd0 μ hA
  set ξ : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-(n : ℝ)) * x k with hξ
  obtain ⟨hmem, hnorm⟩ := hbd t ht u hu (pieComb K ξ) (pieDom_comb J K ξ)
  have hpos : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  -- the rows
  have hrow : ∀ j : NonzeroLattice d, ∑ k ∈ K, pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
        (pieT D μ u t) (n : ℝ) j k * x k =
      Lattice.jp j.1 ^ (n : ℝ) * Torus.funRealCoeff (propagator D μ u t (pieComb K ξ)) j := by
    intro j
    rw [pie_coeff_comb H ht hu K ξ j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [pieWmat, hξ]
    have : Lattice.jp k.1 ^ (n : ℝ) * Lattice.jp k.1 ^ (-(n : ℝ)) = 1 := by
      rw [← Real.rpow_add (hpos k)]; simp
    have e1 : Lattice.jp j.1 ^ (n : ℝ) * pieT D μ u t j k * Lattice.jp k.1 ^ (-(n : ℝ)) * x k =
        Lattice.jp j.1 ^ (n : ℝ) * (Lattice.jp k.1 ^ (-(n : ℝ)) * x k * pieT D μ u t j k) := by ring
    exact e1
  simp_rw [hrow]
  obtain ⟨-, hsum⟩ := hmem
  set c : NonzeroLattice d → ℝ := fun j => Torus.funRealCoeff (propagator D μ u t (pieComb K ξ)) j with hc
  have h1 : ∑ j ∈ J', (Lattice.jp j.1 ^ (n : ℝ) * c j) ^ 2 ≤
      ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (2 * (n : ℝ)) * c j ^ 2 := by
    refine (Finset.sum_le_sum fun j _ => le_of_eq ?_).trans
      (hsum.sum_le_tsum J' fun j _ => mul_nonneg (Real.rpow_nonneg (hpos j).le _) (sq_nonneg _))
    rw [mul_pow, Torus.jp_rpow_sq]
  have h2 : ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (2 * (n : ℝ)) * c j ^ 2 ≤
      sobolevNorm (n : ℝ) (propagator D μ u t (pieComb K ξ)) ^ 2 := by
    unfold sobolevNorm
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (tsum_nonneg fun k =>
      mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)))]
    linarith [sq_nonneg (Torus.mean (propagator D μ u t (pieComb K ξ)))]
  have h3 : sobolevNorm (n : ℝ) (propagator D μ u t (pieComb K ξ)) ^ 2 ≤
      C ^ 2 * ∑ k ∈ K, x k ^ 2 := by
    have hnn : 0 ≤ sobolevNorm (n : ℝ) (propagator D μ u t (pieComb K ξ)) := by
      unfold sobolevNorm; exact Real.sqrt_nonneg _
    calc _ ≤ (C * sobolevNorm (n : ℝ) (pieComb K ξ)) ^ 2 := pow_le_pow_left₀ hnn hnorm 2
      _ = C ^ 2 * ∑ k ∈ K, x k ^ 2 := by
          rw [mul_pow, pieComb_sobolevNorm_sq]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [hξ]
          rw [mul_pow, Torus.jp_rpow_sq, ← mul_assoc, ← Real.rpow_add (hpos k)]
          simp
  exact h1.trans (h2.trans h3)


/-- finite-section bound at a real exponent between two integer levels, constant before `μ` -/
lemma e213i_finBd_real (hd : 1 ≤ d) (J : ℕ) (hJ : mStar d ≤ J) (D : DynData d)
    (Rg : PDE.Regime) (MB Λ VB ν₀ G : ℝ) (m : ℝ) (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (hJ' : n₀ + 1 ≤ J)
    (hm0 : (n₀ : ℝ) < m) (hm1 : m ≤ n₀ + 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ μ : ℝ → Torus d → ℝ, AdjointData D.s J Rg MB Λ VB D ν₀ G μ →
      ∀ t ∈ Set.Ioc 0 G, ∀ u ∈ Set.Icc 0 t,
      pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) m) A := by
  obtain ⟨C0, hC0, h0⟩ := e213i_finBd hd J hJ D Rg MB Λ VB ν₀ G n₀ hn₀ (by omega)
  obtain ⟨C1, hC1, h1⟩ := e213i_finBd hd J hJ D Rg MB Λ VB ν₀ G (n₀ + 1) (by omega) hJ'
  set θ : ℝ := m - n₀ with hθ
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  refine ⟨C0 ^ (1 - θ) * C1 ^ θ, mul_nonneg (Real.rpow_nonneg hC0 _) (Real.rpow_nonneg hC1 _),
    fun μ hA t ht u hu => ?_⟩
  have hw : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hint := pie_interp hw (T := pieT D μ u t) hC0 hC1 (h0 μ hA t ht u hu)
    (by simpa using h1 μ hA t ht u hu) hθ0 hθ1
  have hσ : (1 - θ) * (n₀ : ℝ) + θ * ((n₀ : ℝ) + 1) = m := by
    simp only [hθ]; ring
  rw [hσ] at hint
  exact hint

/-- uniform bound of `V^{t,u}` on `E_m`, constant before `μ` -/
theorem e213i_Vbound (hd : 1 ≤ d) (J : ℕ) (hJ : mStar d ≤ J) (D : DynData d)
    (Rg : PDE.Regime) (MB Λ VB ν₀ G : ℝ) (m : ℝ) (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (hJ' : n₀ + 1 ≤ J)
    (hm0 : (n₀ : ℝ) < m) (hm1 : m ≤ n₀ + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : ℝ → Torus d → ℝ, AdjointData D.s J Rg MB Λ VB D ν₀ G μ →
      ∀ t ∈ Set.Ioc 0 G, ∀ u ∈ Set.Icc 0 t, ∀ F : NegSobolev d m,
      ‖Vprop D μ m t u F‖ ≤ C * ‖F‖ := by
  obtain ⟨A, hA0, hA⟩ := e213i_finBd_real hd J hJ D Rg MB Λ VB ν₀ G m n₀ hn₀ hJ' hm0 hm1
  exact ⟨A, hA0, fun μ hμ t ht u hu F =>
    pie_Vbound_of_finBd D μ m t u hA0 (hA μ hμ t ht u hu) F⟩


/-- Coefficient-level time regularity with target `H^m`, constant before `μ`:
`‖F(τ) - φ‖_{H^m} ≤ K τ ‖φ‖_{H^{m+2}}`. -/
lemma e213i_lip_coeff (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (R : PDE.Regime)
    (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ μ : ℝ → Torus d → ℝ, AdjointData s (m + 2) R MB Λ VB D ν₀ T μ →
      ∀ t ∈ Set.Ioc 0 T, ∀ φc : Coeff d, MemHs ((m + 2 : ℕ) : ℝ) φc →
      ∀ τ ∈ Set.Icc 0 t, MemHs (m : ℝ) (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc τ - φc) ∧
        PDE.hsNorm (m : ℝ) (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc τ - φc) ≤
          K * τ * PDE.hsNorm ((m + 2 : ℕ) : ℝ) φc := by
  classical
  by_cases hex : ∃ μ₀ : ℝ → Torus d → ℝ, AdjointData s (m + 2) R MB Λ VB D ν₀ T μ₀
  swap
  · exact ⟨0, le_rfl, fun μ hA => absurd ⟨μ, hA⟩ hex⟩
  obtain ⟨μ₀, hA₀⟩ := hex
  obtain ⟨C, hC, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd (m + 2) (by omega) R MB Λ VB
  have hAm₀ := StabAux.adjointData_mono (by omega : m ≤ m + 2) hA₀
  obtain ⟨c, hc, hgen⟩ := MFAdjoint.forwardGen_hsNorm_le hd hs0 hsd m MB Λ VB D hA₀.hs hA₀.hM hAm₀.hV
  set lam : ℝ := R.lambdaM C ν₀ (thetaOrder d s) with hlam
  refine ⟨c * Real.exp (|lam| * T), mul_nonneg hc (Real.exp_pos _).le, fun μ hA t ht φc hφ τ hτ => ?_⟩
  have hAm := StabAux.adjointData_mono (by omega : m ≤ m + 2) hA
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

/-- Function-level time regularity with target `H^m`, constant before `μ`:
`‖U^{r,t}φ - φ‖_{H^m} ≤ K (t - r) ‖φ‖_{H^{m+2}}`. -/
lemma e213i_lip_fun (hd : 1 ≤ d) (D : DynData d) (Rg : PDE.Regime) (MB Λ VB ν₀ G : ℝ) (m : ℕ)
    (hm : 1 ≤ m) (hJ : mStar d ≤ m + 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ μ : ℝ → Torus d → ℝ, AdjointData D.s (m + 2) Rg MB Λ VB D ν₀ G μ →
      ∀ t ∈ Set.Ioc 0 G, ∀ r ∈ Set.Icc 0 t, ∀ φ : Torus d → ℝ, Dom (m + 2) φ →
      MemSobolev (m : ℝ) (fun x => propagator D μ r t φ x - φ x) ∧
        sobolevNorm (m : ℝ) (fun x => propagator D μ r t φ x - φ x) ≤
          K * (t - r) * sobolevNorm ((m + 2 : ℕ) : ℝ) φ := by
  classical
  have h3 := ClassicalPart.three_le_mStar d
  obtain ⟨K, hK, hlip0⟩ := e213i_lip_coeff hd D.hs0 D.hsd m hm Rg MB Λ VB D ν₀ G
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
  refine ⟨K, hK, fun μ hA t ht r hr φ hφ => ?_⟩
  have hlip := hlip0 μ hA
  obtain ⟨-, hpe, -, -⟩ := hmain D ν₀ G μ hA t ht φ hφ.1 hφ.2
  obtain ⟨hcm, -⟩ := hsNormSq_coeffOf (((m + 2 : ℕ) : ℝ)) φ hφ.2
  have hre : IsRealCoeff (coeffOf φ) :=
    isRealCoeff_coeffOf φ (ClassicalAux.integrable_of_continuous hφ.1)
  have hreal := ClassicalPart.propagatorCoeff_real hd D.s D.hs0 D.hsd (m + 2) (by omega) Rg MB Λ VB D ν₀ G μ hA
    t ht (coeffOf φ) hcm hre
  obtain ⟨Cp, hCp, hspec⟩ := propagatorCoeff_spec hd D.s D.hs0 D.hsd (m + 2) (by omega) Rg MB Λ VB
  obtain ⟨-, hw, -⟩ := hspec D ν₀ G μ hA t ht (coeffOf φ) hcm
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


/-- **Integer-level Lipschitz bound of the propagator matrix with the shifted weights**, constant before `μ`. -/
lemma e213i_lipMat (hd : 1 ≤ d) (J : ℕ) (D : DynData d) (Rg : PDE.Regime) (MB Λ VB ν₀ G : ℝ)
    (m : ℕ) (hm : 1 ≤ m) (hmJ : m + 2 ≤ J) (hst : mStar d ≤ m + 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ μ : ℝ → Torus d → ℝ, AdjointData D.s J Rg MB Λ VB D ν₀ G μ →
      ∀ u s t : ℝ, 0 ≤ u → u ≤ s → s ≤ t → t ≤ G →
      pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
        (fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) * (pieT D μ u t j k - pieT D μ u s j k))
        ((m + 2 : ℕ) : ℝ)) (K * (t - s)) := by
  classical
  have hJst : mStar d ≤ J := le_trans hst hmJ
  obtain ⟨K1, hK1, hlip0⟩ := e213i_lip_fun hd D Rg MB Λ VB ν₀ G m hm hst
  obtain ⟨C0, hC0, hlev0⟩ := e213i_level_bound hd J hJst D Rg MB Λ VB ν₀ G m hm (by omega)
  have hC1 : 0 ≤ max C0 1 := le_trans zero_le_one (le_max_right _ _)
  refine ⟨max C0 1 * K1, mul_nonneg hC1 hK1, fun μ hA u s t hu hus hst' htT => ?_⟩
  have H : PIEHyp J D μ G := ⟨hd, hJst, Rg, MB, Λ, VB, ν₀, hA⟩
  have hlip := hlip0 μ (StabAux.adjointData_mono hmJ hA)
  have hlev := hlev0 μ hA
  rcases hst'.eq_or_lt with rfl | hlt
  · intro Kf Jf x
    simp [pieWmat]
  have hs0 : 0 ≤ s := hu.trans hus
  have ht : t ∈ Set.Ioc 0 G := ⟨hs0.trans_lt hlt, htT⟩
  have hut : u ∈ Set.Icc 0 t := ⟨hu, hus.trans hlt.le⟩
  have hst'' : s ∈ Set.Icc 0 t := ⟨hs0, hlt.le⟩
  intro Kf Jf x
  obtain ⟨ξ, hξ⟩ : ∃ ξ : NonzeroLattice d → ℝ,
      ξ = fun k => Lattice.jp k.1 ^ (-((m + 2 : ℕ) : ℝ)) * x k := ⟨_, rfl⟩
  obtain ⟨φ, hφdef⟩ : ∃ φ : Torus d → ℝ, φ = pieComb Kf ξ := ⟨_, rfl⟩
  have hφJ : Dom J φ := by rw [hφdef]; exact pieDom_comb J Kf ξ
  have hφm : Dom (m + 2) φ := by rw [hφdef]; exact pieDom_comb (m + 2) Kf ξ
  obtain ⟨hmem1, hnorm1⟩ := hlip t ht s hst'' φ hφm
  have hφn : sobolevNorm ((m + 2 : ℕ) : ℝ) φ ^ 2 = ∑ k ∈ Kf, x k ^ 2 := by
    rw [hφdef, pieComb_sobolevNorm_sq]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hξ]
    rw [mul_pow, Torus.jp_rpow_sq, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1),
      show (2 * ((m + 2 : ℕ) : ℝ) + 2 * -((m + 2 : ℕ) : ℝ)) = 0 by ring, Real.rpow_zero, one_mul]
  have hnn : ∀ (σ : ℝ) (f : Torus d → ℝ), 0 ≤ sobolevNorm σ f := fun σ f => by
    unfold sobolevNorm; exact Real.sqrt_nonneg _
  obtain ⟨g, hgmem, hgrow, hgnorm⟩ : ∃ g : Torus d → ℝ, MemSobolev (m : ℝ) g ∧
      (∀ j, ∑ k ∈ Kf, (pieT D μ u t j k - pieT D μ u s j k) * ξ k = Torus.funRealCoeff g j) ∧
      sobolevNorm (m : ℝ) g ≤ max C0 1 * (K1 * (t - s) * sobolevNorm ((m + 2 : ℕ) : ℝ) φ) := by
    have e : (fun x => propagator D μ s t φ x - φ x) =
        fun x => 1 * propagator D μ s t φ x + (-1) * φ x := by funext x; ring
    rw [e] at hmem1 hnorm1
    have hψJ : Dom J (propagator D μ s t φ) := pie_prop_dom H ht hst'' hφJ
    have hψc : Continuous (propagator D μ s t φ) := hψJ.1
    rcases hs0.eq_or_lt with h0 | hpos
    · -- s = 0, hence u = 0
      have hs_eq : s = 0 := h0.symm
      subst hs_eq
      have hu0 : u = 0 := le_antisymm hus hu
      subst hu0
      refine ⟨fun x => 1 * propagator D μ 0 t φ x + (-1) * φ x, hmem1, fun j => ?_, ?_⟩
      · have c1 : Torus.funRealCoeff (propagator D μ 0 t φ) j = ∑ k ∈ Kf, ξ k * pieT D μ 0 t j k := by
          rw [hφdef]; exact pie_coeff_comb H ht hut Kf ξ j
        have c2 : Torus.funRealCoeff φ j = ∑ k ∈ Kf, ξ k * pieT D μ 0 0 j k := by
          rw [hφdef, pieComb_coeff]
          simp only [S7PIDV_pieT_zero H, mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite_eq]
        rw [pie_funRealCoeff_lin hψc hφJ.1, c1, c2, one_mul, neg_one_mul, ← sub_eq_add_neg,
          ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      · calc sobolevNorm (m : ℝ) (fun x => 1 * propagator D μ 0 t φ x + (-1) * φ x)
            ≤ K1 * (t - 0) * sobolevNorm ((m + 2 : ℕ) : ℝ) φ := hnorm1
          _ ≤ max C0 1 * (K1 * (t - 0) * sobolevNorm ((m + 2 : ℕ) : ℝ) φ) := by
              have h0' : 0 ≤ K1 * (t - 0) * sobolevNorm ((m + 2 : ℕ) : ℝ) φ :=
                mul_nonneg (mul_nonneg hK1 (by linarith [ht.1])) (hnn _ _)
              nlinarith [le_max_right C0 1]
    · have hs : s ∈ Set.Ioc 0 G := ⟨hpos, hlt.le.trans htT⟩
      have hu' : u ∈ Set.Icc 0 s := ⟨hu, hus⟩
      have hχJ : Dom J (fun x => 1 * propagator D μ s t φ x + (-1) * φ x) := dom_closed hψJ hφJ 1 (-1)
      obtain ⟨hmem2, hnorm2⟩ := hlev s hs u hu' _ hχJ
      refine ⟨propagator D μ u s (fun x => 1 * propagator D μ s t φ x + (-1) * φ x), hmem2,
        fun j => ?_, ?_⟩
      · have hsg : propagator D μ u t φ = propagator D μ u s (propagator D μ s t φ) :=
          pie_prop_semigroup H ht hφJ hu hus hlt
        have c1 : Torus.funRealCoeff (propagator D μ u t φ) j = ∑ k ∈ Kf, ξ k * pieT D μ u t j k := by
          rw [hφdef]; exact pie_coeff_comb H ht hut Kf ξ j
        have c2 : Torus.funRealCoeff (propagator D μ u s φ) j = ∑ k ∈ Kf, ξ k * pieT D μ u s j k := by
          rw [hφdef]; exact pie_coeff_comb H hs hu' Kf ξ j
        have c3 := pie_T_sub_coeff H hs hu' hψJ hφJ j
        rw [← c3, ← hsg, c1, c2, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      · calc sobolevNorm (m : ℝ) (propagator D μ u s
              (fun x => 1 * propagator D μ s t φ x + (-1) * φ x))
            ≤ max C0 1 * sobolevNorm (m : ℝ) (fun x => 1 * propagator D μ s t φ x + (-1) * φ x) :=
              hnorm2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hnn _ _))
          _ ≤ _ := mul_le_mul_of_nonneg_left hnorm1 hC1
  have hgn2 : sobolevNorm (m : ℝ) g ^ 2 ≤ (max C0 1 * K1 * (t - s)) ^ 2 * ∑ k ∈ Kf, x k ^ 2 := by
    calc sobolevNorm (m : ℝ) g ^ 2
        ≤ (max C0 1 * (K1 * (t - s) * sobolevNorm ((m + 2 : ℕ) : ℝ) φ)) ^ 2 :=
          pow_le_pow_left₀ (hnn _ _) hgnorm 2
      _ = (max C0 1 * K1 * (t - s)) ^ 2 * sobolevNorm ((m + 2 : ℕ) : ℝ) φ ^ 2 := by ring
      _ = _ := by rw [hφn]
  have hrow : ∀ j, ∑ k ∈ Kf, (fun j k => pieT D μ u t j k - pieT D μ u s j k) j k *
      (Lattice.jp k.1 ^ (-((m + 2 : ℕ) : ℝ)) * x k) = Torus.funRealCoeff g j := by
    intro j
    rw [← hgrow j, hξ]
  exact S7PIDV_finBd_tail m (fun j k => pieT D μ u t j k - pieT D μ u s j k) Kf Jf x g _ hgmem hrow hgn2


end HRS.MC.E213I

end
