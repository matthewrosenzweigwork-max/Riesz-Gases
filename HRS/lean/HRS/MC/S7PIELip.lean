import HRS.MC.S7PIEProp
import HRS.PDE.MeanFieldAdjointDuhamel

/-!
# Packet PI-E, part 5: quantitative time regularity of the propagator

`pie_lip_coeff`: at the coefficient level, `‖F(τ) - F(0)‖_{H^1} ≤ K τ ‖φ‖_{H^J}` for the forward solution
`F = propagatorCoeff` (terminal time `t ≤ T`), with `K` independent of `t, τ, φ`.  Route: `F(τ) - F(0)` is the
integral of the generator path, the generator maps `H^J → H^{J-2}` boundedly
(`DuhamelAux.forwardGen_hsNorm_le`), and a coefficient of an element of `H^{J-2}` decays like
`⟨k⟩^{-(J-2)}`; `J - 2 > d/2 + 1` makes the weighted sum finite.
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.PIE

open HRS HRS.PDE HRS.A33

variable {d : ℕ}

lemma pie_coord_bound {m : ℝ} {g : Coeff d} (hg : MemHs m g) {B : ℝ} (hB : PDE.hsNorm m g ≤ B) (k : Lattice d) :
    ‖g k‖ ≤ B / Real.sqrt (PDE.sobWeight m k) := by
  have hw : 0 < PDE.sobWeight m k := PDE.sobWeight_pos m k
  have hBnn : 0 ≤ B := le_trans (Real.sqrt_nonneg _) hB
  have h1 : PDE.sobWeight m k * ‖g k‖ ^ 2 ≤ PDE.hsNormSq m g := hg.le_tsum k (fun i _ =>
    mul_nonneg (PDE.sobWeight_pos m i).le (sq_nonneg _))
  have h2 : PDE.hsNormSq m g ≤ B ^ 2 := by
    have := PDE.hsNormSq_nonneg m g
    have h3 : Real.sqrt (PDE.hsNormSq m g) ≤ B := hB
    calc PDE.hsNormSq m g = Real.sqrt (PDE.hsNormSq m g) ^ 2 := (Real.sq_sqrt this).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 2
  rw [le_div_iff₀ (Real.sqrt_pos.2 hw)]
  have h4 : (‖g k‖ * Real.sqrt (PDE.sobWeight m k)) ^ 2 ≤ B ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hw.le]; nlinarith
  exact abs_le_of_sq_le_sq' h4 hBnn |>.2 |> fun h => by simpa using h

/-- Integral form of the time-Lipschitz bound in a weighted `ℓ²` norm: if `F τ = φ + ∫_0^τ G` coordinatewise and every
finite weighted section of `G σ` is bounded by `B²`, then `‖F τ - φ‖_{H^m} ≤ τ B`. -/
lemma pie_lip_abstract (m : ℝ) (F G : ℝ → Coeff d) (φ : Coeff d) {τ : ℝ} (hτ : 0 ≤ τ) {B : ℝ} (hB : 0 ≤ B)
    (hint : ∀ k, IntervalIntegrable (fun σ => G σ k) volume 0 τ)
    (hG : ∀ σ ∈ Set.Icc 0 τ, ∀ S : Finset (Lattice d), ∑ k ∈ S, PDE.sobWeight m k * ‖G σ k‖ ^ 2 ≤ B ^ 2)
    (heq : ∀ k, F τ k = φ k + ∫ σ in (0 : ℝ)..τ, G σ k) :
    MemHs m (F τ - φ) ∧ PDE.hsNorm m (F τ - φ) ≤ τ * B := by
  classical
  set v : Coeff d := F τ - φ with hv
  have hvk : ∀ k, v k = ∫ σ in (0 : ℝ)..τ, G σ k := fun k => by
    simp only [hv, Pi.sub_apply, heq k]; ring
  have hw : ∀ k : Lattice d, 0 ≤ PDE.sobWeight m k := fun k => (PDE.sobWeight_pos m k).le
  have key : ∀ S : Finset (Lattice d), ∑ k ∈ S, PDE.sobWeight m k * ‖v k‖ ^ 2 ≤ (τ * B) ^ 2 := by
    intro S
    set Q : ℝ := ∑ k ∈ S, PDE.sobWeight m k * ‖v k‖ ^ 2 with hQ
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (sq_nonneg _)
    -- Q as a complex number equals an integral
    have h1 : ((Q : ℝ) : ℂ) = ∫ σ in (0 : ℝ)..τ, ∑ k ∈ S, ((PDE.sobWeight m k : ℝ) : ℂ) *
        (starRingEnd ℂ (v k) * G σ k) := by
      rw [intervalIntegral.integral_finsetSum]
      · rw [hQ]; push_cast
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ← hvk k]
        rw [← mul_assoc, mul_comm ((PDE.sobWeight m k : ℝ) : ℂ), mul_assoc, Complex.conj_mul']
        push_cast; ring
      · intro k _
        exact ((hint k).const_mul (starRingEnd ℂ (v k))).const_mul _
    have h2 : ∀ σ ∈ Set.uIoc (0 : ℝ) τ, ‖∑ k ∈ S, ((PDE.sobWeight m k : ℝ) : ℂ) *
        (starRingEnd ℂ (v k) * G σ k)‖ ≤ Real.sqrt Q * B := by
      intro σ hσ
      have hσ' : σ ∈ Set.Icc 0 τ := by
        rw [Set.uIoc_of_le hτ] at hσ; exact ⟨hσ.1.le, hσ.2⟩
      refine (norm_sum_le _ _).trans ?_
      have e : ∀ k ∈ S, ‖((PDE.sobWeight m k : ℝ) : ℂ) * (starRingEnd ℂ (v k) * G σ k)‖ =
          (Real.sqrt (PDE.sobWeight m k) * ‖v k‖) * (Real.sqrt (PDE.sobWeight m k) * ‖G σ k‖) := by
        intro k _
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hw k)]
        have := Real.mul_self_sqrt (hw k)
        linear_combination (-(‖v k‖ * ‖G σ k‖)) * this
      rw [Finset.sum_congr rfl e]
      refine (Real.sum_mul_le_sqrt_mul_sqrt S _ _).trans ?_
      refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      · refine le_of_eq ?_
        rw [hQ]; congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_pow, Real.sq_sqrt (hw k)]
      · rw [show B = Real.sqrt (B ^ 2) from (Real.sqrt_sq hB).symm]
        exact Real.sqrt_le_sqrt (by
          refine le_trans (le_of_eq ?_) (hG σ hσ' S)
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_pow, Real.sq_sqrt (hw k)])
    have h3 := intervalIntegral.norm_integral_le_of_norm_le_const h2
    rw [← h1, Complex.norm_real, Real.norm_of_nonneg hQ0, sub_zero, abs_of_nonneg hτ] at h3
    have hs0 := Real.sqrt_nonneg Q
    have hsq := Real.sq_sqrt hQ0
    have : Real.sqrt Q ≤ τ * B := by
      by_contra hcon
      push_neg at hcon
      have hτB : 0 ≤ τ * B := mul_nonneg hτ hB
      nlinarith [mul_pos (lt_of_le_of_lt hτB hcon) (lt_of_le_of_lt hτB hcon)]
    calc Q = Real.sqrt Q ^ 2 := hsq.symm
      _ ≤ (τ * B) ^ 2 := pow_le_pow_left₀ hs0 this 2
  have hsum : Summable fun k => PDE.sobWeight m k * ‖v k‖ ^ 2 :=
    summable_of_sum_le (fun k => mul_nonneg (hw k) (sq_nonneg _)) key
  refine ⟨hsum, ?_⟩
  unfold PDE.hsNorm PDE.hsNormSq
  calc Real.sqrt (∑' k, PDE.sobWeight m k * ‖v k‖ ^ 2) ≤ Real.sqrt ((τ * B) ^ 2) :=
        Real.sqrt_le_sqrt (hsum.tsum_le_of_sum_le key)
    _ = τ * B := Real.sqrt_sq (mul_nonneg hτ hB)

/-- Coefficient-level time regularity: `‖F(τ) - φ‖_{H^1} ≤ K τ ‖φ‖_{H^{m+2}}`, with `K` independent of the terminal time
`t ≤ T`, of the datum and of `τ ∈ [0,t]`. -/
lemma pie_lip_coeff (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (R : PDE.Regime)
    (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s (m + 2) R MB Λ VB D ν₀ T μ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Ioc 0 T, ∀ φc : Coeff d, MemHs ((m + 2 : ℕ) : ℝ) φc →
      ∀ τ ∈ Set.Icc 0 t, MemHs 1 (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc τ - φc) ∧
        PDE.hsNorm 1 (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc τ - φc) ≤
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
      ∑ k ∈ S, PDE.sobWeight 1 k * ‖G σ k‖ ^ 2 ≤
        (c * Real.exp (|lam| * T) * PDE.hsNorm ((m + 2 : ℕ) : ℝ) φc) ^ 2 := by
    intro σ hσ S
    obtain ⟨hmem, hnorm⟩ := hGσ σ ⟨hσ.1, hσ.2.trans hτt⟩
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    calc ∑ k ∈ S, PDE.sobWeight 1 k * ‖G σ k‖ ^ 2
        ≤ ∑ k ∈ S, PDE.sobWeight (m : ℝ) k * ‖G σ k‖ ^ 2 :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (PDE.sobWeight_mono hm1 k) (sq_nonneg _)
      _ ≤ ∑' k, PDE.sobWeight (m : ℝ) k * ‖G σ k‖ ^ 2 :=
          hmem.sum_le_tsum S fun k _ => mul_nonneg (PDE.sobWeight_pos _ k).le (sq_nonneg _)
      _ = PDE.hsNorm (m : ℝ) (G σ) ^ 2 := by
          unfold PDE.hsNorm PDE.hsNormSq
          rw [Real.sq_sqrt (tsum_nonneg fun k => mul_nonneg (PDE.sobWeight_pos _ k).le (sq_nonneg _))]
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hnorm 2
  obtain ⟨h1, h2⟩ := pie_lip_abstract 1 F G φc hτ.1 hE hint hGs (fun k => hsol.eq k τ hτ)
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  ring

/-- Function-level time regularity of the propagator: `‖U^{r,t}φ - φ‖_{H^1} ≤ K (t - r) ‖φ‖_{H^J}`. -/
lemma pie_lip_fun {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Ioc 0 T, ∀ r ∈ Set.Icc 0 t, ∀ φ : Torus d → ℝ, Dom J φ →
      MemSobolev 1 (fun x => propagator D μ r t φ x - φ x) ∧
        sobolevNorm 1 (fun x => propagator D μ r t φ x - φ x) ≤ K * (t - r) * sobolevNorm (J : ℝ) φ := by
  classical
  obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
  have h3 := ClassicalPart.three_le_mStar d
  obtain ⟨m, rfl⟩ : ∃ m, J = m + 2 := ⟨J - 2, by omega⟩
  have hm : 1 ≤ m := by omega
  obtain ⟨K, hK, hlip⟩ := pie_lip_coeff hd D.hs0 D.hsd m hm Rg MB Λ VB D ν₀ T μ hA
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

end HRS.MC.Sec7.PIE

end
