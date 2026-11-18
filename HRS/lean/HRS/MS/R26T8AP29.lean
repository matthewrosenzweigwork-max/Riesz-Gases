import HRS.MS.R26T8AP29q
import HRS.MS.R26T8AP20
import HRS.MS.R26T8AP20b
import HRS.MS.R26T8AP23
import HRS.MS.R26T8AO00

/-!
# S8.2 T8A P29: `r26t8a_weighted_pair_corrector` (Pro contract, verbatim)
`Psi f = parametrixZero f + sym (pairInverseW U (remainder f))` with `U = s85_Ulim a β ρ M_U`.
Fields: P20 (conormal, canonical, Poisson up to the remainder), P23 (value/gradient/Hessian on `parametrixZero` by the
off-diagonal jet transfer P29j), P29d (`-pairA Psi_R = R`, jets), P29l (assembly), P29i (pairJ pole bound), P29q (linearity),
O00 (`aSource`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd HRS.MS.Wad

set_option maxHeartbeats 12800000 in
theorem r26t8a_weighted_pair_corrector
    (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∃ Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ,
        (∀ f g : Euc d → ℝ, ∀ A B : ℝ,
          TestBound (testOrder d) A f → TestBound (testOrder d) B g →
          ∀ c : ℝ, Psi (f + c • g) = Psi f + c • Psi g) ∧
        (∀ c : ℝ, Psi (fun _ => c) = 0) ∧
        ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f →
          PairCorrector a beta rho M (C * A) f (Psi f) ∧
          MemLp (aSource (HRS.Whole.withDensityReal rho) f) 2 (HRS.Whole.withDensityReal rho) ∧
          eLpNorm (aSource (HRS.Whole.withDensityReal rho) f) 2 (HRS.Whole.withDensityReal rho) ≤ ENNReal.ofReal (C * A) := by
  obtain ⟨chi, hchi⟩ := r26t8a_p10a_exists_cutoff d
  obtain ⟨C20, M20, hC20, hM20, h20⟩ := r26t8a_finite_parametrix d hd a beta ha hbeta chi hchi
  obtain ⟨C23, M23, hC23, hM23, h23⟩ := r26t8a_parametrix_sharp d hd a beta ha hbeta chi hchi
  set MU : ℝ := max M20 M23 + 1 with hMUdef
  have hMUpos : 0 < MU := by have := le_max_left M20 M23; rw [hMUdef]; linarith
  have hKMU : M20 < MU := by have := le_max_left M20 M23; rw [hMUdef]; linarith
  have hM23U : M23 ≤ MU + 2 := by have := le_max_right M20 M23; rw [hMUdef]; linarith
  obtain ⟨Cpsi, hCpsi, hpsi⟩ := r26t8a_p29_psi hd a beta M20 MU ha hbeta hMUpos hKMU
  obtain ⟨CJ, hCJ, hJ⟩ := r26t8a_p29_pairJ_bound d hd a beta MU ha hbeta hMUpos.le
  obtain ⟨C00, hC00, h00⟩ := r26t8a_aSource_bound d hd a beta ha hbeta
  set Cfin : ℝ := C23 + 2 * (Cpsi * C20) + (1 + CJ) * (C20 + 64 * (Cpsi * C20)) + C00 with hCfin
  have hp0 : 0 ≤ Cpsi * C20 := mul_nonneg hCpsi hC20
  have hCfin0 : 0 ≤ Cfin := by rw [hCfin]; positivity
  have hq0 : 0 ≤ C20 + 64 * (Cpsi * C20) := by positivity
  have hCJq : 0 ≤ CJ * (C20 + 64 * (Cpsi * C20)) := mul_nonneg hCJ hq0
  have hCf1 : C23 + 2 * (Cpsi * C20) ≤ Cfin := by rw [hCfin]; nlinarith
  have hCf2 : C20 + 64 * (Cpsi * C20) ≤ Cfin := by rw [hCfin]; nlinarith
  have hCf3 : CJ * (C20 + 64 * (Cpsi * C20)) ≤ Cfin := by rw [hCfin]; nlinarith
  have hCf4 : C00 ≤ Cfin := by rw [hCfin]; nlinarith
  refine ⟨Cfin, MU + 2, hCfin0, by linarith, fun rho hrho => ?_⟩
  set U := s85_Ulim a beta rho MU with hU
  set C0 := critCoeff d a beta rho with hC0
  set mu := HRS.Whole.withDensityReal rho with hmu
  refine ⟨fun f x y => r26t8a_parametrixZero C0 mu chi f x y +
      r26t8a_p29_sym (HRS.Whole.pairInverseW U (r26t8a_remainder C0 mu chi f)) x y, ?_, ?_, ?_⟩
  · -- linearity
    intro f g A B hf hg c
    have hk : 1 ≤ testOrder d := by unfold testOrder; omega
    have hA := r26t8a_p29_testBound_nonneg hk hf
    have hB := r26t8a_p29_testBound_nonneg hk hg
    obtain ⟨Qf, Rf, rfl, rfl, -, hcanf, -, -, hRcf, hRjf, -⟩ := h20 rho hrho f A hA hf
    obtain ⟨Qg, Rg, rfl, rfl, -, hcang, -, -, hRcg, hRjg, -⟩ := h20 rho hrho g B hB hg
    obtain ⟨hl1, hl2, -⟩ := r26t8a_parametrix_linear d hd a beta ha hbeta chi hchi rho hrho f g A B hA hB hf hg c
    exact r26t8a_p29_map_linear hd a beta M20 MU ha hbeta hMUpos hKMU rho hrho _ _ _ _ _ _ (C20 * A) (C20 * B)
      (mul_nonneg hC20 hA) (mul_nonneg hC20 hB) c hl1 hl2 hRcf hRcg hRjf hRjg hcanf hcang
  · -- constants
    intro b
    have hz : TestBound (testOrder d) 0 (fun _ : Euc d => (0 : ℝ)) := by
      refine ⟨contDiff_const, fun j hj _ x => ?_⟩
      have : iteratedFDeriv ℝ j (fun _ : Euc d => (0 : ℝ)) = 0 := iteratedFDeriv_fun_zero
      simp [this]
    obtain ⟨-, -, hcst⟩ := r26t8a_parametrix_linear d hd a beta ha hbeta chi hchi rho hrho _ _ 0 0 le_rfl le_rfl hz hz 0
    obtain ⟨h1, h2⟩ := hcst b
    exact r26t8a_p29_map_zero hd a beta M20 MU ha hbeta hMUpos hKMU rho hrho _ _ h1 h2
  · -- the corrector, the nonzero bound and the aSource clause
    intro f A hA hf
    obtain ⟨Q0, R, hQ0e, hRe, hQcan, hRcan, hsym, hQcon, hRc, hRj, hpois⟩ := h20 rho hrho f A hA hf
    have h23f := h23 rho hrho f A hA hf
    dsimp only at h23f
    have hQeq : ∀ x y, x ≠ y → r26t8a_parametrixZero C0 mu chi f x y = r26t8a_parametrix C0 mu chi f x y := by
      intro x y hxy; simp [r26t8a_parametrixZero, hxy]
    obtain ⟨hPcan, hPc, hPsym, hPj, hPpois⟩ := hpsi rho hrho R (C20 * A) (mul_nonneg hC20 hA) hRc hRj hRcan
      (fun x y => (hsym x y).2)
    subst hQ0e hRe
    have hpc := r26t8a_p29_fields hd a beta ha hbeta rho hrho hchi f
      (r26t8a_parametrixZero C0 mu chi f)
      (r26t8a_p29_sym (HRS.Whole.pairInverseW U (r26t8a_remainder C0 mu chi f)))
      (r26t8a_remainder C0 mu chi f)
      (A1 := C20 * A) (A2 := C23 * A) (B := Cpsi * (C20 * A)) (CJ := CJ) (Afin := Cfin * A)
      (M1 := M20) (MU := MU) (M2 := M23)
      (mul_nonneg hC20 hA) (mul_nonneg hC23 hA) (mul_nonneg hCpsi (mul_nonneg hC20 hA)) hCJ hKMU.le hM23U hMUpos.le
      hQcon hQcan (fun x y => (hsym x y).1) (fun x => by simp [r26t8a_parametrixZero])
      hpois
      (fun x y hxy => by
        rw [hQeq x y hxy]; exact (h23f x y hxy).1)
      (fun x y hxy => by
        rw [(r26t8a_p29_offdiag_grad hQeq x y hxy).1, (r26t8a_p29_offdiag_grad hQeq x y hxy).2]
        exact (h23f x y hxy).2.1)
      (fun x y hxy => by
        rw [r26t8a_p29_offdiag_iterated hQeq 2 x y hxy]; exact (h23f x y hxy).2.2)
      hPcan hPc hPsym hPj hPpois
      (fun G A' hA' hG x y hxy => hJ rho hrho G A' hA' hG x y hxy)
      (by have := mul_le_mul_of_nonneg_right hCf1 hA; nlinarith [this])
      (by have := mul_le_mul_of_nonneg_right hCf2 hA; nlinarith [this])
      (by have := mul_le_mul_of_nonneg_right hCf3 hA; nlinarith [this])
    obtain ⟨hMem, hLp⟩ := h00 rho hrho f A hA hf
    refine ⟨hpc, hMem, hLp.trans ?_⟩
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCf4 hA)

end HRS.MS.R26T8A

end
