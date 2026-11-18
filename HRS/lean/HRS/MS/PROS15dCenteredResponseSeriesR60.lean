import HRS.MS.PROS15dResolventSpectralSeriesR60
import HRS.MS.S21H2_S14aD3

/-!
# S15d: the frozen susceptibility is the spectral resolvent series on all L2 tests

For an actual centered-space Hilbert eigenbasis of the KRep operator,
the original frozen physical susceptibilityCov equals the full Parseval
spectral response series for arbitrary spatial L2 tests. The hypothesis
that S14a's exported eigenfunctions diagonalize this exact KRep remains
to be discharged separately.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory
open HRS.Whole HRS.Whole.Q34 HRS.MS.S111X2
open scoped RealInnerProductSpace
namespace HRS.MS.R26T3

theorem s15d_susceptibility_alltest_centered_eigenbasis_series
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    {g : HRS.Euc d → ℝ}
    {K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} {Mg : ℝ}
    (hK : KRep g μ K Mg) {θ : ℝ} (hθ : 0 ≤ θ)
    (b : HilbertBasis ℕ ℝ (s21h2_V μ))
    (lam : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (heig : ∀ j, K (((b j : s21h2_V μ) : Lp ℝ 2 μ)) =
      lam j • ((b j : s21h2_V μ) : Lp ℝ 2 μ))
    {f h : HRS.Euc d → ℝ} (hf : MemLp f 2 μ) (hh : MemLp h 2 μ) :
    HasSum (fun j => (1 + θ * lam j)⁻¹ *
      (inner ℝ (s111x2_cl hf) ((b j : s21h2_V μ) : Lp ℝ 2 μ) *
        inner ℝ ((b j : s21h2_V μ) : Lp ℝ 2 μ) (s111x2_cl hh)))
      (HRS.Whole.susceptibilityCov g μ θ f h) := by
  let x : Lp ℝ 2 μ := s111x2_cl hf
  let y : Lp ℝ 2 μ := s111x2_cl hh
  let z : Lp ℝ 2 μ := s111x2_Res hK.posOp hθ y
  have hxPc : Pc μ x = x := s111x2_cl_pc hf
  have hyPc : Pc μ y = y := s111x2_cl_pc hh
  have hx0 : inner ℝ (one2 μ) x = 0 := by
    calc
      inner ℝ (one2 μ) x = inner ℝ (one2 μ) (Pc μ x) := by rw [hxPc]
      _ = 0 := inner_one2_Pc x
  have hy0 : inner ℝ (one2 μ) y = 0 := by
    calc
      inner ℝ (one2 μ) y = inner ℝ (one2 μ) (Pc μ y) := by rw [hyPc]
      _ = 0 := inner_one2_Pc y
  have hzSpec : z + θ • K z = y := s111x2_Res_spec hK.posOp hθ y
  have hk0 : inner ℝ (one2 μ) (K z) = 0 := by
    calc
      inner ℝ (one2 μ) (K z) = inner ℝ (one2 μ) (Pc μ (K z)) := by rw [hK.pc]
      _ = 0 := inner_one2_Pc (K z)
  have hz0 : inner ℝ (one2 μ) z = 0 := by
    have hs := congrArg (fun w : Lp ℝ 2 μ => inner ℝ (one2 μ) w) hzSpec
    rw [inner_add_right, real_inner_smul_right, hk0, hy0] at hs
    simpa using hs
  have hxV : x ∈ s21h2_V μ := (s21h2_mem_V).2 hx0
  have hzV : z ∈ s21h2_V μ := (s21h2_mem_V).2 hz0
  have hParse := b.hasSum_inner_mul_inner
    (⟨x, hxV⟩ : s21h2_V μ)
    (⟨z, hzV⟩ : s21h2_V μ)
  have hParse' : HasSum
      (fun j => inner ℝ x (((b j : s21h2_V μ) : Lp ℝ 2 μ)) *
        inner ℝ (((b j : s21h2_V μ) : Lp ℝ 2 μ)) z)
      (inner ℝ x z) := by
    simpa only [Submodule.coe_inner] using hParse
  have hterm : ∀ j,
      inner ℝ (((b j : s21h2_V μ) : Lp ℝ 2 μ)) z =
        (1 + θ * lam j)⁻¹ *
          inner ℝ (((b j : s21h2_V μ) : Lp ℝ 2 μ)) y := by
    intro j
    have hs := s111x2_Res_symm hK.posOp hθ
      (((b j : s21h2_V μ) : Lp ℝ 2 μ)) y
    calc
      _ = inner ℝ (s111x2_Res hK.posOp hθ
          (((b j : s21h2_V μ) : Lp ℝ 2 μ))) y := hs.symm
      _ = _ := by
        rw [s15d_positive_resolvent_eigenvector hK.posOp hθ
          (hlam j) _ (heig j), real_inner_smul_left]
  rw [s111x2_susc_eq hK hθ hf hh]
  convert hParse' using 1
  funext j
  rw [hterm j]
  ring

#print axioms s15d_susceptibility_alltest_centered_eigenbasis_series
end HRS.MS.R26T3
