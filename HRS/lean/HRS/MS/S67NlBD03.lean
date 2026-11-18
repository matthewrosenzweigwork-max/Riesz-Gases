import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovAdjAux12
import HRS.MS.S67NlBD02

/-!
# S6.7 nonlinear breakdown, packet 03: non-Schwartz physical converse ladder

`s67bd_ladder_converse`: for `u ∈ C¹` with `u, x_i u, ∂_i u ∈ Σ^r`, `u ∈ Σ^{r+1}` with the norm bound.
The coefficient of `x_i u + ∂_i u` is `√(2(α_i+1)) c_{α+e_i}(u)`; feed packet 02.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- Honest Euclidean coordinate derivative; every analytic use supplies regularity. -/
def s67bd_D (i : Fin d) (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  fderiv ℝ u x (EuclideanSpace.single i 1)

theorem s67bd_ladder_converse (d : ℕ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Euc d → ℝ, ContDiff ℝ 1 u → MemOsc r u →
      (∀ i : Fin d, MemOsc r (fun x => x i * u x)) →
      (∀ i : Fin d, MemOsc r (s67bd_D i u)) →
      MemOsc (r + 1) u ∧ oscNorm (r + 1) u ≤
        C * (oscNorm r u + ∑ i : Fin d,
          (oscNorm r (fun x => x i * u x) + oscNorm r (s67bd_D i u))) := by
  obtain ⟨C0, hC0, hconv⟩ := s67bd_coeff_converse d r
  refine ⟨Real.sqrt (2 * C0), Real.sqrt_nonneg _, fun u hu1 hu hx hD => ?_⟩
  have hl0 : ∀ α : MultiIndex d, 0 < oscEigenvalue d α := fun α => oscEv_pos α
  have hnn : ∀ (f : Euc d → ℝ) (α : MultiIndex d), 0 ≤ oscEigenvalue d α ^ r * hermiteCoeff f α ^ 2 :=
    fun f α => mul_nonneg (Real.rpow_nonneg (hl0 α).le _) (sq_nonneg _)
  have hsq : ∀ f : Euc d → ℝ, oscNorm r f ^ 2 = ∑' α, oscEigenvalue d α ^ r * hermiteCoeff f α ^ 2 :=
    fun f => Real.sq_sqrt (tsum_nonneg (hnn f))
  -- the raising coefficient is the sum of the two ladder coefficients
  have hR : ∀ (i : Fin d) (α : MultiIndex d),
      Real.sqrt (2 * ((α i : ℝ) + 1)) * hermiteCoeff u (mova1_up i α) =
        hermiteCoeff (fun x => x i * u x) α + hermiteCoeff (s67bd_D i u) α := by
    intro i α
    have h1 := s67_coeff_xmul_gen hu.1 i α
    have h2 := s67_coeff_partial_gen hu1 hu.1 i (hD i).1 α
    have h3 : Real.sqrt (2 * ((α i : ℝ) + 1)) = 2 * Real.sqrt (((α i : ℝ) + 1) / 2) := by
      rw [show 2 * ((α i : ℝ) + 1) = 2 ^ 2 * (((α i : ℝ) + 1) / 2) by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    have h2' : hermiteCoeff (s67bd_D i u) α = _ := h2
    rw [h1, h2', h3]
    ring
  have hRsq : ∀ (i : Fin d) (α : MultiIndex d),
      oscEigenvalue d α ^ r * (Real.sqrt (2 * ((α i : ℝ) + 1)) * hermiteCoeff u (mova1_up i α)) ^ 2 ≤
        2 * (oscEigenvalue d α ^ r * hermiteCoeff (fun x => x i * u x) α ^ 2 +
          oscEigenvalue d α ^ r * hermiteCoeff (s67bd_D i u) α ^ 2) := by
    intro i α
    rw [hR i α]
    have : (hermiteCoeff (fun x => x i * u x) α + hermiteCoeff (s67bd_D i u) α) ^ 2 ≤
        2 * (hermiteCoeff (fun x => x i * u x) α ^ 2 + hermiteCoeff (s67bd_D i u) α ^ 2) := by
      nlinarith [sq_nonneg (hermiteCoeff (fun x => x i * u x) α - hermiteCoeff (s67bd_D i u) α)]
    have h := mul_le_mul_of_nonneg_left this (Real.rpow_nonneg (hl0 α).le r)
    linarith
  have hsg : ∀ i : Fin d, Summable (fun α => oscEigenvalue d α ^ r *
      (Real.sqrt (2 * ((α i : ℝ) + 1)) * hermiteCoeff u (mova1_up i α)) ^ 2) := by
    intro i
    refine Summable.of_nonneg_of_le (fun α => ?_) (hRsq i) (((hx i).2.add (hD i).2).mul_left 2)
    exact mul_nonneg (Real.rpow_nonneg (hl0 α).le _) (sq_nonneg _)
  obtain ⟨hsumm, hbound⟩ := hconv (hermiteCoeff u) hu.2 hsg
  refine ⟨⟨hu.1, hsumm⟩, ?_⟩
  -- tsum bounds
  have hB : ∀ i : Fin d, ∑' α, oscEigenvalue d α ^ r *
      (Real.sqrt (2 * ((α i : ℝ) + 1)) * hermiteCoeff u (mova1_up i α)) ^ 2 ≤
      2 * (oscNorm r (fun x => x i * u x) ^ 2 + oscNorm r (s67bd_D i u) ^ 2) := by
    intro i
    rw [hsq, hsq, ← Summable.tsum_add (hx i).2 (hD i).2, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (hRsq i) (hsg i) (((hx i).2.add (hD i).2).mul_left 2)
  set a : Fin d → ℝ := fun i => oscNorm r (fun x => x i * u x) with ha
  set b : Fin d → ℝ := fun i => oscNorm r (s67bd_D i u) with hb
  set N0 : ℝ := oscNorm r u with hN0
  have ha0 : ∀ i, 0 ≤ a i := fun i => Real.sqrt_nonneg _
  have hb0 : ∀ i, 0 ≤ b i := fun i => Real.sqrt_nonneg _
  have hN00 : 0 ≤ N0 := Real.sqrt_nonneg _
  set S : ℝ := ∑ i : Fin d, (a i + b i) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => add_nonneg (ha0 i) (hb0 i)
  have hS2 : ∑ i : Fin d, (a i ^ 2 + b i ^ 2) ≤ S ^ 2 := by
    calc ∑ i : Fin d, (a i ^ 2 + b i ^ 2) ≤ ∑ i : Fin d, (a i + b i) ^ 2 :=
          Finset.sum_le_sum fun i _ => by nlinarith [mul_nonneg (ha0 i) (hb0 i)]
      _ ≤ S ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => add_nonneg (ha0 i) (hb0 i)
  have hsumB : ∑ i : Fin d, ∑' α, oscEigenvalue d α ^ r *
      (Real.sqrt (2 * ((α i : ℝ) + 1)) * hermiteCoeff u (mova1_up i α)) ^ 2 ≤
      2 * S ^ 2 := by
    calc _ ≤ ∑ i : Fin d, 2 * (a i ^ 2 + b i ^ 2) := Finset.sum_le_sum fun i _ => hB i
      _ = 2 * ∑ i : Fin d, (a i ^ 2 + b i ^ 2) := by rw [Finset.mul_sum]
      _ ≤ 2 * S ^ 2 := by linarith
  have hA : (∑' α, oscEigenvalue d α ^ r * hermiteCoeff u α ^ 2) = N0 ^ 2 := (hsq u).symm
  have htot : ∑' α, oscEigenvalue d α ^ (r + 1) * hermiteCoeff u α ^ 2 ≤
      (Real.sqrt (2 * C0) * (N0 + S)) ^ 2 := by
    refine hbound.trans ?_
    rw [hA, mul_pow, Real.sq_sqrt (by positivity)]
    have : N0 ^ 2 + ∑ i : Fin d, ∑' α, oscEigenvalue d α ^ r *
        (Real.sqrt (2 * ((α i : ℝ) + 1)) * hermiteCoeff u (mova1_up i α)) ^ 2 ≤
        2 * (N0 + S) ^ 2 := by
      nlinarith [mul_nonneg hN00 hS0]
    nlinarith
  unfold oscNorm
  have := Real.sqrt_le_sqrt htot
  rw [Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hN00 hS0))] at this
  exact this

end HRS.MS.BreakdownS67
