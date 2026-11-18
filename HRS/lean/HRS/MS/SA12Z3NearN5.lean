import HRS.MS.SA12Z3NearN5C

/-!
# S.A.12 N5 (SA12Z3): `weighted_matrix_hess`

For `Sym M ≤ 0`, `a ≥ 0` in `C²_b`, `u ∈ C²_c`:
`-∫ u matrixHess M (a u) ≤ C ‖a‖_{C²_b} ‖u‖²`.  Route: polarization of the Hessian into the `2 d²` directions
`e_i ± e_j`, the Fourier bridge `-∫ u (g * D_q² v) = B_q(u,v)` (`n3a_bridge`), the weighted symmetrization
`B_q(a u, u) = B_q(√a u, √a u) + E_q` with `|E_q| ≤ C_q ‖a‖ ‖u‖²` (`quadratic_toolbox_weighted`, Glaeser), and
the nonpositivity of the combined symbol `c (2π)² |ξ|^{s-d} ξᵀ M ξ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution Matrix

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3 HRS.MS.UniqN3a HRS.MS.UniqN3c
  HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.PDE.ToolboxRd.WeightAux

variable {d : ℕ}

theorem weighted_matrix_hess (d : ℕ) (hd : 1 ≤ d) (s MB : ℝ)
    (hs0 : 0 ≤ s) (hs2 : (d : ℝ)-2<s) (hsd : s<d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ,
      PDE.MatBound MB M → Torus.SymNonpos M →
      ∀ a : Euc d → ℝ, MemCb 2 a → (∀ x, 0 ≤ a x) →
      ∀ u : Euc d → ℝ, MemCb 2 u → HasCompactSupport u →
      Integrable (fun x => u x*matrixHess d s M (fun y => a y*u y) x) volume ∧
      -(∫ x, u x*matrixHess d s M (fun y => a y*u y) x) ≤
        C*cbNorm 2 a*(∫ x, u x^2) := by
  have hθ0 : 0 < s + 2 - d := by linarith
  have hθ2 : s + 2 - d < 2 := by linarith
  obtain ⟨c, hc, hbr⟩ := HRS.MS.UniqN3a.n3a_bridge hd hs0 (by linarith) hsd
  choose Cd hCd0 hCd using fun q : Euc d => sa12z3_dir_bound hd hs0 hs2 hsd hc q
  set K : ℝ := ∑ i : Fin d, ∑ j : Fin d, (Cd (sa12z3_dp d i j) + Cd (sa12z3_dm d i j)) with hK
  have hK0 : 0 ≤ K :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => add_nonneg (hCd0 _) (hCd0 _)
  have hCpos : 0 < 1 + |MB| * K / 4 := by
    have := div_nonneg (mul_nonneg (abs_nonneg MB) hK0) (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  refine ⟨1 + |MB| * K / 4, hCpos, fun M hM hSN a ha h0 u hu huc => ?_⟩
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  have hu2 : ContDiff ℝ 2 u := by simpa using hu.1
  have hv : ContDiff ℝ 2 (fun y => a y * u y) := ha2.mul hu2
  have hvc : HasCompactSupport (fun y => a y * u y) := huc.mul_left
  set v : Euc d → ℝ := fun y => a y * u y with hvdef
  have hL2 : MemLp u 2 volume := hu2.continuous.memLp_of_hasCompactSupport huc
  -- integrability
  have hcontH : Continuous (matrixHess d s M v) := by
    have : matrixHess d s M v = fun x => ∑ i, ∑ j, M j i * hessRiesz d s i j v x := rfl
    rw [this]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    have hf : hessRiesz d s i j v = fun y => D1 i (HRS.Whole.AppendixALemmas.kernelConvDeriv d s j v) y :=
      funext fun x => sa12z3_hess_eq hs0 hsd i j hv hvc x
    refine continuous_const.mul ?_
    rw [hf]
    exact HRS.MS.UniqN1c.n1c_D1_kcd_cont hs0 hsd hv hvc j i
  have hint : Integrable (fun x => u x * matrixHess d s M v x) volume :=
    (hu2.continuous.mul hcontH).integrable_of_hasCompactSupport huc.mul_right
  refine ⟨hint, ?_⟩
  -- the bridge
  have hI : ∀ q : Euc d, Integrable (fun x => u x * HRS.Whole.convFun (rieszKernel d s) (qq q v) x)
      volume := fun q => (hbr q u v hL2 hv hvc).1
  have hBq : ∀ q : Euc d, ∫ x, u x * HRS.Whole.convFun (rieszKernel d s) (qq q v) x =
      -symbolForm (mq c s q) u v := fun q => by
    have h : symbolForm (mq c s q) u v =
        -∫ x, u x * HRS.Whole.convFun (rieszKernel d s) (qq q v) x := (hbr q u v hL2 hv hvc).2.2
    rw [h, neg_neg]
  have hpt : ∀ x, u x * matrixHess d s M v x = (1 / 4 : ℝ) * ∑ i, ∑ j, M j i *
      (u x * HRS.Whole.convFun (rieszKernel d s) (qq (sa12z3_dp d i j) v) x -
        u x * HRS.Whole.convFun (rieszKernel d s) (qq (sa12z3_dm d i j) v) x) := by
    intro x
    rw [sa12z3_matrixHess_polar hs0 hsd M hv hvc x, mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hIj : ∀ i j : Fin d, Integrable (fun x => M j i *
      (u x * HRS.Whole.convFun (rieszKernel d s) (qq (sa12z3_dp d i j) v) x -
        u x * HRS.Whole.convFun (rieszKernel d s) (qq (sa12z3_dm d i j) v) x)) volume :=
    fun i j => ((hI _).sub (hI _)).const_mul _
  have hint_eq : ∫ x, u x * matrixHess d s M v x = (1 / 4 : ℝ) * ∑ i, ∑ j, M j i *
      ((∫ x, u x * HRS.Whole.convFun (rieszKernel d s) (qq (sa12z3_dp d i j) v) x) -
        (∫ x, u x * HRS.Whole.convFun (rieszKernel d s) (qq (sa12z3_dm d i j) v) x)) := by
    simp_rw [hpt]
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hIj i j)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hIj i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_sub (hI _) (hI _)]
  set Bp : Euc d → ℝ := fun q => symbolForm (mq c s q) u v with hBp
  have hY : -(∫ x, u x * matrixHess d s M v x) = (1 / 4 : ℝ) * ∑ i, ∑ j, M j i *
      (Bp (sa12z3_dp d i j) - Bp (sa12z3_dm d i j)) := by
    rw [hint_eq]
    simp_rw [hBq]
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hBp]; ring
  -- the weighted function
  set F : Euc d → ℝ := fun x => Real.sqrt (a x) * u x with hFdef
  obtain ⟨⟨Lw, hLw⟩, _⟩ := sa12z3_u_facts hu huc
  have hFL : HRS.PDE.ToolboxRd.IsLipschitz (Real.sqrt (cbNorm 2 a) * Lw +
      cbNorm 2 u * Real.sqrt (cbNorm 2 a)) F := by
    refine isLipschitz_mul (sa12z3_sqrt_lip ha h0) hLw
      (Bu := Real.sqrt (cbNorm 2 a)) (Bv := cbNorm 2 u) (fun x => ?_) (fun x => ?_)
    · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (le_trans (le_abs_self _) (sa12z3_cb2_bounds ha x).1)
    · exact (sa12z3_cb2_bounds hu x).1
  have hFc : HasCompactSupport F := huc.mul_left
  have hFH : HRS.PDE.ToolboxRd.MemSobolev ((s + 2 - d) / 2) F :=
    memSobolev_mono (by linarith) (HRS.MS.UniqT1.t1_memSobolev_one hFL hFc)
  have hm : ∀ q : Euc d, IsHomogSymbol (s + 2 - d) (mq c s q) :=
    fun q => n3c_mq_homog hd hs0 hs2 hsd hc q
  have hFint : ∀ q : Euc d, Integrable (fun ξ => mq c s q ξ * ‖fourierL2 F ξ‖ ^ 2) volume :=
    fun q => integrable_m_sq hθ0 (hm q) hFH
  set S : Euc d → ℝ := fun q => symbolForm (mq c s q) F F with hSdef
  have hnp : (1 / 4 : ℝ) * ∑ i, ∑ j, M j i * (S (sa12z3_dp d i j) - S (sa12z3_dm d i j)) ≤ 0 := by
    have hFj : ∀ i j : Fin d, Integrable (fun ξ => M j i * (mq c s (sa12z3_dp d i j) ξ * ‖fourierL2 F ξ‖ ^ 2 -
          mq c s (sa12z3_dm d i j) ξ * ‖fourierL2 F ξ‖ ^ 2)) volume :=
      fun i j => ((hFint _).sub (hFint _)).const_mul _
    have heq : (1 / 4 : ℝ) * ∑ i, ∑ j, M j i * (S (sa12z3_dp d i j) - S (sa12z3_dm d i j)) =
        ∫ ξ, (1 / 4 : ℝ) * ∑ i, ∑ j, M j i * (mq c s (sa12z3_dp d i j) ξ * ‖fourierL2 F ξ‖ ^ 2 -
          mq c s (sa12z3_dm d i j) ξ * ‖fourierL2 F ξ‖ ^ 2) := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hFj i j)]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ => hFj i j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, integral_sub (hFint _) (hFint _)]
      simp only [hSdef, symbolForm_self_eq]
    rw [heq]
    refine integral_nonpos fun ξ => ?_
    have hterm : ∀ i j : Fin d, (1 / 4 : ℝ) * (M j i * (mq c s (sa12z3_dp d i j) ξ * ‖fourierL2 F ξ‖ ^ 2 -
        mq c s (sa12z3_dm d i j) ξ * ‖fourierL2 F ξ‖ ^ 2)) =
        (c * (2 * Real.pi) ^ 2 * ‖ξ‖ ^ (s - d)) * (M j i * (ξ i * ξ j)) * ‖fourierL2 F ξ‖ ^ 2 := by
      intro i j
      have := sa12z3_mq_polar c s i j ξ
      calc (1 / 4 : ℝ) * (M j i * (mq c s (sa12z3_dp d i j) ξ * ‖fourierL2 F ξ‖ ^ 2 -
            mq c s (sa12z3_dm d i j) ξ * ‖fourierL2 F ξ‖ ^ 2))
          = M j i * ‖fourierL2 F ξ‖ ^ 2 * ((1 / 4 : ℝ) * (mq c s (sa12z3_dp d i j) ξ -
              mq c s (sa12z3_dm d i j) ξ)) := by ring
        _ = _ := by rw [this]; ring
    have hrw : (1 / 4 : ℝ) * ∑ i, ∑ j, M j i * (mq c s (sa12z3_dp d i j) ξ * ‖fourierL2 F ξ‖ ^ 2 -
          mq c s (sa12z3_dm d i j) ξ * ‖fourierL2 F ξ‖ ^ 2) =
        (c * (2 * Real.pi) ^ 2 * ‖ξ‖ ^ (s - d)) * (∑ i, ∑ j, M j i * (ξ i * ξ j)) *
          ‖fourierL2 F ξ‖ ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact hterm i j
    rw [hrw]
    have hP : 0 ≤ c * (2 * Real.pi) ^ 2 * ‖ξ‖ ^ (s - d) := by positivity
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hP (sa12z3_quad_nonpos hSN ξ))
      (sq_nonneg _)
  -- the errors
  set cb : ℝ := cbNorm 2 a with hcb
  have hcb0 : 0 ≤ cb := sa12z3_cb_nonneg ha
  have hI0 : 0 ≤ ∫ x, u x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hD : ∀ q : Euc d, |Bp q - S q| ≤ Cd q * cb * ∫ x, u x ^ 2 := fun q => by
    have h := hCd q a u ha h0 hu huc
    have e : Bp q = symbolForm (mq c s q) (fun x => a x * u x) u := symbolForm_comm _ _ _
    simp only [hSdef, hFdef]
    rw [e]
    exact h
  rw [hY]
  have hsplit : (1 / 4 : ℝ) * ∑ i, ∑ j, M j i * (Bp (sa12z3_dp d i j) - Bp (sa12z3_dm d i j)) =
      (1 / 4 : ℝ) * ∑ i, ∑ j, M j i * (S (sa12z3_dp d i j) - S (sa12z3_dm d i j)) +
      (1 / 4 : ℝ) * ∑ i, ∑ j, M j i * ((Bp (sa12z3_dp d i j) - S (sa12z3_dp d i j)) -
        (Bp (sa12z3_dm d i j) - S (sa12z3_dm d i j))) := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have herr : (1 / 4 : ℝ) * ∑ i, ∑ j, M j i * ((Bp (sa12z3_dp d i j) - S (sa12z3_dp d i j)) -
        (Bp (sa12z3_dm d i j) - S (sa12z3_dm d i j))) ≤
      |MB| * K / 4 * (cb * ∫ x, u x ^ 2) := by
    have hterm : ∀ i j : Fin d, M j i * ((Bp (sa12z3_dp d i j) - S (sa12z3_dp d i j)) -
        (Bp (sa12z3_dm d i j) - S (sa12z3_dm d i j))) ≤
        |MB| * ((Cd (sa12z3_dp d i j) + Cd (sa12z3_dm d i j)) * (cb * ∫ x, u x ^ 2)) := by
      intro i j
      have h1 := hD (sa12z3_dp d i j)
      have h2 := hD (sa12z3_dm d i j)
      have hMji : |M j i| ≤ |MB| := (hM j i).trans (le_abs_self MB)
      calc M j i * ((Bp (sa12z3_dp d i j) - S (sa12z3_dp d i j)) -
            (Bp (sa12z3_dm d i j) - S (sa12z3_dm d i j)))
          ≤ |M j i * ((Bp (sa12z3_dp d i j) - S (sa12z3_dp d i j)) -
            (Bp (sa12z3_dm d i j) - S (sa12z3_dm d i j)))| := le_abs_self _
        _ = |M j i| * |(Bp (sa12z3_dp d i j) - S (sa12z3_dp d i j)) -
            (Bp (sa12z3_dm d i j) - S (sa12z3_dm d i j))| := abs_mul _ _
        _ ≤ |MB| * ((Cd (sa12z3_dp d i j) * cb * ∫ x, u x ^ 2) +
            (Cd (sa12z3_dm d i j) * cb * ∫ x, u x ^ 2)) := by
            refine mul_le_mul hMji ((abs_sub _ _).trans (add_le_add h1 h2)) (abs_nonneg _)
              (abs_nonneg _)
        _ = _ := by ring
    have hsum : ∑ i, ∑ j, M j i * ((Bp (sa12z3_dp d i j) - S (sa12z3_dp d i j)) -
        (Bp (sa12z3_dm d i j) - S (sa12z3_dm d i j))) ≤
        ∑ i : Fin d, ∑ j : Fin d, |MB| * ((Cd (sa12z3_dp d i j) + Cd (sa12z3_dm d i j)) *
          (cb * ∫ x, u x ^ 2)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    have hsum' : ∑ i : Fin d, ∑ j : Fin d, |MB| * ((Cd (sa12z3_dp d i j) + Cd (sa12z3_dm d i j)) *
          (cb * ∫ x, u x ^ 2)) = |MB| * K * (cb * ∫ x, u x ^ 2) := by
      simp only [hK, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    calc (1 / 4 : ℝ) * ∑ i, ∑ j, M j i * ((Bp (sa12z3_dp d i j) - S (sa12z3_dp d i j)) -
          (Bp (sa12z3_dm d i j) - S (sa12z3_dm d i j)))
        ≤ (1 / 4 : ℝ) * (|MB| * K * (cb * ∫ x, u x ^ 2)) := by
          rw [← hsum']; exact mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = _ := by ring
  rw [hsplit]
  have hX0 : 0 ≤ cb * ∫ x, u x ^ 2 := mul_nonneg hcb0 hI0
  have hfin : |MB| * K / 4 * (cb * ∫ x, u x ^ 2) ≤
      (1 + |MB| * K / 4) * cb * ∫ x, u x ^ 2 := by
    nlinarith [hX0]
  linarith [hnp, herr, hfin]

end HRS.MH.AdjointRd.Phase2SA12Near
