import HRS.MS.SA12LimitL11
import HRS.MS.SA12LimitL1
import HRS.MS.SA12LimitL12
import HRS.MS.SA12LimitL16

/-!
# S.A.12 L13: localized negative-order time modulus of a forward weak solution
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12y_uloc_zero_le (m : ℕ) (χ : Euc d → ℝ) (u : Euc d → ℝ) :
    ulocNormE 0 χ u ≤ ulocNormE m χ u := by
  unfold ulocNormE
  refine iSup_mono fun z => ?_
  have := HRS.MS.UniqM1.sobolevNormE_zero_le (d := d) (r := (m : ℝ)) (Nat.cast_nonneg m)
    (fun x => χ (x - z) * u x)
  simpa using this

/-- The weak operator of a `C_c^∞` test is continuous. -/
theorem sa12y_weakOp_cont (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (m : ℕ) (hm : 1 ≤ m) (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T)
    (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) t) (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ) :
    Continuous (weakOp (D.coeff μ) t σ ψ) := by
  obtain ⟨hDs, -, -⟩ := hD.hs
  have hs0' : 0 ≤ D.s := by rw [hDs]; exact hs0
  have hsd' : D.s < d := by rw [hDs]; exact hsd
  have hμ : CoeffHypRd D.s m Λ T μ := by rw [hDs]; exact hD.hμ
  have hr : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  obtain ⟨hb1, -, -, -, -, -⟩ :=
    HRS.MS.UniqE1.e1_coeff hd hs0' hsd' m MB Λ ΛV G₀ hD.hM hD.hV hμ hr
  have hψ2 : ContDiff ℝ 2 ψ := hψ.1.of_le (by simp)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by simp)
  obtain ⟨K, -, hKc⟩ := test_nonlocal_decay hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD ψ hψ
  have hnl : Continuous (nonlocalTestRd (D.coeff μ) (t - σ) ψ) := (hKc (t - σ) hr).1
  have hlap : Continuous (Laplacian.laplacian ψ) := by
    have e : Laplacian.laplacian ψ = fun y => ∑ i, HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i ψ) y :=
      funext fun y => HRS.MS.UniqT3.lap_eq hψ2 y
    rw [e]
    exact continuous_finsetSum _ fun i _ => HRS.MS.UniqN2b.n2b_D1D1_cont hψ2 i i
  have hmov : Continuous (movDiv (fun y => ψ y • (D.coeff μ).drift (t - σ) y)) := by
    have hdr : (D.coeff μ).drift (t - σ) = meanFieldDriftW D (μ (t - σ)) := rfl
    rw [hdr]
    have hvc : ContDiff ℝ 1 (meanFieldDriftW D (μ (t - σ))) := contDiff_euclidean.2 hb1
    have hF1 : ContDiff ℝ 1 (fun y => ψ y • meanFieldDriftW D (μ (t - σ)) y) := hψ1.smul hvc
    unfold movDiv
    refine continuous_finsetSum _ fun i _ => ?_
    have := (hF1.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const (y := (EuclideanSpace.single i (1 : ℝ) : Euc d)))
    exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp this
  unfold weakOp
  exact ((continuous_const.mul hlap).sub hmov).sub hnl

/-- The weak term of a forward solution as the pairing with the weak operator. -/
theorem sa12y_fwt_eq {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {G : ℝ → Euc d → ℝ}
    (hG : IsForwardSolutionRd C t φ G) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) t) :
    forwardWeakTerm C t G ψ σ = ∫ x, G σ x * weakOp C t σ ψ x := by
  obtain ⟨-, k1, k2, k3⟩ := hG.integrable_x ψ hψ σ hσ
  unfold forwardWeakTerm weakOp
  have e : (fun x => G σ x * (C.ν * Laplacian.laplacian ψ x -
      movDiv (fun y => ψ y • C.drift (t - σ) y) x - nonlocalTestRd C (t - σ) ψ x)) =
      fun x => C.ν * (G σ x * Laplacian.laplacian ψ x) -
        G σ x * movDiv (fun y => ψ y • C.drift (t - σ) y) x -
          G σ x * nonlocalTestRd C (t - σ) ψ x := by
    funext x; ring
  have i1 : Integrable (fun x => C.ν * (G σ x * Laplacian.laplacian ψ x)) volume := k1.const_mul _
  have i12 : Integrable (fun x => C.ν * (G σ x * Laplacian.laplacian ψ x) -
      G σ x * movDiv (fun y => ψ y • C.drift (t - σ) y) x) volume := i1.sub k2
  rw [e, integral_sub i12 k3, integral_sub i1 k2, integral_const_mul]

/-- The time increment of the pairings is controlled by the weak operator size. -/
theorem sa12y_time_pair (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) {C : WholeCoeff d} {t : ℝ}
    {φ0 : Euc d → ℝ} {G : ℝ → Euc d → ℝ} (hG : IsForwardSolutionRd C t φ0 G) {B' : ℝ} (hB0 : 0 ≤ B')
    (hB : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (G τ) ≤ ENNReal.ofReal B') {ψ : Euc d → ℝ}
    (hψ : IsCcInfty ψ) {c : ℝ} (hc0 : 0 ≤ c)
    (hmeas : ∀ σ ∈ Icc (0 : ℝ) t, AEStronglyMeasurable (weakOp C t σ ψ) volume)
    (hcell : ∀ σ ∈ Icc (0 : ℝ) t, cellL2Sum (weakOp C t σ ψ) ≤ ENNReal.ofReal c) {τ σ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) t) (hσ : σ ∈ Icc (0 : ℝ) t) :
    |(∫ x, G τ x * ψ x) - ∫ x, G σ x * ψ x| ≤ B' * c * |τ - σ| := by
  have hbd : ∀ r ∈ Icc (0 : ℝ) t, ‖forwardWeakTerm C t G ψ r‖ ≤ B' * c := by
    intro r hr
    rw [sa12y_fwt_eq hG hψ hr, Real.norm_eq_abs]
    have h := (cell_pair_bound hd χ hχ B' hB0 (G r) (weakOp C t r ψ) (hB r hr) (hmeas r hr)
      ((hcell r hr).trans_lt ENNReal.ofReal_lt_top)).2
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hB0)
    exact ENNReal.toReal_le_of_le_ofReal hc0 (hcell r hr)
  have hint := hG.integrable_σ ψ hψ
  set f : ℝ → ℝ := forwardWeakTerm C t G ψ with hf
  have hII : ∀ a ∈ Icc (0 : ℝ) t, IntervalIntegrable f volume 0 a := fun a ha =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le ha.1).2
      (hint.mono_set (Icc_subset_Icc_right ha.2))
  have hconv : ∀ a ∈ Icc (0 : ℝ) t, ∫ r in Icc (0 : ℝ) a, f r = ∫ r in (0 : ℝ)..a, f r := fun a ha => by
    rw [intervalIntegral.integral_of_le ha.1, integral_Icc_eq_integral_Ioc]
  have e : (∫ x, G τ x * ψ x) - ∫ x, G σ x * ψ x = ∫ r in σ..τ, f r := by
    rw [hG.eq ψ hψ τ hτ, hG.eq ψ hψ σ hσ, hconv τ hτ, hconv σ hσ,
      add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left (hII τ hτ) (hII σ hσ)]
  rw [e, ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => hbd r ?_).trans (le_of_eq ?_)
  · have := Set.uIoc_subset_uIcc hr
    exact (Set.uIcc_subset_Icc hσ hτ) this
  · ring

-- BEGIN SA12.L13
theorem localized_negative_time (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (m : ℕ) (hm : 1 ≤ m) (MB Λ ΛV G₀ νbar T : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ) (G : ℝ → Euc d → ℝ)
    (hG : IsForwardSolutionRd (D.coeff μ) t φ G) (B : ℝ)
    (hB : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE m χ (G τ) ≤ ENNReal.ofReal B)
    (z : Euc d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Icc (0 : ℝ) t, ∀ σ ∈ Icc (0 : ℝ) t,
      sobolevNormE (-(mStar d : ℝ)) (fun x => χ (x - z) * (G τ x - G σ x)) ≤
        ENNReal.ofReal (K * |τ - σ|) := by
  set B' : ℝ := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hB0 : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (G τ) ≤ ENNReal.ofReal B' := fun τ hτ =>
    (sa12y_uloc_zero_le m χ _).trans ((hB τ hτ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  obtain ⟨K0, hK0, hK⟩ := localized_test_operator_bound hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T χ hχ D μ hD
    t ht z
  refine ⟨B' * K0, by positivity, fun τ hτ σ hσ => ?_⟩
  have hmem : ∀ τ ∈ Icc (0 : ℝ) t, MemLp (fun x => χ (x - z) * G τ x) 2 volume := by
    intro τ hτ
    have h : sobolevNormE (m : ℝ) (fun x => χ (x - z) * G τ x) ≤ ENNReal.ofReal B' :=
      (le_iSup (fun w : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - w) * G τ x) z).trans
        ((hB τ hτ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    exact HRS.MS.UniqM1.memLp_of_sobolevNormE_lt_top (h.trans_lt ENNReal.ofReal_lt_top)
  have hu : MemLp (fun x => χ (x - z) * (G τ x - G σ x)) 2 volume := by
    have e : (fun x => χ (x - z) * (G τ x - G σ x)) =
        fun x => χ (x - z) * G τ x - χ (x - z) * G σ x := funext fun x => by ring
    rw [e]
    exact (hmem τ hτ).sub (hmem σ hσ)
  refine HRS.MH.AdjointRd.Phase2SA12Limit.negative_norm_from_tests hd (mStar d : ℝ) (B' * K0 * |τ - σ|)
    (Nat.cast_nonneg _) (by positivity) _ hu ?_
  intro ψ hψ
  set φ' : Euc d → ℝ := fun x => χ (x - z) * ψ x with hφ'
  have hφ'c : IsCcInfty φ' :=
    ⟨(hχ.1.comp (contDiff_id.sub contDiff_const)).mul hψ.1, hψ.2.mul_left⟩
  set S : ℝ := HRS.PDE.ToolboxRd.sobolevNormSq (mStar d : ℝ) ψ with hS
  have hS0 : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  have e : (∫ x, χ (x - z) * (G τ x - G σ x) * ψ x) = (∫ x, G τ x * φ' x) - ∫ x, G σ x * φ' x := by
    rw [← integral_sub (hG.integrable_x φ' hφ'c τ hτ).1 (hG.integrable_x φ' hφ'c σ hσ).1]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hφ']
    ring
  have hcell : ∀ σ' ∈ Icc (0 : ℝ) t, cellL2Sum (weakOp (D.coeff μ) t σ' φ') ≤
      ENNReal.ofReal (K0 * Real.sqrt S) := by
    intro σ' hσ'
    refine (hK ψ hψ σ' hσ').trans (le_of_eq ?_)
    have e : sobolevNormE (mStar d : ℝ) ψ = ENNReal.ofReal (Real.sqrt S) := by
      unfold sobolevNormE
      rw [if_pos (sa12y_memSob hψ _)]
    rw [e, ← ENNReal.ofReal_mul hK0]
  have hmeas : ∀ σ' ∈ Icc (0 : ℝ) t, AEStronglyMeasurable (weakOp (D.coeff μ) t σ' φ') volume :=
    fun σ' hσ' => (sa12y_weakOp_cont hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD t ht σ' hσ' φ'
      hφ'c).aestronglyMeasurable
  have := sa12y_time_pair hd χ hχ hG hB'0 hB0 hφ'c (by positivity) hmeas hcell hτ hσ
  rw [e]
  calc _ ≤ B' * (K0 * Real.sqrt S) * |τ - σ| := this
    _ = _ := by ring
-- END SA12.L13

end HRS.MH.AdjointRd.Phase2SA12Limit
