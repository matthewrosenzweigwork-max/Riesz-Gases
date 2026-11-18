import HRS.MS.AdjFarAux1
import HRS.MS.UlTail

/-!
# S8.5 `feature_decay`, part 1 (S85 packet): far-field estimates for the cancellation convolution, `0 ≤ s < d`

**Plan of the packet** (see also `S85_PLAN.md`; the frozen statement is `HRS.Whole.feature_decay`, S L6562-6574).

*Statement audit.*  TRUE and non-vacuous: `IsThermalEquilibrium d (d/2) a β ρβ` is inhabited and unique (pointwise), so
`∃ C, ∀ ρβ ...` is `∃ C` for one density.  No junk-value trap: `IsKFeature` is part of the conclusion; `convGradConvW` is the
genuine cancellation convolution for `s = d/2 < d` (for `d = 2` the force `∇g ~ |x|^{-2}` is not locally integrable, so the
plain integral of `far_derivatives_proof`, which needs `s ≤ d - 2` i.e. `d ≥ 4`, is NOT enough: the proof below uses the
cancellation operator `ultK` of `UlTail`, valid for all `0 ≤ s < d`); `propagatorW` is `Classical.choose`, so uniqueness
(`ulw_unique`) is used.  The decay exponent `p = s + 2` is sharp.  The row dependency "S5.4" is not used (growth weights, `s < d/2`).

*This file.*  The two far-field inputs of the S4.12 engine, for the cancellation convention and every `0 ≤ s < d`
(one extra derivative of the density / of `∇f` compared with `far_derivatives`, the price of the near-field cancellation):

* `s85_partA`: `h ∈ C^{k+1}` with `weightedSupE (k+1) L h < ⊤` gives `∇g*h ∈ C^k`, `‖∇g*h‖_{k,s+1} ≤ C ‖h‖_{k+1,L}`;
* `s85_partB`: for `f ∈ C_b^{k+2}`, the source `S = ∑_j (∇g * (ρ (Mᵀ∇f)_j))_j` (exactly the nonlocal term of `generatorW`)
  is `C^k` with `decayNormE k (s+1) S ≤ C ‖f‖_{C_b^{k+2}}`;
* `s85_drift_hyps`: the drift field `B = M ∇g*ρ` of the stationary dynamics satisfies the `LcHyp` bounds (order `k+1`).

Helper names carry the prefix `s85_`; namespace `HRS.MS.S85`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S85

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Adj

variable {d : ℕ}

/-- Part (a) for the cancellation convolution. -/
theorem s85_partA (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (k : ℕ) (L : ℝ)
    (hL : (d : ℝ) + k + s + 3 < L) :
    ∃ C : ℝ, ∀ h : Euc d → ℝ, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) h → weightedSupE (k + 1) L h < ⊤ →
      ContDiff ℝ (k : WithTop ℕ∞) (convGradConvW (rieszKernelGrad d s) h) ∧
        decayNormVecE k (s + 1) (convGradConvW (rieszKernelGrad d s) h) ≤
          ENNReal.ofReal C * weightedSupE (k + 1) L h := by
  have hd1 : 1 ≤ d := by omega
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hdL : (d : ℝ) < L := by linarith
  have hL0 : 0 ≤ L := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hker := fun i : Fin d => ult_ker_kap hs0 hsd i
  choose Ci hCi0 hCi using fun i : Fin d => ult_core hd1 (hker i) k hL
  have hC0 : 0 ≤ (∑ i, Ci i) * ((d : ℝ) ^ (k + 1) * 2 ^ L) :=
    mul_nonneg (Finset.sum_nonneg fun i _ => hCi0 i) (by positivity)
  refine ⟨(∑ i, Ci i) * ((d : ℝ) ^ (k + 1) * 2 ^ L), fun h hcd hfin => ?_⟩
  set Ar : ℝ := (weightedSupE (k + 1) L h).toReal with hAr
  have hAr0 : 0 ≤ Ar := ENNReal.toReal_nonneg
  have hwse : weightedSupE (k + 1) L h = ENNReal.ofReal Ar := (ENNReal.ofReal_toReal hfin.ne).symm
  have hΛ : ∀ j ≤ k + 1, ∀ (I : Fin j → Fin d) (x : Euc d),
      jbracket x ^ L * |partialDeriv I h x| ≤ Ar := by
    intro j hj I x
    have := u2_wse_bound (k := k + 1) (L := L) (h := h) (Λ := Ar) hwse.le j hj I x
    rwa [max_eq_left hAr0] at this
  have hA' : 0 ≤ (d : ℝ) ^ (k + 1) * 2 ^ L * Ar := by positivity
  have hdec : U2Dec (k + 1) L ((d : ℝ) ^ (k + 1) * 2 ^ L * Ar) h :=
    ⟨hcd, fun m hm y => u2_norm_le_of_partial hd1 hL0 hAr0 hΛ m hm y⟩
  have hfun : ∀ i : Fin d, (fun x => convGradConvW (rieszKernelGrad d s) h x i) =
      ultK (u2_kap d s i) h := fun i => funext fun x =>
    (ult_conv_comp hd1 hs0 hsd hdL hA' (ult_U2Dec_mono hdec (by omega : 1 ≤ k + 1)) x).2 i
  refine ⟨contDiff_euclidean.2 fun i => ?_, ?_⟩
  · rw [hfun i]; exact (hCi i _ h hA' hdec).1
  · unfold decayNormVecE
    refine iSup_le fun i => ?_
    rw [hfun i]
    have hb : (0 : ℝ) ≤ s + 1 := by linarith
    have h1 := u2_decayNormE_le (k := k) hb (F := ultK (u2_kap d s i) h)
      (B := Ci i * ((d : ℝ) ^ (k + 1) * 2 ^ L * Ar)) (mul_nonneg (hCi0 i) hA')
      (fun j hj x => by
        have := (hCi i _ h hA' hdec).2 j hj x
        simpa [mul_assoc] using this)
    refine h1.trans ?_
    rw [hwse, ← ENNReal.ofReal_mul hC0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle : Ci i ≤ ∑ i, Ci i :=
      Finset.single_le_sum (f := Ci) (fun i _ => hCi0 i) (Finset.mem_univ i)
    calc Ci i * ((d : ℝ) ^ (k + 1) * 2 ^ L * Ar)
        ≤ (∑ i, Ci i) * ((d : ℝ) ^ (k + 1) * 2 ^ L * Ar) :=
          mul_le_mul_of_nonneg_right hle hA'
      _ = (∑ i, Ci i) * ((d : ℝ) ^ (k + 1) * 2 ^ L) * Ar := by ring

/-- The nonlocal term of `generatorW` for a density `ρ` and a function `f`:
`S f = ∑_j (∇g * (ρ (Mᵀ∇f)_j))_j` (cancellation convention). -/
def s85S (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ρ f : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
    (fun y => ρ y * (Torus.matVec M.transpose (gradient f y)) j) x) j

/-- Part (b) for the cancellation convolution. -/
theorem s85_partB (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (k : ℕ) (L : ℝ)
    (hL : (d : ℝ) + k + s + 3 < L) (M : Matrix (Fin d) (Fin d) ℝ) (Λρ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) ρ →
      weightedSupE (k + 1) L ρ ≤ ENNReal.ofReal Λρ →
      ∀ f : Euc d → ℝ, MemCb (k + 2) f →
        ContDiff ℝ (k : WithTop ℕ∞) (s85S s M ρ f) ∧
        decayNormE k (s + 1) (s85S s M ρ f) ≤ ENNReal.ofReal (C * cbNorm (k + 2) f) := by
  have hd1 : 1 ≤ d := by omega
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hdL : (d : ℝ) < L := by linarith
  have hL0 : 0 ≤ L := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hker := fun i : Fin d => ult_ker_kap hs0 hsd i
  choose Ci hCi0 hCi using fun i : Fin d => ult_core hd1 (hker i) k hL
  let wv : Fin d → Euc d := fun i => WithLp.toLp 2 (fun l => M l i)
  set Aρ : ℝ := (d : ℝ) ^ (k + 1) * 2 ^ L * max Λρ 0 with hAρ
  have hAρ0 : 0 ≤ Aρ := by positivity
  refine ⟨∑ i, Ci i * (2 ^ (k + 1) * Aρ * ‖wv i‖), ?_, fun ρ hρ hwse f hf => ?_⟩
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hCi0 i) (by positivity)
  have hΛ : ∀ j ≤ k + 1, ∀ (I : Fin j → Fin d) (x : Euc d),
      jbracket x ^ L * |partialDeriv I ρ x| ≤ max Λρ 0 :=
    fun j hj I x => u2_wse_bound hwse j hj I x
  have hdecρ : U2Dec (k + 1) L Aρ ρ :=
    ⟨hρ, fun m hm y => u2_norm_le_of_partial hd1 hL0 (le_max_right _ _) hΛ m hm y⟩
  set cb : ℝ := cbNorm (k + 2) f with hcb
  have hcb0 : 0 ≤ cb := u2_cb_nonneg
  have hf1 : ContDiff ℝ (k + 1 + 1) f := by exact_mod_cast hf.1
  have hu : ∀ i, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun y => fderiv ℝ f y (wv i)) := fun i => by
    have h1 : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ f) :=
      hf1.fderiv_right (m := ((k + 1 : ℕ) : WithTop ℕ∞)) (by push_cast; exact le_refl _)
    exact h1.clm_apply (contDiff_const (c := wv i))
  have hub : ∀ i, ∀ m ≤ k + 1, ∀ y, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (wv i)) y‖ ≤
      ‖wv i‖ * cb := fun i m hm y =>
    (u2_fderiv_apply_bound hf1 (wv i) m hm y).trans
      (mul_le_mul_of_nonneg_left (u2_cb_le hf (m + 1) (by omega) y) (norm_nonneg _))
  have hdecG : ∀ i, U2Dec (k + 1) L (2 ^ (k + 1) * Aρ * (‖wv i‖ * cb))
      (fun y => ρ y * fderiv ℝ f y (wv i)) := fun i =>
    u2_prod_dec hdecρ hAρ0 (hu i) (mul_nonneg (norm_nonneg _) hcb0) (hub i)
  have hA_i : ∀ i, 0 ≤ 2 ^ (k + 1) * Aρ * (‖wv i‖ * cb) := fun i => by positivity
  have hS : s85S s M ρ f =
      fun x => ∑ i, ultK (u2_kap d s i) (fun y => ρ y * fderiv ℝ f y (wv i)) x := by
    funext x
    unfold s85S
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ∀ y, ρ y * (Torus.matVec M.transpose (gradient f y)) i = ρ y * fderiv ℝ f y (wv i) := by
      intro y
      rw [u2_matVec_apply, u2_fderiv_eq_sum]
    simp only [h1]
    exact (ult_conv_comp hd1 hs0 hsd hdL (hA_i i)
      (ult_U2Dec_mono (hdecG i) (by omega : 1 ≤ k + 1)) x).2 i
  rw [hS]
  refine ⟨?_, ?_⟩
  · exact ContDiff.sum fun i _ => (hCi i _ _ (hA_i i) (hdecG i)).1
  · have hCnn : 0 ≤ (∑ i, Ci i * (2 ^ (k + 1) * Aρ * ‖wv i‖)) * cb :=
      mul_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hCi0 i) (by positivity)) hcb0
    have := u2_decayNormE_le (k := k) (b := s + 1) (by linarith)
      (F := fun x => ∑ i, ultK (u2_kap d s i) (fun y => ρ y * fderiv ℝ f y (wv i)) x)
      hCnn (fun j hj x => by
        have hcd : ∀ i ∈ (Finset.univ : Finset (Fin d)), ContDiffAt ℝ (j : ℕ∞ω)
            (ultK (u2_kap d s i) (fun y => ρ y * fderiv ℝ f y (wv i))) x := fun i _ =>
          (((hCi i _ _ (hA_i i) (hdecG i)).1).of_le (by exact_mod_cast hj)).contDiffAt
        rw [iteratedFDeriv_fun_sum_apply hcd]
        refine (norm_sum_le _ _).trans ?_
        have hsum : ∑ i, ‖iteratedFDeriv ℝ j
            (ultK (u2_kap d s i) (fun y => ρ y * fderiv ℝ f y (wv i))) x‖ ≤
            ∑ i, (Ci i * (2 ^ (k + 1) * Aρ * (‖wv i‖ * cb))) * (1 + ‖x‖) ^ (-((s + 1) + (j : ℝ))) :=
          Finset.sum_le_sum fun i _ => by
            have := (hCi i _ _ (hA_i i) (hdecG i)).2 j hj x
            simpa [mul_assoc] using this
        refine hsum.trans (le_of_eq ?_)
        have hh : ∑ i, (Ci i * (2 ^ (k + 1) * Aρ * (‖wv i‖ * cb))) =
            (∑ i, Ci i * (2 ^ (k + 1) * Aρ * ‖wv i‖)) * cb := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [← Finset.sum_mul, hh])
    refine this.trans (le_of_eq ?_)
    rfl

/-- The drift hypotheses of the engine (`LcHyp`) for the field `B = M ∇g*ρ` (cancellation convention, `0 ≤ s < d`), order
`k + 1`; the density needs `k + 2` derivatives (the near-field cancellation costs one). -/
theorem s85_drift_hyps (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (k : ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (L Λ : ℝ) (hL : (d : ℝ) + k + s + 4 < L) :
    ∃ ΛB : ℝ, 0 ≤ ΛB ∧ ∀ ρ : Euc d → ℝ, ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞) ρ →
      weightedSupE (k + 2) L ρ ≤ ENNReal.ofReal Λ →
        ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
          (fun x => Torus.matVec M (convGradConvW (rieszKernelGrad d s) ρ x)) ∧
        (∀ j ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ j
            (fun x => Torus.matVec M (convGradConvW (rieszKernelGrad d s) ρ x)) x‖ ≤ ΛB) ∧
        decayNormVecE (k + 1) (s + 1)
          (fun x => Torus.matVec M (convGradConvW (rieszKernelGrad d s) ρ x)) ≤
          ENNReal.ofReal ΛB := by
  have hL' : (d : ℝ) + ((k + 1 : ℕ) : ℝ) + s + 3 < L := by push_cast; linarith
  obtain ⟨C, hC⟩ := s85_partA hd s hs0 hsd (k + 1) L hL'
  set C0 : ℝ := max C 0 with hC0
  set Λ0 : ℝ := max Λ 0 with hΛ0
  set Λ' : ℝ := C0 * Λ0 with hΛ'
  have hΛ'0 : 0 ≤ Λ' := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  set A : Euc d →L[ℝ] Euc d := (Matrix.toEuclideanLin M).toContinuousLinearMap with hA
  have hd1 : 1 ≤ d := by omega
  refine ⟨‖A‖ * ((d : ℝ) ^ (k + 1 + 1) * Λ'), by positivity, fun ρ hρsm hwse => ?_⟩
  have hlt : weightedSupE (k + 1 + 1) L ρ < ⊤ := lt_of_le_of_lt hwse ENNReal.ofReal_lt_top
  obtain ⟨hGc, hGd⟩ := hC ρ hρsm hlt
  have hGd' : decayNormVecE (k + 1) (s + 1) (convGradConvW (rieszKernelGrad d s) ρ) ≤
      ENNReal.ofReal Λ' := by
    refine hGd.trans ?_
    rw [hΛ', ENNReal.ofReal_mul (le_max_right _ _)]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      (hwse.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hmain := ad1_matVec_decay M hd1 (by linarith) hΛ'0 hGc hGd'
  exact_mod_cast hmain

end HRS.MS.S85
