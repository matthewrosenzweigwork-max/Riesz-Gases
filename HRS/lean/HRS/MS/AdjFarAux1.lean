import HRS.MS.AdjConvAux1
import HRS.MS.LcWtAux3
import HRS.MS.SuppU2

/-!
# AD-1: drift hypotheses and source bound for S4.12 from `far_derivatives_proof` (S4.10)

Infrastructure for `adjoint_decay` (S4.12), new statements (not manuscript rows); `Adjoint.lean`,
`Dynamics.lean` are untouched.  Consumer: AD-3 (`adjoint_decay_proof`), which feeds the drift
`B_u = M ∇g*ρ_u` to `local_decay`/`lc_*` and the source `S_u = Div g*(ρ_u Mᵀ ∇f_u)` to the engine.

* `ad_drift_hyps_gen` / `ad_drift_hyps`: for `d ≥ 2`, `0 ≤ s ≤ d - 2`, `L > d + k + s + 4` there is a
  constant `ΛB`, depending only on `d, s, k, L, Λ, M` (quantified before `θ, Q, c, T, ν_*, K, ν, ρ`),
  such that for every family `ρ_t` (`t ∈ [0,T]`) of `C^{k+1}` functions with
  `weightedSupE (k+1) L (ρ_t) ≤ ofReal Λ`, the field `B_t x = M (∇g*ρ_t)(x)` (cancellation
  convention `convGradConvW`) is `C^{k+1}`, `‖D^j B_t‖ ≤ ΛB` (`j ≤ k+1`) and
  `decayNormVecE (k+1) (s+1) B_t ≤ ofReal ΛB`.  Together with joint continuity from `drift_cont`
  this is exactly the hypothesis block of `local_decay` / `LcHyp` on `[0,T]`.  `ad_drift_hyps` is the
  form with `AdjointDecayHyp` (the generic form needs only the `ρ`-bounds and `drift_cont`).
  The cancellation convention is identified with the plain integral by `ad_conv_plain`
  (the pointwise decay `|ρ_t y| ≤ A (1+‖y‖)^{-L}` comes from the weighted bound at order `0`).
* `ad_drift_eq`: the drift of `(D.coeff ρ)` is `B_t x - (Q x + c)`.
* `ad_source_bound`: for `u ≤ t ≤ T`, `φ` as in `adjoint_decay` and `f_u := propagatorW (D.coeff ρ) u t φ`
  (which is `C_b^{k+1}` with `cbNorm ≤ K ‖φ‖_ul` by `D.adjoint`), the source
  `S_u = Div g*(ρ_u Mᵀ ∇f_u)` (plain integral `divGConvPlain`) is `C^k` and
  `decayNormE k (s+1) S_u ≤ ofReal (C * (K * ‖φ‖_ul))`, with `C ≥ 0` depending only on
  `d, s, k, L, Λ, M` (uniform in `u ∈ [0,t]`, `ν`, `ρ`, `Q`, `c`, `θ`, `T`, `ν_*`).
  Here `‖φ‖_ul` is `(ulNormE (k+2+⌈d/2⌉) θ φ).toReal`, finite by hypothesis.

Differences from the sketch of `docs/S4_PLAN.md`: none in content; the lemma is stated for arbitrary
`0 ≤ u ≤ t ≤ T` (so it covers `u ∈ [r,t]`).  No junk values: the Bochner integrals are genuine
(absolutely convergent, `ad_conv_plain` needs `L > d`), and the ENNReal bounds are not trivial
(`decayNormVecE` of the actual field).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.Adj
open HRS HRS.Whole

variable {d : ℕ}

/-! ### Elementary lemmas -/

lemma ad1_one_le_jb (y : Euc d) : 1 ≤ jbracket y := by
  unfold jbracket
  exact Real.le_sqrt_of_sq_le (by nlinarith [norm_nonneg y])

/-- Monotonicity of the weighted sup norm in the derivative order. -/
lemma ad1_wse_mono (k : ℕ) (L : ℝ) (f : Euc d → ℝ) :
    weightedSupE k L f ≤ weightedSupE (k + 1) L f := by
  unfold weightedSupE derivSupE
  refine iSup_le fun j => iSup_le fun I => iSup_le fun x => ?_
  refine le_trans ?_ (le_iSup _ (⟨(j : ℕ), by omega⟩ : Fin (k + 1 + 1)))
  refine le_trans ?_ (le_iSup _ I)
  exact le_iSup (fun x => ENNReal.ofReal (jbracket x ^ L * |partialDeriv I f x|)) x

/-- A matrix applied to a vector field: weighted norm bounds on all derivatives. -/
lemma ad1_matVec_pt (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ} {σ Λ' : ℝ} (hd : 1 ≤ d) (_hσ : 0 ≤ σ)
    (hΛ' : 0 ≤ Λ') {G : Euc d → Euc d} (hG : ContDiff ℝ (m : WithTop ℕ∞) G)
    (h : decayNormVecE m σ G ≤ ENNReal.ofReal Λ') (j : ℕ) (hj : j ≤ m) (x : Euc d) :
    jbracket x ^ (σ + (j : ℝ)) *
      ‖iteratedFDeriv ℝ j (fun y => Torus.matVec M (G y)) x‖ ≤
      ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖ * ((d : ℝ) ^ (m + 1) * Λ') := by
  set A : Euc d →L[ℝ] Euc d := (Matrix.toEuclideanLin M).toContinuousLinearMap with hA
  have hF : (fun y => Torus.matVec M (G y)) = A ∘ G := rfl
  have h1 := HRS.MS.Lc.lc2_decay_op hΛ' hG h j hj x
  rw [hF, ContinuousLinearMap.iteratedFDeriv_comp_left A hG.contDiffAt (by exact_mod_cast hj)]
  have h2 : ‖A.compContinuousMultilinearMap (iteratedFDeriv ℝ j G x)‖ ≤
      ‖A‖ * ‖iteratedFDeriv ℝ j G x‖ := A.norm_compContinuousMultilinearMap_le _
  have hw : 0 ≤ jbracket x ^ (σ + (j : ℝ)) := Real.rpow_nonneg (u2_jb_pos x).le _
  have hdj : (d : ℝ) ^ (j + 1) ≤ (d : ℝ) ^ (m + 1) :=
    pow_le_pow_right₀ (by exact_mod_cast hd) (by omega)
  calc jbracket x ^ (σ + (j : ℝ)) * ‖A.compContinuousMultilinearMap (iteratedFDeriv ℝ j G x)‖
      ≤ jbracket x ^ (σ + (j : ℝ)) * (‖A‖ * ‖iteratedFDeriv ℝ j G x‖) :=
        mul_le_mul_of_nonneg_left h2 hw
    _ = ‖A‖ * (jbracket x ^ (σ + (j : ℝ)) * ‖iteratedFDeriv ℝ j G x‖) := by ring
    _ ≤ ‖A‖ * ((d : ℝ) ^ (j + 1) * Λ') := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ ‖A‖ * ((d : ℝ) ^ (m + 1) * Λ') :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdj hΛ') (norm_nonneg _)

lemma ad1_matVec_decay (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ} {σ Λ' : ℝ} (hd : 1 ≤ d)
    (hσ : 0 ≤ σ) (hΛ' : 0 ≤ Λ') {G : Euc d → Euc d} (hG : ContDiff ℝ (m : WithTop ℕ∞) G)
    (h : decayNormVecE m σ G ≤ ENNReal.ofReal Λ') :
    ContDiff ℝ (m : WithTop ℕ∞) (fun y => Torus.matVec M (G y)) ∧
    (∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j (fun y => Torus.matVec M (G y)) x‖ ≤
      ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖ * ((d : ℝ) ^ (m + 1) * Λ')) ∧
    decayNormVecE m σ (fun y => Torus.matVec M (G y)) ≤
      ENNReal.ofReal (‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖ * ((d : ℝ) ^ (m + 1) * Λ')) := by
  set A : Euc d →L[ℝ] Euc d := (Matrix.toEuclideanLin M).toContinuousLinearMap with hA
  have hF : (fun y => Torus.matVec M (G y)) = A ∘ G := rfl
  have hFc : ContDiff ℝ (m : WithTop ℕ∞) (fun y => Torus.matVec M (G y)) := by
    rw [hF]; exact A.contDiff.comp hG
  have hpt := ad1_matVec_pt M hd hσ hΛ' hG h
  refine ⟨hFc, fun j hj x => ?_, ?_⟩
  · have h1 := hpt j hj x
    have hw : 1 ≤ jbracket x ^ (σ + (j : ℝ)) :=
      Real.one_le_rpow (ad1_one_le_jb x) (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    calc ‖iteratedFDeriv ℝ j (fun y => Torus.matVec M (G y)) x‖
        = 1 * ‖iteratedFDeriv ℝ j (fun y => Torus.matVec M (G y)) x‖ := (one_mul _).symm
      _ ≤ _ := le_trans (mul_le_mul_of_nonneg_right hw (norm_nonneg _)) h1
  · unfold decayNormVecE
    refine iSup_le fun i => ?_
    unfold decayNormE derivSupE
    refine iSup_le fun j => iSup_le fun I => iSup_le fun x => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hj : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.2
    have hpd : |partialDeriv I (fun y => Torus.matVec M (G y) i) x| ≤
        ‖iteratedFDeriv ℝ (j : ℕ) (fun y => Torus.matVec M (G y)) x‖ := by
      have e1 : (fun y => Torus.matVec M (G y) i) =
          (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) ∘ (fun y => Torus.matVec M (G y)) := rfl
      have e2 : partialDeriv I (fun y => Torus.matVec M (G y) i) x =
          iteratedFDeriv ℝ (j : ℕ) (fun y => Torus.matVec M (G y)) x
            (fun l => EuclideanSpace.single (I l) 1) i := by
        unfold partialDeriv
        rw [e1, ContinuousLinearMap.iteratedFDeriv_comp_left _ (hFc.contDiffAt)
          (by exact_mod_cast hj)]
        rfl
      rw [e2]
      have h3 := PiLp.norm_apply_le
        (iteratedFDeriv ℝ (j : ℕ) (fun y => Torus.matVec M (G y)) x
          (fun l => EuclideanSpace.single (I l) 1)) i
      rw [Real.norm_eq_abs] at h3
      refine h3.trans ?_
      have h4 := (iteratedFDeriv ℝ (j : ℕ) (fun y => Torus.matVec M (G y)) x).le_opNorm
        (fun l => EuclideanSpace.single (I l) (1 : ℝ))
      have h5 : ∏ l, ‖(EuclideanSpace.single (I l) (1 : ℝ) : Euc d)‖ = 1 := by simp
      rw [h5, mul_one] at h4
      exact h4
    have hw : 0 ≤ jbracket x ^ (σ + ((j : ℕ) : ℝ)) := Real.rpow_nonneg (u2_jb_pos x).le _
    show jbracket x ^ (σ + ((j : ℕ) : ℝ)) * _ ≤ _
    exact (mul_le_mul_of_nonneg_left hpd hw).trans (hpt j hj x)

/-- The cancellation convention equals the plain integral for a `C^{k+1}` density with the weighted
bound (`L > d`). -/
lemma ad1_conv_eq_plain (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2) {k : ℕ}
    {L Λ : ℝ} (hL : (d : ℝ) < L) {h : Euc d → ℝ} (hh : ContDiff ℝ (k + 1) h)
    (hw : weightedSupE (k + 1) L h ≤ ENNReal.ofReal Λ) :
    convGradConvW (rieszKernelGrad d s) h = gradGConvPlain d s h := by
  have hL0 : 0 ≤ L := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hΛ : ∀ j ≤ 0, ∀ (I : Fin j → Fin d) (x : Euc d),
      jbracket x ^ L * |partialDeriv I h x| ≤ max Λ 0 :=
    fun j hj I x => u2_wse_bound hw j (by omega) I x
  have hbd : ∀ y, ‖h y‖ ≤ ((d : ℝ) ^ 0 * 2 ^ L * max Λ 0) * u2Wt L y := by
    intro y
    have := u2_norm_le_of_partial (by omega) (k := 0) hL0 (le_max_right Λ 0) hΛ 0 le_rfl y
    rwa [norm_iteratedFDeriv_zero] at this
  funext x
  exact ad_conv_plain hd hs0 hsd h
    (adlu_integrable_conv hd hs0 hsd (hh.continuous) hL (by positivity) hbd x)

/-! ### Step 3: drift hypotheses -/

/-- Generic form of the drift hypotheses (AD-1, step 3). -/
theorem ad_drift_hyps_gen (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2) (k : ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (L Λ : ℝ) (hL : (d : ℝ) + k + s + 4 < L) :
    ∃ ΛB : ℝ, 0 ≤ ΛB ∧ ∀ (T : ℝ) (ρ : ℝ → Euc d → ℝ),
      (∀ t ∈ Set.Icc 0 T, ContDiff ℝ (k + 1) (ρ t) ∧ weightedSupE (k + 1) L (ρ t) ≤ ENNReal.ofReal Λ) →
      ContinuousOn (fun p : ℝ × Euc d => convGradConvW (rieszKernelGrad d s) (ρ p.1) p.2)
        (Set.Icc 0 T ×ˢ Set.univ) →
      ContinuousOn (fun p : ℝ × Euc d =>
          Torus.matVec M (convGradConvW (rieszKernelGrad d s) (ρ p.1) p.2))
        (Set.Icc 0 T ×ˢ Set.univ) ∧
      ∀ t ∈ Set.Icc 0 T,
        ContDiff ℝ (k + 1) (fun x => Torus.matVec M (convGradConvW (rieszKernelGrad d s) (ρ t) x)) ∧
        (∀ j ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ j
            (fun x => Torus.matVec M (convGradConvW (rieszKernelGrad d s) (ρ t) x)) x‖ ≤ ΛB) ∧
        decayNormVecE (k + 1) (s + 1)
          (fun x => Torus.matVec M (convGradConvW (rieszKernelGrad d s) (ρ t) x)) ≤
          ENNReal.ofReal ΛB := by
  have hL' : (d : ℝ) + ((k + 1 : ℕ) : ℝ) + s + 3 < L := by push_cast; linarith
  obtain ⟨C, hC⟩ := (far_derivatives_proof hd s hs0 hsd (k + 1) L hL').1
  set C0 : ℝ := max C 0 with hC0
  set Λ0 : ℝ := max Λ 0 with hΛ0
  set Λ' : ℝ := C0 * Λ0 with hΛ'
  have hΛ'0 : 0 ≤ Λ' := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  set A : Euc d →L[ℝ] Euc d := (Matrix.toEuclideanLin M).toContinuousLinearMap with hA
  have hd1 : 1 ≤ d := by omega
  have hdL : (d : ℝ) < L := by
    have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  refine ⟨‖A‖ * ((d : ℝ) ^ (k + 1 + 1) * Λ'), by positivity, fun T ρ hρ hcont => ?_⟩
  refine ⟨A.continuous.comp_continuousOn hcont, fun t ht => ?_⟩
  obtain ⟨hρsm, hwse⟩ := hρ t ht
  have hρsm' : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (ρ t) := by exact_mod_cast hρsm
  have hlt : weightedSupE (k + 1) L (ρ t) < ⊤ := lt_of_le_of_lt hwse ENNReal.ofReal_lt_top
  obtain ⟨hGc, hGd⟩ := hC (ρ t) hρsm' hlt
  have hGd' : decayNormVecE (k + 1) (s + 1) (gradGConvPlain d s (ρ t)) ≤ ENNReal.ofReal Λ' := by
    refine hGd.trans ?_
    rw [hΛ', ENNReal.ofReal_mul (le_max_right _ _)]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      (hwse.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have heq := ad1_conv_eq_plain hd hs0 hsd hdL hρsm hwse
  have hmain := ad1_matVec_decay M hd1 (by linarith) hΛ'0 hGc hGd'
  rw [heq]
  exact_mod_cast hmain

/-- Step 3 (AD-1) in the hypotheses of `AdjointDecayHyp`: the constant `ΛB` depends only on
`d, s, k, L, Λ, M`. -/
theorem ad_drift_hyps (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2) (k : ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (L Λ : ℝ) (hL : (d : ℝ) + k + s + 4 < L) :
    ∃ ΛB : ℝ, 0 ≤ ΛB ∧ ∀ (θ : Euc d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (c : Euc d)
      (T νstar K ν : ℝ) (ρ : ℝ → Euc d → ℝ), AdjointDecayHyp θ s M Q c T νstar k L Λ K ν ρ →
      ContinuousOn (fun p : ℝ × Euc d =>
          Torus.matVec M (convGradConvW (rieszKernelGrad d s) (ρ p.1) p.2))
        (Set.Icc 0 T ×ˢ Set.univ) ∧
      ∀ t ∈ Set.Icc 0 T,
        ContDiff ℝ (k + 1) (fun x => Torus.matVec M (convGradConvW (rieszKernelGrad d s) (ρ t) x)) ∧
        (∀ j ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ j
            (fun x => Torus.matVec M (convGradConvW (rieszKernelGrad d s) (ρ t) x)) x‖ ≤ ΛB) ∧
        decayNormVecE (k + 1) (s + 1)
          (fun x => Torus.matVec M (convGradConvW (rieszKernelGrad d s) (ρ t) x)) ≤
          ENNReal.ofReal ΛB := by
  obtain ⟨ΛB, hΛB, h⟩ := ad_drift_hyps_gen hd s hs0 hsd k M L Λ hL
  refine ⟨ΛB, hΛB, fun θ Q c T νstar K ν ρ D => ?_⟩
  exact h T ρ (fun t ht => ⟨(D.density t ht).2.1, (D.density t ht).2.2⟩) D.drift_cont

/-- The drift of the coefficients along `ρ` is `B_t x - (Q x + c)` with `B_t = M ∇g*ρ_t`. -/
theorem ad_drift_eq {θ : Euc d → ℝ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {c : Euc d}
    {T νstar : ℝ} {k : ℕ} {L Λ K ν : ℝ} {ρ : ℝ → Euc d → ℝ}
    (D : AdjointDecayHyp θ s M Q c T νstar k L Λ K ν ρ) (r : ℝ) (x : Euc d) :
    ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ).drift r x =
      Torus.matVec M (convGradConvW (rieszKernelGrad d s) (ρ r) x) - (Torus.matVec Q x + c) := by
  show meanFieldDriftW ⟨s, M, quadV Q c, ν⟩ (ρ r) x = _
  unfold meanFieldDriftW
  simp only
  rw [ad_gradient_quadV D.Q_symm]

/-! ### Step 4: the source -/

/-- Step 4 (AD-1): the source `S_u = Div g*(ρ_u Mᵀ ∇f_u)` of the equation for the adjoint solution
`f_u = U(u,t)φ`. -/
theorem ad_source_bound (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2) (k : ℕ)
    (M : Matrix (Fin d) (Fin d) ℝ) (L Λ : ℝ) (hL : (d : ℝ) + k + s + 4 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : Euc d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (c : Euc d)
      (T νstar K ν : ℝ) (ρ : ℝ → Euc d → ℝ), AdjointDecayHyp θ s M Q c T νstar k L Λ K ν ρ →
      ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ φ : Euc d → ℝ,
        ContDiff ℝ ((k + 2 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ →
        ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ < ⊤ →
        ContDiff ℝ k (fun x => divGConvPlain d s
          (fun y => ρ u y • Torus.matVec M.transpose (gradient
            (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) u t φ) y)) x) ∧
        decayNormE k (s + 1) (fun x => divGConvPlain d s
          (fun y => ρ u y • Torus.matVec M.transpose (gradient
            (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) u t φ) y)) x) ≤
          ENNReal.ofReal (C * (K * (ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ).toReal)) := by
  have hL' : (d : ℝ) + k + s + 3 < L := by linarith
  obtain ⟨C, hC⟩ := (far_derivatives_proof hd s hs0 hsd k L hL').2 M Λ
  refine ⟨max C 0, le_max_right _ _, fun θ Q c T νstar K ν ρ D u t hu hut htT φ hφ hul => ?_⟩
  have huT : u ∈ Set.Icc 0 T := ⟨hu, hut.trans htT⟩
  obtain ⟨_, hρsm, hwse⟩ := D.density u huT
  have hρk : ContDiff ℝ k (ρ u) := hρsm.of_le (by exact_mod_cast Nat.le_succ k)
  have hwk : weightedSupE k L (ρ u) ≤ ENNReal.ofReal Λ := (ad1_wse_mono k L _).trans hwse
  have e : k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ = k + 2 + ⌈(d : ℝ) / 2⌉₊ := by omega
  have hadj := D.adjoint u t hu hut htT φ (by rw [e]; exact hφ) (by rw [e]; exact hul)
  rw [e] at hadj
  obtain ⟨_, hmem, hcb⟩ := hadj
  obtain ⟨hS, hSd⟩ := hC (ρ u) hρk hwk _ hmem
  refine ⟨hS, hSd.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hcb0 : 0 ≤ cbNorm (k + 1) (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) u t φ) :=
    u2_cb_nonneg
  calc C * cbNorm (k + 1) (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) u t φ)
      ≤ max C 0 * cbNorm (k + 1) (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) u t φ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hcb0
    _ ≤ max C 0 * (K * (ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ).toReal) :=
        mul_le_mul_of_nonneg_left hcb (le_max_right _ _)

end HRS.MS.Adj
