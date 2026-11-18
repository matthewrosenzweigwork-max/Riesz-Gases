import HRS.MS.AdjDecayAux1
import HRS.MS.AdjFarAux1

/-!
# AD-3: `adjoint_decay_proof` (supplement S4.12)

`adjoint_decay_proof : type_of% @HRS.Whole.adjoint_decay` (the frozen statement, `HRS/Whole/Adjoint.lean`).

Route (S4_PLAN section 2.2, "verify, do not construct").  Let `f_u := propagatorW C u t φ` (`C = D.coeff ρ`),
the classical adjoint solution given by `UlAdjointInput` (`MemCb (k+1) f_u`, `cbNorm (k+1) f_u ≤ K ‖φ‖_ul`).
Its equation reads `∂_u f + νΔf + b_u·∇f = S_u` with `b_u = M(∇g*ρ_u) - Qx - c` and
`S_u = Div g*(ρ_u Mᵀ ∇f_u)` (`ad_generator_split_hyp`, `ad_drift_eq`).  The Ito/chain-rule verification
(`ad_verification_sg` for `ν > 0`, `ad3_verification_zero` for `ν = 0`) gives
`f_r x = lcSg r t φ x - ∫_r^t lcSg r u (S_u) x du` with the LC engine `lcSg`.  The engine `lc_engine` bounds the first
term by `C decayNormE k (s+1) φ`, and `ad3_int_engine` bounds the Duhamel integral (all derivatives, via
differentiation under the product integral `du ⊗ dP`) by `C ‖S‖` where `‖S_u‖_{k,s+1} ≤ C K ‖φ‖_ul` is
`ad_source_bound` (`far_derivatives_proof` (b) with `f = f_u`).  The data on `[0,T]` are clamped
(`lcHyp_clamp`, `lcDecay_clamp`) to satisfy the engine hypotheses for all times.

The conclusion constant is `max (max Ce (Ci * Cs * max K 0)) 1`, with `Ce` the engine constant, `Ci` the constant of
`ad3_int_engine`, `Cs` the constant of `ad_source_bound`; all depend only on `d, s, k, L, Λ, K, T, ν*, M, Q, c`
(and not on `ν, ρ, r, t, φ`).  Statement adjustments relative to the frozen file: none (`hk2` is not needed
by the proof).  Standing facts used: `0 ≤ s ≤ d - 2`, `L > d + k + s + 4`, `0 ≤ ν ≤ ν*` (the case in which
the hypothesis `AdjointDecayHyp` can hold at all; otherwise the statement is vacuous and `C = 0`).
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open HRS HRS.Whole HRS.MS.Lc HRS.MS.AdjVerif HRS.MS.Adj HRS.MS.PoisKolm HRS.MD.EQLawPath

noncomputable section

universe u

namespace HRS.MS.AdjDecay

variable {d : ℕ}

/-- The representation formula for every viscosity `ν ≥ 0` (`ad_verification_sg` if `ν > 0`,
`ad3_verification_zero` if `ν = 0`). -/
theorem ad3_representation {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ)
    (hW : IsBrownianFiltration P ℱ W) (Q : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) (Λc ΛB : ℝ)
    (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d) (H : LcHyp Q k Λc ΛB c B)
    (C : WholeCoeff d) (hν : 0 ≤ C.ν) {t : ℝ}
    (hdrift : ∀ u ∈ Icc 0 t, ∀ y, C.drift u y = B u y - lcQ Q y - c u)
    {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f)
    (S : ℝ → Euc d → ℝ)
    (hS : ∀ u ∈ Icc 0 t, ∀ y, generatorW C u (f u) y = C.ν * Laplacian.laplacian (f u) y +
      inner ℝ (C.drift u y) (gradient (f u) y) - S u y)
    {r : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (x : Euc d) :
    IntervalIntegrable (fun u => lcSg P W (fun _ => C.ν) Q c B r u (S u) x) volume r t ∧
    f r x = lcSg P W (fun _ => C.ν) Q c B r t φ x -
      ∫ u in r..t, lcSg P W (fun _ => C.ν) Q c B r u (S u) x := by
  rcases hν.eq_or_lt with h | h
  · exact ad3_verification_zero P ℱ W hW Q k Λc ΛB c B H C h.symm hdrift hf S hS hr hrt x
  · exact ad_verification_sg P ℱ W hW Q k Λc ΛB c B H C h hdrift hf S hS hr hrt x

/-- A single derivative term of `decayNormE` is bounded by the norm. -/
theorem ad3_term_le {k : ℕ} {b : ℝ} {g : Euc d → ℝ} {j : ℕ} (hj : j ≤ k) (I : Fin j → Fin d)
    (x : Euc d) :
    ENNReal.ofReal (jbracket x ^ (b + (j : ℝ)) * |partialDeriv I g x|) ≤ decayNormE k b g := by
  unfold decayNormE derivSupE
  refine le_trans ?_ (le_iSup _ (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (k + 1)))
  refine le_trans ?_ (le_iSup _ I)
  exact le_iSup (fun x => ENNReal.ofReal (jbracket x ^ (b + (j : ℝ)) * |partialDeriv I g x|)) x

/-- **S4.12 `adjoint_decay`**: proof (tie in `AdjDecayTie`). -/
theorem adjoint_decay_proof : type_of% @HRS.Whole.adjoint_decay := by
  intro d hd θ hθ s M Q c T νstar k hk2 L Λ K
  by_cases hrange : 0 ≤ s ∧ s ≤ (d : ℝ) - 2 ∧ (d : ℝ) + k + s + 4 < L
  swap
  · exact ⟨0, fun ν ρ D => absurd ⟨D.s_range.1, D.s_range.2, D.L_range⟩ hrange⟩
  obtain ⟨hs0, hsd, hL⟩ := hrange
  obtain ⟨ΛB, hΛB0, hΛB⟩ := ad_drift_hyps hd s hs0 hsd k M L Λ hL
  obtain ⟨Cs, hCs0, hCs⟩ := ad_source_bound hd s hs0 hsd k M L Λ hL
  have hb : (0 : ℝ) < s + 1 := by linarith
  obtain ⟨Ce, hCe⟩ := lc_engine.{0} s hs0 Q k T νstar (s + 1) ‖c‖ ΛB hb
  obtain ⟨Ci, hCi0, hCi⟩ := ad3_int_engine.{0} s hs0 Q k T νstar (s + 1) ‖c‖ ΛB hb
  set Cfin : ℝ := max (max Ce (Ci * Cs * max K 0)) 1 with hCfin
  have hCfin1 : 1 ≤ Cfin := le_max_right _ _
  have hCfin0 : 0 < Cfin := by linarith
  refine ⟨Cfin, fun ν ρ D r t hr hrt htT φ hφ hul => ?_⟩
  set C0 : WholeCoeff d := (⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ with hC0
  have hT0 : 0 ≤ T := hr.trans (hrt.trans htT)
  set ulE : ℝ≥0∞ := ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ with hulE
  have hkk : (k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) = k + 2 + ⌈(d : ℝ) / 2⌉₊ := by omega
  -- the adjoint input
  have hadj := D.adjoint r t hr hrt htT φ (by rw [hkk]; exact hφ) (by rw [hkk]; exact hul)
  rw [hkk] at hadj
  obtain ⟨hex, hmem, -⟩ := hadj
  have hCk : ContDiff ℝ (k : WithTop ℕ∞) (propagatorW C0 r t φ) :=
    hmem.1.of_le (by exact_mod_cast Nat.le_succ k)
  refine ⟨hCk, ?_⟩
  -- trivial case of an infinite norm of φ
  by_cases hdφ : decayNormE k (s + 1) φ = ⊤
  · rw [hdφ, top_add, ENNReal.mul_top (by simpa using hCfin0)]
    exact le_top
  have hdφ' : decayNormE k (s + 1) φ < ⊤ := lt_top_iff_ne_top.2 hdφ
  -- the terminal case
  rcases hrt.eq_or_lt with hrt0 | hlt
  · subst hrt0
    obtain ⟨f, hf⟩ := hex
    have hpt : propagatorW C0 r r φ = φ := by
      unfold propagatorW
      rw [dif_pos ⟨f, hf⟩]
      exact (Classical.choose_spec (⟨f, hf⟩ : ∃ f, IsClassicalAdjointW C0 r φ f)).terminal
    rw [hpt]
    calc decayNormE k (s + 1) φ ≤ decayNormE k (s + 1) φ + ulE := le_self_add
      _ = 1 * (decayNormE k (s + 1) φ + ulE) := (one_mul _).symm
      _ ≤ ENNReal.ofReal Cfin * (decayNormE k (s + 1) φ + ulE) := by
          gcongr
          simpa using hCfin1
  have ht : 0 < t := lt_of_le_of_lt hr hlt
  -- the classical solution
  have hf := hex.choose_spec
  set f : ℝ → Euc d → ℝ := hex.choose with hfdef
  have hprop : ∀ v, propagatorW C0 v t φ = f v := fun v => by
    unfold propagatorW
    rw [dif_pos hex]
  -- the data of the engine (clamped to `[0,T]`)
  obtain ⟨hcontB, hBsm⟩ := hΛB θ Q c T νstar K ν ρ D
  set Bu : ℝ → Euc d → Euc d := fun v y =>
    Torus.matVec M (convGradConvW (rieszKernelGrad d s) (ρ v) y) with hBu
  have hH : LcHyp Q k ‖c‖ ΛB (fun v => (fun _ : ℝ => c) (min v T)) (fun v => Bu (min v T)) :=
    lcHyp_clamp hT0 continuousOn_const hcontB (fun _ _ => le_rfl)
      (fun v hv => ⟨by exact_mod_cast (hBsm v hv).1, fun j hj x => (hBsm v hv).2.1 j hj x⟩)
  have hdec := lcDecay_clamp hT0 (fun v hv => (hBsm v hv).2.2)
  set c' : ℝ → Euc d := fun v => (fun _ : ℝ => c) (min v T) with hc'
  set B' : ℝ → Euc d → Euc d := fun v => Bu (min v T) with hB'
  -- drift identification
  have hdrift : ∀ v ∈ Icc 0 t, ∀ y, C0.drift v y = B' v y - lcQ Q y - c' v := by
    intro v hv y
    have hvT : v ∈ Icc 0 T := ⟨hv.1, hv.2.trans htT⟩
    rw [ad_drift_eq D v y]
    simp only [hB', hc', hBu, min_eq_left hvT.2, lcQ_apply]
    abel
  -- bounds on the gradient of f
  obtain ⟨B1, hB1⟩ := hf.bdd 1 (by norm_num)
  have hgrad : ∀ v ∈ Icc 0 t, ∀ y, ‖gradient (f v) y‖ ≤ B1 := by
    intro v hv y
    have h1 := hB1 v hv y
    rw [norm_iteratedFDeriv_one] at h1
    unfold gradient
    rwa [LinearIsometryEquiv.norm_map]
  -- the source
  set S : ℝ → Euc d → ℝ := fun v y => divGConvPlain d s
    (fun z => ρ v z • Torus.matVec M.transpose (gradient (f v) z)) y with hSdef
  have hS : ∀ v ∈ Icc 0 t, ∀ y, generatorW C0 v (f v) y = C0.ν * Laplacian.laplacian (f v) y +
      inner ℝ (C0.drift v y) (gradient (f v) y) - S v y := by
    intro v hv y
    have hvT : v ∈ Icc 0 T := ⟨hv.1, hv.2.trans htT⟩
    have h := ad_generator_split_hyp hd D hvT (f v) y
      ((hf.c2 v hv).of_le (by norm_num)) (hgrad v hv)
    rw [h, ad_drift_eq D v y]
    rfl
  have hSc := ad2_S_cont hH C0 ht hdrift hf S hS
  -- the representation formula
  obtain ⟨Ω, mΩ, P, hP, ℱ, W, hW⟩ := exists_isBrownianFiltration_type (Fin d)
  haveI := hP
  have hrep := fun x => (ad3_representation.{0} P ℱ W hW Q k ‖c‖ ΛB c' B' hH C0 D.ν_range.1 hdrift hf
    S hS hr hlt.le x).2
  have hfr : propagatorW C0 r t φ = fun x => lcSg P W (fun _ => ν) Q c' B' r t φ x -
      ∫ u in r..t, lcSg P W (fun _ => ν) Q c' B' r u (S u) x := by
    funext x
    rw [hprop r]
    exact hrep x
  -- the source bound
  set ulr : ℝ := ulE.toReal with hulr
  have hulr0 : 0 ≤ ulr := ENNReal.toReal_nonneg
  set D1 : ℝ := Cs * (max K 0 * ulr) with hD1
  have hD10 : 0 ≤ D1 := by positivity
  have hSd : ∀ v ∈ Icc r t, ContDiff ℝ (k : WithTop ℕ∞) (S v) ∧
      decayNormE k (s + 1) (S v) ≤ ENNReal.ofReal D1 := by
    intro v hv
    obtain ⟨h1, h2⟩ := hCs θ Q c T νstar K ν ρ D v t (hr.trans hv.1) hv.2 htT φ hφ hul
    have e : ∀ v, propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) v t φ = f v := hprop
    simp only [e] at h1 h2
    refine ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [hD1]
    have : K * ulr ≤ max K 0 * ulr := mul_le_mul_of_nonneg_right (le_max_left _ _) hulr0
    exact mul_le_mul_of_nonneg_left this hCs0
  obtain ⟨hFcd, hFb⟩ := hCi P ℱ W ν c' B' hW D.ν_range.1 D.ν_range.2 hH hdec S D1 hD10 r t hr hlt
    htT hSc hSd
  have hφk : ContDiff ℝ (k : WithTop ℕ∞) φ := hφ.of_le (by
    rw [show k + 2 + ⌈(d : ℝ) / 2⌉₊ = k + (2 + ⌈(d : ℝ) / 2⌉₊) by omega]
    exact_mod_cast Nat.le_add_right k _)
  obtain ⟨hEcd, hEb⟩ := hCe P ℱ W (fun _ => ν) c' B' hW continuous_const
    (fun _ => ⟨D.ν_range.1, D.ν_range.2⟩) hH hdec r t hr hlt.le htT φ hφk hdφ'
  -- the bound
  set Ge : Euc d → ℝ := lcSg P W (fun _ => ν) Q c' B' r t φ with hGe
  set Fd : Euc d → ℝ := fun x => ∫ u in r..t, lcSg P W (fun _ => ν) Q c' B' r u (S u) x with hFd
  have hsplit : ∀ j ≤ k, ∀ (I : Fin j → Fin d) (x : Euc d),
      partialDeriv I (propagatorW C0 r t φ) x = partialDeriv I Ge x - partialDeriv I Fd x := by
    intro j hj I x
    rw [hfr]
    unfold partialDeriv
    have h1 : ContDiff ℝ (j : WithTop ℕ∞) Ge := hEcd.of_le (by exact_mod_cast hj)
    have h2 : ContDiff ℝ (j : WithTop ℕ∞) Fd := hFcd.of_le (by exact_mod_cast hj)
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := j) (x := x) h1.contDiffAt h2.contDiffAt
    have e : (fun x => Ge x - Fd x) = Ge - Fd := rfl
    rw [e, this]
    rfl
  have hmain : decayNormE k (s + 1) (propagatorW C0 r t φ) ≤
      ENNReal.ofReal Ce * decayNormE k (s + 1) φ + ENNReal.ofReal (Ci * D1) := by
    unfold decayNormE derivSupE
    refine iSup_le fun j => iSup_le fun I => iSup_le fun x => ?_
    have hj : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.2
    rw [hsplit (j : ℕ) hj I x]
    have hjb : 0 ≤ jbracket x ^ (s + 1 + ((j : ℕ) : ℝ)) :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hle1 : jbracket x ^ (s + 1 + ((j : ℕ) : ℝ)) * |partialDeriv I Ge x - partialDeriv I Fd x| ≤
        jbracket x ^ (s + 1 + ((j : ℕ) : ℝ)) * |partialDeriv I Ge x| +
          jbracket x ^ (s + 1 + ((j : ℕ) : ℝ)) * |partialDeriv I Fd x| := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) hjb
    refine (ENNReal.ofReal_le_ofReal hle1).trans ?_
    rw [ENNReal.ofReal_add (mul_nonneg hjb (abs_nonneg _)) (mul_nonneg hjb (abs_nonneg _))]
    refine add_le_add ?_ ?_
    · exact (ad3_term_le (b := s + 1) (g := Ge) hj I x).trans hEb
    · refine ENNReal.ofReal_le_ofReal ?_
      exact (mul_le_mul_of_nonneg_left (lc4_partial_le (j : ℕ) I x) hjb).trans (hFb (j : ℕ) hj x)
  refine hmain.trans ?_
  have hulfin : ulE ≠ ⊤ := hul.ne
  have hulE' : ENNReal.ofReal ulr = ulE := ENNReal.ofReal_toReal hulfin
  have h2 : ENNReal.ofReal (Ci * D1) = ENNReal.ofReal (Ci * Cs * max K 0) * ulE := by
    rw [← hulE', ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hD1]; ring
  rw [h2, mul_add]
  gcongr
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)

end HRS.MS.AdjDecay
