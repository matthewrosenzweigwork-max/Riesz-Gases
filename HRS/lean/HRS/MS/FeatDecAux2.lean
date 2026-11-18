import HRS.MS.FeatDecAux1
import HRS.MS.AdjDecay

/-!
# S8.5 `feature_decay`, part 2 (S85 packet): `adjoint_decay` for `0 ≤ s < d` (stationary density)

`s85_adjoint_decay`: the statement of S4.12 (`HRS.Whole.adjoint_decay`) for the stationary dynamics
`(⟨s, M, quadV Q c, ν⟩).coeff (fun _ => ρ)`, with the range `0 ≤ s ≤ d - 2` of `AdjointDecayHyp` replaced by `0 ≤ s < d`
(needed at the critical exponent `s = d/2` for `d = 2, 3`).  It is the proof of `AdjDecay.adjoint_decay_proof` with the far-field
inputs `s85_drift_hyps`, `s85_partB` (cancellation convention, FeatDecAux1) in place of `far_derivatives_proof`, and the splitting of
the generator being the definition of `generatorW` (the source is `s85S`, no plain-integral conversion).  The price is one extra
derivative: `ρ ∈ C^{k+2}` with `weightedSupE (k+2) L ρ ≤ Λ`, the adjoint input at order `k + 2` and a datum in `C^{k+3+⌈d/2⌉}`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open HRS HRS.Whole HRS.MS.Lc HRS.MS.AdjVerif HRS.MS.Adj HRS.MS.PoisKolm HRS.MD.EQLawPath
open HRS.MS.AdjDecay

noncomputable section

namespace HRS.MS.S85

variable {d : ℕ}

/-- The drift of the stationary coefficient. -/
theorem s85_drift_eq {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Q.IsSymm) {c : Euc d} {ν : ℝ}
    (ρ : Euc d → ℝ) (r : ℝ) (x : Euc d) :
    ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff (fun _ => ρ)).drift r x =
      Torus.matVec M (convGradConvW (rieszKernelGrad d s) ρ x) - (Torus.matVec Q x + c) := by
  show meanFieldDriftW ⟨s, M, quadV Q c, ν⟩ ρ x = _
  unfold meanFieldDriftW
  simp only
  rw [ad_gradient_quadV hQ]

theorem s85_adjoint_decay (hd : 2 ≤ d) (θ : Euc d → ℝ) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (M Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsSymm) (c : Euc d) (T νstar : ℝ) (k : ℕ)
    (L Λ K : ℝ) (hL : (d : ℝ) + k + s + 4 < L) :
    ∃ C : ℝ, ∀ (ν : ℝ) (ρ : Euc d → ℝ), 0 ≤ ν → ν ≤ νstar →
      ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞) ρ → weightedSupE (k + 2) L ρ ≤ ENNReal.ofReal Λ →
      UlAdjointInput θ ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) T (k + 2) K →
      ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ,
        ContDiff ℝ ((k + 3 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ →
        ulNormE (k + 3 + ⌈(d : ℝ) / 2⌉₊) θ φ < ⊤ →
        ContDiff ℝ (k : WithTop ℕ∞)
          (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) r t φ) ∧
        decayNormE k (s + 1)
          (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) r t φ) ≤
          ENNReal.ofReal C * (decayNormE k (s + 1) φ + ulNormE (k + 3 + ⌈(d : ℝ) / 2⌉₊) θ φ) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ΛB, hΛB0, hΛB⟩ := s85_drift_hyps hd s hs0 hsd k M L Λ hL
  have hL3 : (d : ℝ) + k + s + 3 < L := by linarith
  obtain ⟨Cs, hCs0, hCs⟩ := s85_partB hd s hs0 hsd k L hL3 M Λ
  have hb : (0 : ℝ) < s + 1 := by linarith
  obtain ⟨Ce, hCe⟩ := lc_engine.{0} s hs0 Q k T νstar (s + 1) ‖c‖ ΛB hb
  obtain ⟨Ci, hCi0, hCi⟩ := ad3_int_engine.{0} s hs0 Q k T νstar (s + 1) ‖c‖ ΛB hb
  set Cfin : ℝ := max (max Ce (Ci * Cs * max K 0)) 1 with hCfin
  have hCfin1 : 1 ≤ Cfin := le_max_right _ _
  have hCfin0 : 0 < Cfin := by linarith
  refine ⟨Cfin, fun ν ρ hν0 hνs hρsm hwse hAdj r t hr hrt htT φ hφ hul => ?_⟩
  set C0 : WholeCoeff d := (⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff (fun _ => ρ) with hC0
  have hT0 : 0 ≤ T := hr.trans (hrt.trans htT)
  set ulE : ℝ≥0∞ := ulNormE (k + 3 + ⌈(d : ℝ) / 2⌉₊) θ φ with hulE
  have hkk : (k + 2 + 1 + ⌈(d : ℝ) / 2⌉₊) = k + 3 + ⌈(d : ℝ) / 2⌉₊ := by omega
  -- the adjoint input
  have hadjF : ∀ v, 0 ≤ v → v ≤ t → (∃ f, IsClassicalAdjointW C0 t φ f) ∧
      MemCb (k + 2) (propagatorW C0 v t φ) ∧
      cbNorm (k + 2) (propagatorW C0 v t φ) ≤ K * (ulE).toReal := by
    intro v hv hvt
    have h := hAdj v t hv hvt htT φ (by rw [hkk]; exact hφ) (by rw [hkk]; exact hul)
    rw [hkk] at h
    exact h
  obtain ⟨hex, hmem, -⟩ := hadjF r hr hrt
  have hCk : ContDiff ℝ (k : WithTop ℕ∞) (propagatorW C0 r t φ) :=
    hmem.1.of_le (by exact_mod_cast Nat.le_add_right k 2)
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
  have hρk1 : ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞) ρ := hρsm
  obtain ⟨hBc, hBb, hBdec⟩ := hΛB ρ hρsm hwse
  set Bu : ℝ → Euc d → Euc d := fun _ y =>
    Torus.matVec M (convGradConvW (rieszKernelGrad d s) ρ y) with hBu
  have hcontB : ContinuousOn (fun p : ℝ × Euc d => Bu p.1 p.2) (Icc 0 T ×ˢ univ) := by
    have h1 : Continuous (fun x : Euc d => Torus.matVec M (convGradConvW (rieszKernelGrad d s) ρ x)) :=
      hBc.continuous
    exact (h1.comp continuous_snd).continuousOn
  have hH : LcHyp Q k ‖c‖ ΛB (fun v => (fun _ : ℝ => c) (min v T)) (fun v => Bu (min v T)) :=
    lcHyp_clamp hT0 continuousOn_const hcontB (fun _ _ => le_rfl)
      (fun v hv => ⟨hBc, fun j hj x => hBb j hj x⟩)
  have hdec := lcDecay_clamp (B := Bu) (k := k) (σ := s + 1) (ΛB := ΛB) hT0 (fun v hv => hBdec)
  set c' : ℝ → Euc d := fun v => (fun _ : ℝ => c) (min v T) with hc'
  set B' : ℝ → Euc d → Euc d := fun v => Bu (min v T) with hB'
  -- drift identification
  have hdrift : ∀ v ∈ Icc 0 t, ∀ y, C0.drift v y = B' v y - lcQ Q y - c' v := by
    intro v hv y
    rw [hC0, s85_drift_eq hQ ρ v y]
    show _ = Torus.matVec M (convGradConvW (rieszKernelGrad d s) ρ y) - Torus.matVec Q y - c
    abel
  -- bounds on the gradient of f
  obtain ⟨B1, hB1⟩ := hf.bdd 1 (by norm_num)
  -- the source
  set S : ℝ → Euc d → ℝ := fun v y => s85S s M ρ (f v) y with hSdef
  have hS : ∀ v ∈ Icc 0 t, ∀ y, generatorW C0 v (f v) y = C0.ν * Laplacian.laplacian (f v) y +
      inner ℝ (C0.drift v y) (gradient (f v) y) - S v y := by
    intro v hv y
    rfl
  have hSc := ad2_S_cont hH C0 ht hdrift hf S hS
  -- the representation formula
  obtain ⟨Ω, mΩ, P, hP, ℱ, W, hW⟩ := exists_isBrownianFiltration_type (Fin d)
  haveI := hP
  have hrep := fun x => (ad3_representation.{0} P ℱ W hW Q k ‖c‖ ΛB c' B' hH C0 hν0 hdrift hf
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
  have hρk : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) ρ :=
    hρsm.of_le (by exact_mod_cast Nat.le_succ (k + 1))
  have hwk : weightedSupE (k + 1) L ρ ≤ ENNReal.ofReal Λ := (ad1_wse_mono (k + 1) L _).trans hwse
  have hSd : ∀ v ∈ Icc r t, ContDiff ℝ (k : WithTop ℕ∞) (S v) ∧
      decayNormE k (s + 1) (S v) ≤ ENNReal.ofReal D1 := by
    intro v hv
    obtain ⟨-, hmemv, hcbv⟩ := hadjF v (hr.trans hv.1) hv.2
    have e : propagatorW C0 v t φ = f v := hprop v
    rw [e] at hmemv hcbv
    obtain ⟨h1, h2⟩ := hCs ρ hρk hwk (f v) hmemv
    refine ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [hD1]
    have : cbNorm (k + 2) (f v) ≤ max K 0 * ulr :=
      hcbv.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hulr0)
    exact mul_le_mul_of_nonneg_left this hCs0
  obtain ⟨hFcd, hFb⟩ := hCi P ℱ W ν c' B' hW hν0 hνs hH hdec S D1 hD10 r t hr hlt
    htT hSc hSd
  have hφk : ContDiff ℝ (k : WithTop ℕ∞) φ := hφ.of_le (by
    rw [show k + 3 + ⌈(d : ℝ) / 2⌉₊ = k + (3 + ⌈(d : ℝ) / 2⌉₊) by omega]
    exact_mod_cast Nat.le_add_right k _)
  obtain ⟨hEcd, hEb⟩ := hCe P ℱ W (fun _ => ν) c' B' hW continuous_const
    (fun _ => ⟨hν0, hνs⟩) hH hdec r t hr hlt.le htT φ hφk hdφ'
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

end HRS.MS.S85
