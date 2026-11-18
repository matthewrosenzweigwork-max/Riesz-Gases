import HRS.MS.R2WinOrbNLAux1

/-!
# S10.3 (nonlinear branch), part 2: the zeroth-order orbit bound along a small-class trajectory

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.  `s103n_zeroth` (TeX S L8120-8150, nonlinear case): for a trajectory `ρ` of the
S6.3 small class with radius `r ≤ R_w` and a classical adjoint solution `f` with terminal datum `φ`,
`|f_r(x)| ≤ B_φ + C_z (‖∇φ‖_{C_b^k} + ‖√ρ_β Πφ‖_{Σ^M})`: the one-body Markov semigroup contracts the supremum norm, the source
`J(ρ_v) f_v - F_v·∇f_v` decays like `e^{-κ(T-v)}` (weighted decay of `f_v` in `Σ^M`, the gradient estimate, and the bounded force `F_v`),
and the Duhamel formula `s67bd_onebody_duhamel` closes the argument.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.BreakdownS67 HRS.MS.Mov63 HRS.MS.MovLin HRS.MS.MovAdj HRS.MS.MovOsc
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ}

/-- The gradient estimate of S6.7 (orders `k = 4d+42`, `M = 8d+80`) along a fixed trajectory `ρ`. -/
def S103nGrad (d : ℕ) (s a β : ℝ) (ρβ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ) (Cg cg : ℝ) : Prop :=
  ∀ (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ), 0 ≤ T →
    IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) T φ f →
    ContDiff ℝ ((4 * d + 42 : ℕ) + 1) φ → MemOsc ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ φ) →
    ∀ r' ∈ Icc (0 : ℝ) T,
      ContDiff ℝ (4 * d + 42 : ℕ) (fun x => gradient (f r') x) ∧
      cbNormVecE (4 * d + 42) (fun x => gradient (f r') x) ≤
        ENNReal.ofReal (Cg * Real.exp (-cg * (T - r'))) *
          (cbNormVecE (4 * d + 42) (fun x => gradient φ x) +
            ENNReal.ofReal (oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ φ)))

theorem s103n_exp_int_le {κ : ℝ} (hκ : 0 < κ) {a T : ℝ} (haT : a ≤ T) :
    ∫ v in a..T, Real.exp (-κ * (T - v)) ≤ 1 / κ := by
  have h := intervalIntegral.integral_comp_sub_left (fun u : ℝ => Real.exp (-κ * u)) (a := a) (b := T) T
  rw [sub_self] at h
  calc ∫ v in a..T, Real.exp (-κ * (T - v)) = ∫ u in (0 : ℝ)..(T - a), Real.exp (-κ * u) := h
    _ ≤ 1 / κ := HRS.MS.R2WinOrb.s103_exp_integral_le hκ (sub_nonneg.2 haT)

set_option maxHeartbeats 1600000 in
theorem s103n_zeroth {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) :
    ∃ Rw : ℝ, 0 < Rw ∧ ∀ (r c₁ Cg cg : ℝ), 0 ≤ r → r ≤ Rw → r ≤ 1 → 0 ≤ c₁ → 0 < cg → 0 ≤ Cg →
      ∃ Cz : ℝ, 0 ≤ Cz ∧ ∀ (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
        MovInSmallClass d s a β ρβ (102 * d + 1020) r c₁ f0 ρ → S103nGrad d s a β ρβ ρ Cg cg →
        ∀ (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (Bφ : ℝ), 0 ≤ T →
          IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) T φ f →
          ContDiff ℝ ((4 * d + 42 : ℕ) + 1) φ → MemOsc ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ φ) →
          cbNormVecE (4 * d + 42) (fun x => gradient φ x) < ⊤ → (∀ x, |φ x| ≤ Bφ) →
          ∀ r' ∈ Icc (0 : ℝ) T, ∀ x, |f r' x| ≤ Bφ + Cz *
            ((cbNormVecE (4 * d + 42) (fun x => gradient φ x)).toReal +
              oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ φ)) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hM2 : 2 ≤ 8 * d + 80 := by omega
  have hM0 : (d : ℝ) / 2 + ((0 : ℕ) : ℝ) + 5 < ((8 * d + 80 : ℕ) : ℝ) := by push_cast; linarith
  have hMk : (d : ℝ) / 2 + ((4 * d + 42 : ℕ) : ℝ) + 5 < ((8 * d + 80 : ℕ) : ℝ) := by
    push_cast; linarith
  have hm7 : (d : ℝ) / 2 + 7 < ((102 * d + 1020 : ℕ) : ℝ) := by push_cast; linarith
  have hmM : ((8 * d + 80 : ℕ) : ℝ) + 4 < ((102 * d + 1020 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨Rw, Cw, cw, hRw, hCw, hcw, hw⟩ := s67bd_weighted_decay H (8 * d + 80) (102 * d + 1020) hM2 hm7 hmM
  obtain ⟨CJ, hCJ0, hJ⟩ := s67bd_J_bound H 0 (8 * d + 80) (102 * d + 1020) hM0 hm7 hmM
  obtain ⟨CF, hCF0, hF⟩ :=
    s67bd_transport_source_jets H (4 * d + 42) (8 * d + 80) (102 * d + 1020) hMk hm7 hmM
  obtain ⟨Ω, mΩ, P, hP, ℱ, W, hW⟩ := exists_isBrownianFiltration_type (Fin d)
  haveI := hP
  refine ⟨Rw, hRw, fun r c₁ Cg cg hr0 hrRw hr1 hc₁ hcg hCg => ?_⟩
  have hκpos : 0 < min cw cg := lt_min hcw hcg
  have hCw0 : 0 ≤ Cw := zero_le_one.trans hCw
  refine ⟨(CJ * Cw + CF * r * Cg) / min cw cg, by positivity, ?_⟩
  intro f0 ρ hρ hG T φ f Bφ hT hf hφreg hφ hφfin hφB r' hr' x
  set κ := min cw cg with hκ
  set G := (cbNormVecE (4 * d + 42) (fun x => gradient φ x)).toReal with hGdef
  set N := oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ φ) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hK0 : 0 ≤ (CJ * Cw + CF * r * Cg) * (G + N) := by positivity
  have hq' : 0 < β * a := mul_pos H.hβ H.hq
  obtain ⟨-, hrep⟩ := s67bd_onebody_duhamel P ℱ W hW H 0 (8 * d + 80) (102 * d + 1020) hM0 hm7 hmM
    r c₁ hr0 hr1 hc₁ f0 ρ hρ T φ f hT hf hφ r' hr' x
  have hsrc : ∀ v ∈ Icc r' T, ∀ y, |s67bd_source d s ρβ ρ f v y| ≤
      ((CJ * Cw + CF * r * Cg) * (G + N)) * Real.exp (-κ * (T - v)) := by
    intro v hv y
    have hvT : v ∈ Icc (0 : ℝ) T := ⟨hr'.1.trans hv.1, hv.2⟩
    have hv0 : 0 ≤ v := hvT.1
    obtain ⟨hmem, hnorm⟩ := hw r c₁ hr0 hrRw hc₁ f0 ρ hρ T φ f hT hf hφ v hvT
    have hJv := (hJ r c₁ hr0 hr1 hc₁ f0 ρ hρ v hv0 (f v) (hf.isC12TestRd.memCb hvT) hmem).2 0
      (by norm_num) y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hJv
    obtain ⟨hgd, hgb⟩ := hG T φ f hT hf hφreg hφ v hvT
    have hu : ContDiff ℝ (((4 * d + 42 : ℕ) + 1 : ℕ) : WithTop ℕ∞) (f v) :=
      HRS.MS.R2WinOrb.s103_fderiv_contDiff ((hf.c2 v hvT).differentiable (by norm_num)) hgd
    have hrhs : ENNReal.ofReal (Cg * Real.exp (-cg * (T - v))) *
        (cbNormVecE (4 * d + 42) (fun x => gradient φ x) + ENNReal.ofReal N) ≠ ⊤ :=
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.2 ⟨hφfin, ENNReal.ofReal_lt_top⟩)).ne
    have hcbfin : cbNormVecE (4 * d + 42) (fun x => gradient (f v) x) < ⊤ :=
      lt_of_le_of_lt hgb (lt_top_iff_ne_top.2 hrhs)
    have hgr : (cbNormVecE (4 * d + 42) (fun x => gradient (f v) x)).toReal ≤
        Cg * Real.exp (-cg * (T - v)) * (G + N) := by
      refine (ENNReal.toReal_mono hrhs hgb).trans (le_of_eq ?_)
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_add hφfin.ne
        ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hN0]
    have hFv := (hF r c₁ hr0 hr1 hc₁ f0 ρ hρ v hv0 (f v) hu hcbfin).2 0 (Nat.zero_le _) y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hFv
    have hT1 : 0 ≤ T - v := sub_nonneg.2 hv.2
    have hE1 : Real.exp (-cw * (T - v)) ≤ Real.exp (-κ * (T - v)) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_left cw cg])
    have hE2 : Real.exp (-cg * (T - v)) ≤ Real.exp (-κ * (T - v)) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_right cw cg])
    have hEp : 0 ≤ Real.exp (-κ * (T - v)) := (Real.exp_pos _).le
    have hsub : |s67bd_source d s ρβ ρ f v y| ≤
        |s67J d s (ρ v) (f v) y| + |inner ℝ (s67bd_F d s ρβ (movV ρβ ρ v) y) (gradient (f v) y)| := by
      unfold s67bd_source
      exact abs_sub _ _
    have hA : |s67J d s (ρ v) (f v) y| ≤ CJ * Cw * Real.exp (-κ * (T - v)) * N := by
      refine hJv.trans ?_
      calc CJ * oscNorm ((8 * d + 80 : ℕ) : ℝ) (s67psi ρβ (f v)) ≤
          CJ * (Cw * Real.exp (-cw * (T - v)) * N) := mul_le_mul_of_nonneg_left hnorm hCJ0
        _ ≤ CJ * (Cw * Real.exp (-κ * (T - v)) * N) := by gcongr
        _ = _ := by ring
    have hB : |inner ℝ (s67bd_F d s ρβ (movV ρβ ρ v) y) (gradient (f v) y)| ≤
        CF * r * Cg * Real.exp (-κ * (T - v)) * (G + N) := by
      refine hFv.trans ?_
      calc CF * r * (cbNormVecE (4 * d + 42) (fun x => gradient (f v) x)).toReal ≤
          CF * r * (Cg * Real.exp (-cg * (T - v)) * (G + N)) :=
            mul_le_mul_of_nonneg_left hgr (by positivity)
        _ ≤ CF * r * (Cg * Real.exp (-κ * (T - v)) * (G + N)) := by gcongr
        _ = _ := by ring
    calc |s67bd_source d s ρβ ρ f v y| ≤ CJ * Cw * Real.exp (-κ * (T - v)) * N +
          CF * r * Cg * Real.exp (-κ * (T - v)) * (G + N) := hsub.trans (add_le_add hA hB)
      _ ≤ CJ * Cw * Real.exp (-κ * (T - v)) * (G + N) +
          CF * r * Cg * Real.exp (-κ * (T - v)) * (G + N) := by
            have : 0 ≤ CJ * Cw * Real.exp (-κ * (T - v)) := by positivity
            nlinarith [mul_le_mul_of_nonneg_left (show N ≤ G + N by linarith) this]
      _ = _ := by ring
  have hint : |∫ v in r'..T, sg P W (β * a) (s67bd_oneBodyB d s β ρβ) ((v - r') / β)
      (s67bd_source d s ρβ ρ f v) x| ≤ ((CJ * Cw + CF * r * Cg) * (G + N)) * (1 / κ) := by
    rw [← Real.norm_eq_abs]
    have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := r') (b := T) hr'.2
      (f := fun v => sg P W (β * a) (s67bd_oneBodyB d s β ρβ) ((v - r') / β)
        (s67bd_source d s ρβ ρ f v) x)
      (g := fun v => ((CJ * Cw + CF * r * Cg) * (G + N)) * Real.exp (-κ * (T - v)))
      (Eventually.of_forall fun v hv => by
        rw [Real.norm_eq_abs]
        exact HRS.MS.R2WinOrb.s103_sg_abs_le P W (β * a) _ _ _ x (hsrc v ⟨hv.1.le, hv.2⟩))
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (s103n_exp_int_le hκpos hr'.2) hK0
  have h1 : |sg P W (β * a) (s67bd_oneBodyB d s β ρβ) ((T - r') / β) φ x| ≤ Bφ :=
    HRS.MS.R2WinOrb.s103_sg_abs_le P W (β * a) _ _ _ x hφB
  rw [hrep]
  calc _ ≤ |sg P W (β * a) (s67bd_oneBodyB d s β ρβ) ((T - r') / β) φ x| +
        |∫ v in r'..T, sg P W (β * a) (s67bd_oneBodyB d s β ρβ) ((v - r') / β)
          (s67bd_source d s ρβ ρ f v) x| := abs_add_le _ _
    _ ≤ Bφ + ((CJ * Cw + CF * r * Cg) * (G + N)) * (1 / κ) := add_le_add h1 hint
    _ = Bφ + (CJ * Cw + CF * r * Cg) / κ * (G + N) := by field_simp

end HRS.MS.R2WinOrbNL

end
