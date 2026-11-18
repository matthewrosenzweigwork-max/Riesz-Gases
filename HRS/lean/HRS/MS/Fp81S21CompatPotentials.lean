import HRS.MS.Fp81S21QwinCorrector

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS (Euc MemCb cbNorm)
open HRS.Whole
open HRS.MS.R26T3

/-- Each derivative in a C_b^J norm is bounded by the full cbNorm. -/
theorem fp81s21_cb_iter_le_of_memCb
    {d J : ℕ} {q : Euc d → ℝ} (hq : MemCb J q) {i : ℕ} (hi : i ≤ J)
    (x : Euc d) :
    ‖iteratedFDeriv ℝ i q x‖ ≤ cbNorm J q := by
  unfold cbNorm
  calc
    ‖iteratedFDeriv ℝ i q x‖ ≤ ⨆ y, ‖iteratedFDeriv ℝ i q y‖ :=
      le_ciSup (hq.2 i hi) x
    _ ≤ ∑ j ∈ Finset.range (J + 1), ⨆ y, ‖iteratedFDeriv ℝ j q y‖ :=
      Finset.single_le_sum
        (f := fun j => ⨆ y, ‖iteratedFDeriv ℝ j q y‖)
        (fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

/-- Differentiating a scalar multiple scales its gradient by the same scalar. -/
theorem fp81s21_gradient_smul
    {d : ℕ} (q : Euc d → ℝ) (c : ℝ) (x : Euc d)
    (hq : ContDiff ℝ 1 q) :
    gradient (c • q) x = c • gradient q x := by
  have hdif : DifferentiableAt ℝ q x := (hq.differentiable (by norm_num)) x
  unfold gradient
  have hfd : fderiv ℝ (c • q) x = c • fderiv ℝ q x :=
    (hdif.hasFDerivAt.const_smul c).fderiv
  rw [hfd]
  simp only [map_smul]

/-- The shift-indexed compatible-potential family type. -/
abbrev fp81s21_CompatPotentialFamily {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) :=
  ∀ a : Set.Ici (0 : ℝ), InitialFamData R (r26t3_qwin R (a : ℝ))

/-- A shift-indexed InitialFamData family whose potentials are the same scaled choices
returned by the explicit corrector. Its family constant and decaying gradient bound are uniform
in both the shift and feature index. -/
theorem fp81s21_compatible_qwin_potentials (p : Parameters) (hγ : 0 < p.γ) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ K C c : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ 0 < c ∧
          ∃ F : fp81s21_CompatPotentialFamily R,
            (∀ a : Set.Ici (0 : ℝ), (F a).K ≤ K) ∧
            (∀ a : Set.Ici (0 : ℝ), ∀ j : ℕ, HasCbBound (fp81s21_k0 p.d)
              (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j)
              (gradient ((F a).χ j))) := by
  obtain ⟨δu, hδu, hδuhalf, hu⟩ := fp81s21_qwin_uniform p
  obtain ⟨δq, hδq, hδqhalf, hq⟩ := fp81s21_qwin_s48Q_decay p
  let δ0 : ℝ := min δu δq
  have hδ0 : 0 < δ0 := lt_min hδu hδq
  have hδ0half : δ0 ≤ 1 / 2 :=
    (min_le_left δu δq).trans hδuhalf
  refine ⟨δ0, hδ0, hδ0half, fun δ hδ hδle R => ?_⟩
  obtain ⟨Cwin, hCwin, hwin⟩ :=
    hu δ hδ (hδle.trans (min_le_left δu δq)) R
  obtain ⟨Cq, hCq, c, hc, hQdecay⟩ :=
    hq δ hδ (hδle.trans (min_le_right δu δq)) R
  obtain ⟨M₂, hM₂0, hprob, hint2, hM₂⟩ :=
    fp81s21_initial_secondMoment hδ (hδle.trans hδ0half) R
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hprob
  have hEne : Nonempty (InitialSteinEnv R) :=
    initialSteinEnv_exists hδ (hδle.trans hδ0half) R hγ
  let E : InitialSteinEnv R := Classical.choice hEne
  obtain ⟨Ccorr, hCcorr, hcorrector⟩ :=
    fp81s21_initial_corrector_explicit hδ (hδle.trans hδ0half) R E hγ
  obtain ⟨Ca, hCa0, hresponse⟩ :=
    r26t3_response_smooth hδ (hδle.trans hδ0half) R hγ
  let J : ℕ := fp81s21_correctorOrder p.d
  have hJ : 1 ≤ J := by
    dsimp [J, fp81s21_correctorOrder]
    omega
  have hJle : J ≤ r26t3_J p.d :=
    fp81s21_correctorOrder_le p.d p.hd
  have hJd : r26t3_J p.d = fp81s21_J1 p.d := by
    simp [r26t3_J, fp81s21_J1]
  let K : ℝ := max
    ((p.γ * Ccorr) * (Real.sqrt M₂ + (J : ℝ))) Ca
  have hK : 0 ≤ K := le_max_of_le_right hCa0
  let C : ℝ := p.γ * Ccorr * Cq
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hγ.le hCcorr) hCq
  have hQordinary : ∀ a : Set.Ici (0 : ℝ), ∀ j : ℕ,
      HRS.MS.S48.s48_Q (r26t3_mu R 0) J (r26t3_qwin R (a : ℝ) j) ≤
        (Real.sqrt M₂ + (J : ℝ)) *
          cbNorm (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ) j) := by
    intro a j
    let qj := r26t3_qwin R (a : ℝ) j
    have hmemJ : MemCb (r26t3_J p.d) qj := (hwin a a.2).1.1 j
    have hmem : MemCb J qj :=
      (HRS.MS.Tc5.tc5_cb_mono hJle hmemJ).1
    have hA0 : 0 ≤ cbNorm (r26t3_J p.d) qj :=
      HRS.MS.Tc5.tc5_cb_nonneg (r26t3_J p.d) qj
    have hderiv : ∀ i, 1 ≤ i → i ≤ J → ∀ x,
        ‖iteratedFDeriv ℝ i qj x‖ ≤ cbNorm (r26t3_J p.d) qj := by
      intro i hi1 hiJ x
      exact fp81s21_cb_iter_le_of_memCb hmemJ (hiJ.trans hJle) x
    have hQ := fp81s21_s48Q_of_deriv_bounds (r26t3_mu R 0) qj
      (cbNorm (r26t3_J p.d) qj) M₂ hJ hmem hint2 hM₂ hA0 hderiv
    simpa [hJd] using hQ
  have hdata : ∀ a : Set.Ici (0 : ℝ),
      ∃ F : InitialFamData R (r26t3_qwin R (a : ℝ)),
        F.K ≤ K ∧
        ∀ j, HasCbBound (fp81s21_k0 p.d)
          (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j)
          (gradient (F.χ j)) := by
    intro a
    have ha : 0 ≤ (a : ℝ) := a.2
    have hex : ∀ j, ∃ χj : Euc p.d → ℝ,
        ContDiff ℝ ((fp81s21_k0 p.d + 2 : ℕ) : WithTop ℕ∞) χj ∧
        (∀ x, weightedGen (R.ρ 0) χj x =
          r26t3_a R (r26t3_qwin R (a : ℝ) j) x) ∧
        HasCbBound (fp81s21_k0 p.d)
          (Ccorr * HRS.MS.S48.s48_Q (r26t3_mu R 0) J
            (r26t3_qwin R (a : ℝ) j)) (gradient χj) := by
      intro j
      let qj := r26t3_qwin R (a : ℝ) j
      have hmemJ : MemCb (r26t3_J p.d) qj := (hwin a ha).1.1 j
      have hmem : MemCb (fp81s21_correctorOrder p.d) qj := by
        simpa [J] using (HRS.MS.Tc5.tc5_cb_mono hJle hmemJ).1
      obtain ⟨_, _, χj, hχj, hχjgen, hχjgrad⟩ := hcorrector qj hmem
      exact ⟨χj, hχj, hχjgen, hχjgrad⟩
    choose χ hχ hχgen hχgrad using hex
    have hderiv : ∀ j x, ∀ i ≤ fp81s21_k0 p.d,
        ‖iteratedFDeriv ℝ (i + 1) (p.γ • χ j) x‖ ≤
          K * cbNorm (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ) j) := by
      intro j x i hi
      let qj := r26t3_qwin R (a : ℝ) j
      have hmemJ : MemCb (r26t3_J p.d) qj := (hwin a ha).1.1 j
      have hqnorm0 : 0 ≤ cbNorm (fp81s21_J1 p.d) qj := by
        rw [← hJd]
        exact HRS.MS.Tc5.tc5_cb_nonneg (r26t3_J p.d) qj
      have hreg : ContDiffAt ℝ ((i + 1 : ℕ) : WithTop ℕ∞) (χ j) x :=
        ((hχ j).of_le (by exact_mod_cast (show i + 1 ≤ fp81s21_k0 p.d + 2 by omega))).contDiffAt
      have hiter := iteratedFDeriv_const_smul_apply'
        (𝕜 := ℝ) (a := p.γ) (f := χ j) (i := i + 1) (x := x) hreg
      have hscale : iteratedFDeriv ℝ (i + 1) (p.γ • χ j) x =
          p.γ • iteratedFDeriv ℝ (i + 1) (χ j) x := by
        change iteratedFDeriv ℝ (i + 1) (p.γ • χ j) x = _
        exact hiter
      have hphys : ‖iteratedFDeriv ℝ (i + 1) (χ j) x‖ ≤
          Ccorr * HRS.MS.S48.s48_Q (r26t3_mu R 0) J qj := by
        have h := (hχgrad j).2 i hi x
        rw [HRS.MS.Gap.gap1_norm_iter_gradient] at h
        exact h
      rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
      calc
        p.γ * ‖iteratedFDeriv ℝ (i + 1) (χ j) x‖ ≤
            p.γ * (Ccorr * HRS.MS.S48.s48_Q (r26t3_mu R 0) J qj) :=
          mul_le_mul_of_nonneg_left hphys hγ.le
        _ = (p.γ * Ccorr) * HRS.MS.S48.s48_Q (r26t3_mu R 0) J qj := by ring
        _ ≤ (p.γ * Ccorr) *
            ((Real.sqrt M₂ + (J : ℝ)) * cbNorm (fp81s21_J1 p.d) qj) :=
          mul_le_mul_of_nonneg_left (hQordinary a j)
            (mul_nonneg hγ.le hCcorr)
        _ = ((p.γ * Ccorr) * (Real.sqrt M₂ + (J : ℝ))) *
            cbNorm (fp81s21_J1 p.d) qj := by ring
        _ ≤ K * cbNorm (fp81s21_J1 p.d) qj :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hqnorm0
    let F : InitialFamData R (r26t3_qwin R (a : ℝ)) := by
      refine ⟨K, hK, fun j => p.γ • χ j, ?_, hderiv, ?_, ?_, ?_, ?_⟩
      · intro j
        have hs : ContDiff ℝ ((fp81s21_k0 p.d + 2 : ℕ) : WithTop ℕ∞)
            (p.γ • χ j) := (hχ j).const_smul p.γ
        exact hs.of_le (by exact_mod_cast (show fp81s21_k0 p.d + 1 ≤
          fp81s21_k0 p.d + 2 by omega))
      · intro j x
        have hχ2 : ContDiff ℝ 2 (χ j) :=
          (hχ j).of_le (by exact_mod_cast (show 2 ≤ fp81s21_k0 p.d + 2 by omega))
        rw [fp81s21_weightedGen_smul (R.ρ 0) (χ j) p.γ x hχ2, hχgen j x]
      · intro j
        let qj := r26t3_qwin R (a : ℝ) j
        obtain ⟨hRa, hRc, hRL, heq⟩ := hresponse qj ((hwin a ha).1.1 j)
        exact ⟨hRL, Filter.Eventually.of_forall heq⟩
      · intro j
        let qj := r26t3_qwin R (a : ℝ) j
        obtain ⟨hRa, -, -, -⟩ := hresponse qj ((hwin a ha).1.1 j)
        exact (HRS.MS.Tc5.tc5_cb_mono
          (m := fp81s21_k0 p.d) (J := r26t3_k p.d + 2)
          (by simp [fp81s21_k0, r26t3_k]) hRa).1
      · intro j
        let qj := r26t3_qwin R (a : ℝ) j
        obtain ⟨hRa, hRc, -, -⟩ := hresponse qj ((hwin a ha).1.1 j)
        have hnorm : 0 ≤ cbNorm (fp81s21_J1 p.d) qj :=
          HRS.MS.Tc5.tc5_cb_nonneg (fp81s21_J1 p.d) qj
        have hmono := (HRS.MS.Tc5.tc5_cb_mono
          (m := fp81s21_k0 p.d) (J := r26t3_k p.d + 2)
          (by simp [fp81s21_k0, r26t3_k]) hRa).2
        calc
          cbNorm (fp81s21_k0 p.d) (r26t3_a R qj) ≤
              cbNorm (r26t3_k p.d + 2) (r26t3_a R qj) := hmono
          _ ≤ Ca * cbNorm (r26t3_J p.d) qj := hRc
          _ = Ca * cbNorm (fp81s21_J1 p.d) qj := by rw [hJd]
          _ ≤ K * cbNorm (fp81s21_J1 p.d) qj :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hnorm
    refine ⟨F, le_rfl, ?_⟩
    intro j
    let qj := r26t3_qwin R (a : ℝ) j
    have hχ1 : ContDiff ℝ 1 (χ j) :=
      (hχ j).of_le (by exact_mod_cast (show 1 ≤ fp81s21_k0 p.d + 2 by omega))
    have hgradEq : gradient (p.γ • χ j) =
        fun y => p.γ • gradient (χ j) y := by
      funext y
      exact fp81s21_gradient_smul (χ j) p.γ y hχ1
    refine ⟨?_, ?_⟩
    · rw [hgradEq]
      exact HRS.MS.S98.s98_gL_contDiff
        ((hχ j).of_le (by exact_mod_cast (show fp81s21_k0 p.d + 1 ≤
          fp81s21_k0 p.d + 2 by omega))) p.γ
    · intro i hi x
      rw [hgradEq]
      have hscale := HRS.MS.S98.s98_gL_iter
        ((hχ j).of_le (by exact_mod_cast (show fp81s21_k0 p.d + 1 ≤
          fp81s21_k0 p.d + 2 by omega))) p.γ hi x
      rw [abs_of_pos hγ] at hscale
      have hpoint := (hχgrad j).2 i hi x
      rw [HRS.MS.Gap.gap1_norm_iter_gradient] at hpoint
      calc
        ‖iteratedFDeriv ℝ i (fun y => p.γ • gradient (χ j) y) x‖ ≤
            p.γ * ‖iteratedFDeriv ℝ (i + 1) (χ j) x‖ := hscale
        _ ≤ p.γ * (Ccorr * HRS.MS.S48.s48_Q
            (r26t3_mu R 0) J qj) := mul_le_mul_of_nonneg_left
              hpoint hγ.le
        _ = (p.γ * Ccorr) * HRS.MS.S48.s48_Q
            (r26t3_mu R 0) J qj := by ring
        _ ≤ (p.γ * Ccorr) *
            (Cq * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j) :=
          mul_le_mul_of_nonneg_left (hQdecay (a : ℝ) ha j)
            (mul_nonneg hγ.le hCcorr)
        _ = C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j := by
          dsimp [C]
          ring
  let F : fp81s21_CompatPotentialFamily R :=
    fun a => Classical.choose (hdata a)
  have hF : (∀ a : Set.Ici (0 : ℝ), (F a).K ≤ K) ∧
      (∀ a : Set.Ici (0 : ℝ), ∀ j : ℕ, HasCbBound (fp81s21_k0 p.d)
        (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j)
        (gradient ((F a).χ j))) := by
    constructor
    · intro a
      exact (Classical.choose_spec (hdata a)).1
    · intro a j
      exact (Classical.choose_spec (hdata a)).2 j
  exact ⟨K, C, c, hK, hC, hc, F, hF⟩

#print axioms HRS.Fp81.S21.fp81s21_cb_iter_le_of_memCb
#print axioms HRS.Fp81.S21.fp81s21_gradient_smul
#print axioms HRS.Fp81.S21.fp81s21_CompatPotentialFamily
#print axioms HRS.Fp81.S21.fp81s21_compatible_qwin_potentials

end HRS.Fp81.S21

end
