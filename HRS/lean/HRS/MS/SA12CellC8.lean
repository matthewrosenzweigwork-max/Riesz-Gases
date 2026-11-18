import HRS.MS.SA12CellC8B
import HRS.MS.UniqC3

/-!
# S.A.12 C8: differentiation of the moving compact cell energy
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

/-- The derivative of a single term `∫ (χ_c^τ ∂^idx F)²`. -/
theorem sa12y_cell_term (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh)
    (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d) (hb : IsAdvectingDrift m Cb T b)
    (hΨ : IsNegDriftFlow T b Ψ) (ν : ℝ) (G : ℝ → Euc d → ℝ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (F : ℝ → Euc d → ℝ) (hF : IsClassicalSol m ν b G t F) (c : Euc d) (j : ℕ) (hj : j ≤ m)
    (idx : Fin j → Fin d) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) t) :
    HasDerivWithinAt (fun τ' => ∫ x, (advCutoff χ Ψ τ' c x * partialDeriv idx (F τ') x) ^ 2)
      (∫ x, (2 * advCutoff χ Ψ τ c x ^ 2 * (partialDeriv idx (F τ) x *
          partialDeriv idx (fun y => ν * Laplacian.laplacian (F τ) y +
            inner ℝ (b τ y) (gradient (F τ) y) + G τ y) x) +
        2 * advCutoff χ Ψ τ c x * inner ℝ (b τ x) (gradient (advCutoff χ Ψ τ c) x) *
          partialDeriv idx (F τ) x ^ 2)) (Icc (0 : ℝ) t) τ := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have htT : t ≤ T := ht.2
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right htT
  have hfl := HRS.MS.UniqC3.uc3_flowFacts hT hb hΨ
  have hinv := HRS.MS.UniqC3.uc3_hinv hΨ
  obtain ⟨B, R1, hB0, hR1, hBR⟩ := HRS.MH.AdjointRd.Phase2SA12.advected_cutoff_jets d hd m Cb T χ χh hχ
  -- the uniform support radius
  obtain ⟨Mc, hMc⟩ : ∃ Mc : ℝ, ∀ σ ∈ Icc (0 : ℝ) t, ‖Ψ σ c‖ ≤ Mc := by
    have hcomp : IsCompact (Icc (0 : ℝ) t ×ˢ ({c} : Set (Euc d))) := isCompact_Icc.prod isCompact_singleton
    have hcont : ContinuousOn (fun p : ℝ × Euc d => Ψ p.1 p.2) (Icc (0 : ℝ) t ×ˢ ({c} : Set (Euc d))) :=
      hfl.cont.mono (prod_mono (Icc_subset_Icc_right htT) (subset_univ _))
    obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont
    exact ⟨M, fun σ hσ => hM (σ, c) ⟨hσ, rfl⟩⟩
  set R0 : ℝ := |Mc| + 2 * Real.exp (|Cb| * T) with hR0
  have hcutsupp : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, R0 < ‖x‖ → advCutoff χ Ψ σ c x = 0 := by
    intro σ hσ x hx
    by_contra hne
    have hσT : σ ∈ Icc (0 : ℝ) T := hsub hσ
    have hmem : Function.invFun (Ψ σ) x - c ∈ tsupport χ := subset_tsupport χ hne
    have h2 := hχ.1.2.2.1 hmem
    rw [Metric.mem_ball, dist_zero_right] at h2
    have hlip := hfl.lip σ hσT (Function.invFun (Ψ σ) x) c
    rw [hinv σ hσT |>.2 x] at hlip
    have hexp : Real.exp (Cb * σ) ≤ Real.exp (|Cb| * T) := by
      refine Real.exp_le_exp.2 ?_
      calc Cb * σ ≤ |Cb| * σ := mul_le_mul_of_nonneg_right (le_abs_self Cb) hσ.1
        _ ≤ |Cb| * T := mul_le_mul_of_nonneg_left hσT.2 (abs_nonneg _)
    have h3 : ‖x - Ψ σ c‖ ≤ 2 * Real.exp (|Cb| * T) := by
      calc ‖x - Ψ σ c‖ ≤ Real.exp (Cb * σ) * ‖Function.invFun (Ψ σ) x - c‖ := hlip
        _ ≤ Real.exp (|Cb| * T) * 2 := mul_le_mul hexp (by rw [sub_eq_add_neg] at h2 ⊢; linarith [norm_nonneg (Function.invFun (Ψ σ) x - c)]) (norm_nonneg _) (Real.exp_pos _).le
        _ = _ := mul_comm _ _
    have h4 : ‖x‖ ≤ ‖Ψ σ c‖ + 2 * Real.exp (|Cb| * T) := by
      calc ‖x‖ = ‖(x - Ψ σ c) + Ψ σ c‖ := by simp
        _ ≤ ‖x - Ψ σ c‖ + ‖Ψ σ c‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have := hMc σ hσ
    have h5 : ‖x‖ ≤ R0 := by rw [hR0]; linarith [le_abs_self Mc]
    linarith
  have hcutd := HRS.MS.FlowD.flow_cutoff_hasDerivWithinAt hT (HRS.MS.UniqC3.uc3_drift hb)
    (HRS.MS.UniqC3.uc3_flow hΨ) (fun τ => Function.invFun (Ψ τ)) hinv χ hχ.1.1 c
  obtain ⟨KF, hKF⟩ := sa12y_jet_bound hF.contF j R0
  obtain ⟨KD, hKD⟩ := sa12y_rate_bound hb hF htT R0 (by positivity) j hj
  set KF' : ℝ := |KF| with hKF'
  set KD' : ℝ := |KD| with hKD'
  set Gb : ℝ := |Cb| * (1 + R0) * B with hGb
  have hKF0 : 0 ≤ KF' := abs_nonneg _
  have hKD0 : 0 ≤ KD' := abs_nonneg _
  have hGb0 : 0 ≤ Gb := by rw [hGb]; positivity
  set Kc : ℝ := KF' ^ 2 + 2 * (KF' * KD') + 2 * Gb * KF' ^ 2 with hKc
  have hw01 : ∀ σ (x : Euc d), |advCutoff χ Ψ σ c x| ≤ 1 := by
    intro σ x
    have := hχ.1.2.2.2.1 (Function.invFun (Ψ σ) x - c)
    show |χ (Function.invFun (Ψ σ) x - c)| ≤ 1
    rw [abs_of_nonneg this.1]
    exact this.2
  have hpF : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R0 → |partialDeriv idx (F σ) x| ≤ KF' := by
    intro σ hσ x hx
    refine (HRS.MP.RdInit.mri_abs_partialDeriv_le idx _ x).trans ((hKF σ hσ x hx).trans (le_abs_self _))
  have hDd : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R0 →
      |partialDeriv idx (fun y => ν * Laplacian.laplacian (F σ) y +
        inner ℝ (b σ y) (gradient (F σ) y) + G σ y) x| ≤ KD' := fun σ hσ x hx =>
    (hKD idx σ hσ x hx).trans (le_abs_self _)
  have hwg : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R0 →
      |inner ℝ (b σ x) (gradient (advCutoff χ Ψ σ c) x)| ≤ Gb := by
    intro σ hσ x hx
    have hσT : σ ∈ Icc (0 : ℝ) T := hsub hσ
    refine (abs_real_inner_le_norm _ _).trans ?_
    have h1 : ‖b σ x‖ ≤ |Cb| * (1 + R0) := by
      refine (hb.growth σ hσT x).trans ?_
      have : 1 + ‖x‖ ≤ 1 + R0 := by linarith
      nlinarith [le_abs_self Cb, abs_nonneg Cb, norm_nonneg x]
    have h2 : ‖gradient (advCutoff χ Ψ σ c) x‖ ≤ B := by
      have e : ‖gradient (advCutoff χ Ψ σ c) x‖ = ‖iteratedFDeriv ℝ 1 (advCutoff χ Ψ σ c) x‖ := by
        rw [norm_iteratedFDeriv_one]
        exact (InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map _
      rw [e]
      exact ((hBR b Ψ hb hΨ σ hσT c).2.1 1 (by omega) x).1
    rw [hGb]
    exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  have hcontx : ∀ σ ∈ Icc (0 : ℝ) t, Continuous (fun x => advCutoff χ Ψ σ c x * partialDeriv idx (F σ) x) := by
    intro σ hσ
    have hσT : σ ∈ Icc (0 : ℝ) T := hsub hσ
    have h1 : Continuous (advCutoff χ Ψ σ c) :=
      hχ.1.1.continuous.comp ((hfl.contDiff_inv σ hσT).continuous.sub continuous_const)
    have h2 : Continuous (partialDeriv idx (F σ)) := by
      have := (hF.smooth σ hσ).1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)
      exact (continuous_eval_const _).comp this
    exact h1.mul h2
  refine sa12y_param_deriv (K := Kc) (R := R0)
    (f := fun σ x => (advCutoff χ Ψ σ c x * partialDeriv idx (F σ) x) ^ 2)
    (f' := fun σ x => 2 * advCutoff χ Ψ σ c x ^ 2 * (partialDeriv idx (F σ) x *
          partialDeriv idx (fun y => ν * Laplacian.laplacian (F σ) y +
            inner ℝ (b σ y) (gradient (F σ) y) + G σ y) x) +
        2 * advCutoff χ Ψ σ c x * inner ℝ (b σ x) (gradient (advCutoff χ Ψ σ c) x) *
          partialDeriv idx (F σ) x ^ 2) ?_ ?_ ?_ ?_ ?_ hτ
  · intro σ hσ
    exact ((hcontx σ hσ).pow 2).aestronglyMeasurable
  · intro σ hσ x hx
    show (advCutoff χ Ψ σ c x * partialDeriv idx (F σ) x) ^ 2 = 0
    rw [hcutsupp σ hσ x hx]; simp
  · intro σ hσ x
    show |(advCutoff χ Ψ σ c x * partialDeriv idx (F σ) x) ^ 2| ≤ Kc
    by_cases hx : ‖x‖ ≤ R0
    · rw [abs_pow, abs_mul]
      have := mul_le_mul (hw01 σ x) (hpF σ hσ x hx) (abs_nonneg _) zero_le_one
      rw [one_mul] at this
      calc (|advCutoff χ Ψ σ c x| * |partialDeriv idx (F σ) x|) ^ 2 ≤ KF' ^ 2 :=
            pow_le_pow_left₀ (by positivity) this 2
        _ ≤ Kc := by rw [hKc]; nlinarith [mul_nonneg hKF0 hKD0, mul_nonneg hGb0 (sq_nonneg KF')]
    · push Not at hx
      rw [hcutsupp σ hσ x hx]
      simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, abs_zero]
      rw [hKc]; positivity
  · intro x σ hσ
    have hσT : σ ∈ Icc (0 : ℝ) T := hsub hσ
    have hw' := (hcutd x σ hσT).mono hsub
    have hp' := hF.deriv_t j hj idx x σ hσ
    have := (hw'.mul hp').pow 2
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.mul_apply]
    unfold advCutoff
    ring
  · intro σ hσ x hx
    show |2 * advCutoff χ Ψ σ c x ^ 2 * (partialDeriv idx (F σ) x * _) +
      2 * advCutoff χ Ψ σ c x * inner ℝ (b σ x) (gradient (advCutoff χ Ψ σ c) x) * partialDeriv idx (F σ) x ^ 2| ≤ Kc
    have hw := hw01 σ x
    have hwsq : advCutoff χ Ψ σ c x ^ 2 ≤ 1 := by
      calc advCutoff χ Ψ σ c x ^ 2 = |advCutoff χ Ψ σ c x| ^ 2 := (sq_abs _).symm
        _ ≤ 1 := pow_le_one₀ (abs_nonneg _) hw
    have hp := hpF σ hσ x hx
    have hD := hDd σ hσ x hx
    have hg := hwg σ hσ x hx
    refine (abs_add_le _ _).trans ?_
    have t1 : |2 * advCutoff χ Ψ σ c x ^ 2 * (partialDeriv idx (F σ) x *
        partialDeriv idx (fun y => ν * Laplacian.laplacian (F σ) y +
          inner ℝ (b σ y) (gradient (F σ) y) + G σ y) x)| ≤ 2 * (KF' * KD') := by
      have hpd : |partialDeriv idx (F σ) x| * |partialDeriv idx (fun y => ν * Laplacian.laplacian (F σ) y +
          inner ℝ (b σ y) (gradient (F σ) y) + G σ y) x| ≤ KF' * KD' :=
        mul_le_mul hp hD (abs_nonneg _) hKF0
      have hw2 : |advCutoff χ Ψ σ c x| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hw
      calc _ = 2 * (|advCutoff χ Ψ σ c x| ^ 2 * (|partialDeriv idx (F σ) x| *
            |partialDeriv idx (fun y => ν * Laplacian.laplacian (F σ) y +
              inner ℝ (b σ y) (gradient (F σ) y) + G σ y) x|)) := by
            simp only [abs_mul, abs_pow, abs_two]; ring
        _ ≤ 2 * (1 * (KF' * KD')) := by
            gcongr
        _ = _ := by ring
    have t2 : |2 * advCutoff χ Ψ σ c x * inner ℝ (b σ x) (gradient (advCutoff χ Ψ σ c) x) *
        partialDeriv idx (F σ) x ^ 2| ≤ 2 * Gb * KF' ^ 2 := by
      have h3 : |partialDeriv idx (F σ) x| ^ 2 ≤ KF' ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hp 2
      calc _ = 2 * (|advCutoff χ Ψ σ c x| * |inner ℝ (b σ x) (gradient (advCutoff χ Ψ σ c) x)| *
            |partialDeriv idx (F σ) x| ^ 2) := by
            simp only [abs_mul, abs_pow, abs_two]; ring
        _ ≤ 2 * (1 * Gb * KF' ^ 2) := by
            gcongr
        _ = _ := by ring
    rw [hKc]
    nlinarith [sq_nonneg KF']

/-- C8: differentiation of the moving compact cell energy. -/
theorem cell_energy_derivative (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh)
    (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d) (hb : IsAdvectingDrift m Cb T b) (hΨ : IsNegDriftFlow T b Ψ)
    (ν : ℝ) (G : ℝ → Euc d → ℝ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (F : ℝ → Euc d → ℝ)
    (hF : IsClassicalSol m ν b G t F) (c : Euc d) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) t) :
    HasDerivWithinAt (fun τ' => cellEnergy m χ Ψ τ' c (F τ')) (cellRate m χ Ψ τ c ν (b τ) (F τ) (G τ))
      (Icc (0 : ℝ) t) τ := by
  unfold cellEnergy jetSq cellRate
  refine HasDerivWithinAt.fun_sum (fun j hj => ?_)
  refine HasDerivWithinAt.const_mul _ ?_
  refine HasDerivWithinAt.fun_sum (fun idx _ => ?_)
  exact sa12y_cell_term hd m Cb T χ χh hχ b Ψ hb hΨ ν G t ht F hF c j
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) idx τ hτ

end HRS.MH.AdjointRd.Phase2SA12Construction
