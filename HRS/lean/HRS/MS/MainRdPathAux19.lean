import HRS.MS.MainRdPathAux18

/-!
# S.A.9, packet P3m: second moments of the initial and martingale terms, `L¹` of the remainder
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdInit
  HRS.MP.RdMart HRS.MP.RdRem HRS.MP.RdProp HRS.MS.MainRdField HRS.MP.KC

variable {d : ℕ} {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {Γ : ℕ}

theorem sa9_Iq_moment (B : Sa9Bundle S R Γ) {Cin : ℝ} {εf : ℕ → ℝ} {Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (Γ : ℝ)}
    (hTIF : TransportedInitialFieldRd S R Γ Cin εf Iemp I) {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S.T) :
    ∫⁻ ζ, ENNReal.ofReal (‖B.Iq N t ζ‖ ^ 2) ∂(R N).P ≤ ENNReal.ofReal (Cin ^ 2) := by
  obtain ⟨ι, hι⟩ := sa9_exists_lift (d := d) (Nat.le_add_right Γ 2)
  have hq : (Γ : ℝ) ≤ ((Γ + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right Γ 2
  have hnorm : ∀ F : HNeg d (Γ : ℝ), ‖ι F‖ ≤ ‖F‖ := fun F => by
    refine hneg_norm_le_of_pairing _ _ (norm_nonneg _) fun φ hφ => ?_
    rw [hι F φ hφ]
    exact (hneg_pairing_le (sa9_test_mono (Nat.le_add_right Γ 2) hφ) F).trans
      (mul_le_mul_of_nonneg_left (HRS.MP.RdRem.mrr_sobolevNorm_mono hq hφ.2) (norm_nonneg _))
  have hae : ∀ᵐ ζ ∂(R N).P, B.Iq N t ζ = ι (Iemp N t ζ) := by
    have := mrm_ae_eq_of_pairings (μ := (R N).P) (F := B.Iq N t) (G := fun ζ => ι (Iemp N t ζ))
      (fun _ => True) (fun ℓ => by
        have hφ := mrm_e_test (d := d) ((Γ + 2 : ℕ) : ℝ) ℓ
        filter_upwards [B.hIqp N hN t ht _ hφ, hTIF.repr_emp N hN t ht _ (sa9_test_mono (Nat.le_add_right Γ 2) hφ)]
          with ζ h1 h2 _
        rw [h1, hι _ _ hφ, h2])
    filter_upwards [this] with ζ h using h trivial
  have h1 : ∫⁻ ζ, ENNReal.ofReal (‖B.Iq N t ζ‖ ^ 2) ∂(R N).P ≤ ∫⁻ ζ, ‖Iemp N t ζ‖ₑ ^ 2 ∂(R N).P := by
    refine lintegral_mono_ae (hae.mono fun ζ h => ?_)
    rw [h, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hnorm _) 2)
  exact h1.trans (le_trans le_self_add (hTIF.moment N hN t ht))

theorem sa9_Mq_moment (B : Sa9Bundle S R Γ) (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d ((Γ + 2 : ℕ) : ℝ),
      HasSum (fun n => (inner ℝ (mhn_rep ((Γ + 2 : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2))
    {m₀ : ℕ} {Kadj : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hadj : AdjointInputOneD ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) (S.coeff N) S.T Kadj) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S.T) :
    ∫⁻ ζ, ENNReal.ofReal (‖B.Mq N t ζ‖ ^ 2) ∂(R N).P ≤ ENNReal.ofReal (2 * d * Kadj ^ 2 * t) := by
  classical
  have hN0 : 0 < N := hN
  set cN : ℝ := S.sigma N * Real.sqrt (2 * S.invβ N) / N with hcN
  have hcN2 : cN ^ 2 * N ≤ 2 := mrm_cN_sq S hN0
  have hc := sa9_cH_parseval (q := Γ + 2) h hP
  have e1 : ∀ ζ, ENNReal.ofReal (‖B.Mq N t ζ‖ ^ 2) =
      ∑' l, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h (l + 0))) (B.Mq N t ζ)) ^ 2) := fun ζ => by
    have := sa9_ofReal_tail hc 0 (B.Mq N t ζ)
    simp only [sa9_tail, Finset.range_zero, Finset.sum_empty, sub_zero] at this
    rw [this]
    simp only [sa9_cH_apply]
  simp_rw [e1]
  rw [sa9_Mq_tail_eq B h hN hadj ht 0]
  have hpt : ∀ ζ, ∀ r ∈ Set.Icc (0 : ℝ) t, ∑ ia : Fin N × Fin d, ENNReal.ofReal (cN ^ 2) *
      sa9_Tm h (S.coeff N) t ia.2 0 (r, (R N).X (Real.toNNReal (mrrClamp S.T r)) ζ ia.1) ≤
      ENNReal.ofReal (2 * d * Kadj ^ 2) := by
    intro ζ r hr
    calc ∑ ia : Fin N × Fin d, ENNReal.ofReal (cN ^ 2) *
          sa9_Tm h (S.coeff N) t ia.2 0 (r, (R N).X (Real.toNNReal (mrrClamp S.T r)) ζ ia.1)
        ≤ ∑ _ia : Fin N × Fin d, ENNReal.ofReal (cN ^ 2) * ENNReal.ofReal (Kadj ^ 2) :=
          Finset.sum_le_sum fun ia _ => mul_le_mul' le_rfl (sa9_Tm_le hadj h hP ht.2 _ _ _ _)
      _ = ENNReal.ofReal (cN ^ 2 * N * d * Kadj ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
            nsmul_eq_mul, show (cN ^ 2 * N * d * Kadj ^ 2) = ((N * d : ℕ) : ℝ) * (cN ^ 2 * Kadj ^ 2) by
              push_cast; ring, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
            ENNReal.ofReal_mul (sq_nonneg _)]
      _ ≤ ENNReal.ofReal (2 * d * Kadj ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have : cN ^ 2 * N * d * Kadj ^ 2 = (cN ^ 2 * N) * (d * Kadj ^ 2) := by ring
          rw [this]
          nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) (sq_nonneg Kadj)]
  calc ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) t, ∑ ia : Fin N × Fin d, ENNReal.ofReal (cN ^ 2) *
        sa9_Tm h (S.coeff N) t ia.2 0 (r, (R N).X (Real.toNNReal (mrrClamp S.T r)) ζ ia.1)) ∂(R N).P
      ≤ ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal (2 * d * Kadj ^ 2)) ∂(R N).P :=
        lintegral_mono fun ζ => setLIntegral_mono' measurableSet_Icc (hpt ζ)
    _ = ENNReal.ofReal (2 * d * Kadj ^ 2 * t) := by
        rw [lintegral_const, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_Icc, sub_zero, measure_univ, mul_one]
        exact (ENNReal.ofReal_mul (by positivity)).symm

end HRS.MS.MainRdPath
