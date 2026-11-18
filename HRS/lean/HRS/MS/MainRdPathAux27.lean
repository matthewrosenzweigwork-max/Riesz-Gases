import HRS.MS.MainRdPathAux26
import HRS.MS.IidInitTie

/-!
# S.A.10, part 1: fixed-time `W₁` convergence of an arbitrary representative of the Gaussian transported field

Single-time variant of `HRS.MS.IidInit.sa27_fixed_time` (first conjunct): the limit field `J` and the representatives
`I' N` are given at the one time `t` only (as in `TransportedConvergesFixedTime`), no path structure is needed.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.MP.HNegInfra HRS.MP.RdProp HRS.U5 HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
  HRS.MS.IidInit
open HRS.Whole.AppendixALemmas (AdjointInputOneD AdjointDerivInput)

variable {d : ℕ}

theorem sa9_fix_w1 (S : WholeMainData d) (L : LimitCoeffsRd d) (R : ∀ N, RealizationRd d N)
    (hid : IidSettingRd S R) (q m m₀ : ℕ) (Kadj Kst : ℝ)
    (hm₀ : 1 ≤ m₀)
    (hAdj : AdjointDerivInput (q : ℝ) (m₀ + 1) S.coeff S.T Kadj)
    (hAdjL : AdjointInputOneD (q : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj)
    (hStab : AdjointStabilityInputRd S L q (m₀ + 1) m Kst)
    (hΔ : Tendsto (fun N => coeffDiscrepancyRd S L m N) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T)
    (I' : ∀ N, (R N).Ω → HNeg d (q : ℝ))
    (hI' : ∀ N : ℕ, 1 ≤ N → Measurable (I' N) ∧ ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ →
      ∀ᵐ ζ ∂(R N).P, HNeg.pairing φ (I' N ζ) = S.AN N * (R N).η ζ (propagatorW (S.coeff N) 0 t φ))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η' : Ω' → (Euc d → ℝ) → ℝ) (hη' : IsGaussianBridgeW P' S.μ0 η')
    (J : Ω' → HNeg d (q : ℝ)) (hJm : Measurable J)
    (hJ : ∀ φ, IsSobolevTest (q : ℝ) φ → ∀ᵐ ζ ∂P',
      HNeg.pairing φ (J ζ) = L.A * η' ζ (propagatorW (L.coeff S) 0 t φ)) :
    Tendsto (fun n : ℕ => wassersteinE 1 (law (R (n + 1)).P (I' (n + 1))) (law P' J))
      atTop (𝓝 0) := by
  haveI := S.hμ0
  have hj : 1 ≤ m₀ + 1 := by omega
  have hFI := sa27_fieldInput hj hAdj
  -- representatives of `A_N η'(U_N ·)` on `Ω'`
  obtain ⟨C₂, hC₂⟩ := iid_init_field_rd_proof (d := d) S.hd q S.T ((1 + d) * Kadj) (∫ x, ‖x‖ ^ 2 ∂S.μ0)
  have hex : ∀ n : ℕ, ∃ Y : Ω' → HNeg d (q : ℝ), Measurable Y ∧ ∀ φ, IsSobolevTest (q : ℝ) φ →
      ∀ᵐ ζ ∂P', HNeg.pairing φ (Y ζ) = S.AN (n + 1) * η' ζ (propagatorW (S.coeff (n + 1)) 0 t φ) := by
    intro n
    have h := hC₂ S.coeff S.invβ S.hinvβ hFI S.μ0 S.hμ0 hid.second_moment le_rfl (n + 1)
      (by omega) t ht
    obtain ⟨Y, hYm, hY⟩ := h.2.1 P' η' hη'
    refine ⟨Y, hYm, fun φ hφ => ?_⟩
    filter_upwards [hY φ hφ] with ζ hζ
    rw [hζ, sa27_fieldAmp_eq S hid.kappa (n + 1) (by omega)]
  choose Y hYm hY using hex
  -- bounds on the amplitude and the discrepancy
  have hA : ∀ N : ℕ, 1 ≤ N → 0 ≤ S.AN N ∧ S.AN N ≤ 1 := fun N hN => by
    rw [sa27_fieldAmp_eq S hid.kappa N hN]
    exact u5_fieldAmp_bounds N hN (S.invβ N) (S.hinvβ N)
  have hfin : ∀ᶠ n : ℕ in atTop, coeffDiscrepancyRd S L m (n + 1) ≠ ⊤ := by
    have := (hΔ.comp (tendsto_add_atTop_nat 1)).eventually (eventually_lt_nhds ENNReal.zero_lt_top)
    exact this.mono fun n hn => hn.ne
  set Dr : ℕ → ℝ := fun n => (coeffDiscrepancyRd S L m (n + 1)).toReal with hDr
  have hDr0 : Tendsto Dr atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hΔ.comp (tendsto_add_atTop_nat 1))
    simpa [Function.comp_def, hDr] using this
  set Bn : ℕ → ℝ := fun n => (max Kst 0 + max Kadj 0) * Dr n with hBn
  have hBn0 : Tendsto Bn atTop (𝓝 0) := by
    simpa [hBn] using hDr0.const_mul (max Kst 0 + max Kadj 0)
  -- the laws of `Jq` and `Y` agree
  have hlaw : ∀ n : ℕ, law (R (n + 1)).P (I' (n + 1)) = law P' (Y n) := by
    intro n
    haveI : IsProbabilityMeasure (law (R (n + 1)).P (I' (n + 1))) :=
      inferInstance
    haveI : IsProbabilityMeasure (law P' (Y n)) := inferInstance
    refine sa27_hneg_ext (q : ℝ) _ _ fun p g => ?_
    obtain ⟨hf1, hl1⟩ := sa27_psi_facts hj (hAdj (n + 1) (by omega)) ht
    have hψ : ∀ j : Fin p, MemCb 1 (propagatorW (S.coeff (n + 1)) 0 t (g j).1) :=
      fun j => (hf1 _ (g j).2).1
    have hmeasF : Measurable (sa27_fd (sa27_pf d (q : ℝ)) g) :=
      (sa27_fd_continuous (sa27_pf d (q : ℝ)) (sa27_pf_continuous (q : ℝ)) g).measurable
    rw [Measure.map_map hmeasF (hI' (n + 1) (by omega)).1,
      Measure.map_map hmeasF (hYm n)]
    have e1 : (R (n + 1)).P.map (fun ζ => sa27_fd (sa27_pf d (q : ℝ)) g (I' (n + 1) ζ)) =
        (R (n + 1)).P.map (fun ζ => (WithLp.toLp 2 fun c => S.AN (n + 1) *
          (R (n + 1)).η ζ (propagatorW (S.coeff (n + 1)) 0 t (g c).1) :
            EuclideanSpace ℝ (Fin p))) := Measure.map_congr (sa27_vec_law_ae (S.AN (n + 1)) (R (n + 1)).P (R (n + 1)).η
      (propagatorW (S.coeff (n + 1)) 0 t) (I' (n + 1))
      (fun φ hφ => by
        exact (hI' (n + 1) (by omega)).2 φ hφ) g)
    have e2 : P'.map (fun ζ => sa27_fd (sa27_pf d (q : ℝ)) g (Y n ζ)) =
        P'.map (fun ζ => (WithLp.toLp 2 fun c => S.AN (n + 1) *
          η' ζ (propagatorW (S.coeff (n + 1)) 0 t (g c).1) : EuclideanSpace ℝ (Fin p))) :=
      Measure.map_congr (sa27_vec_law_ae (S.AN (n + 1)) P' η'
      (propagatorW (S.coeff (n + 1)) 0 t) (Y n) (hY n) g)
    have hb1 := sa27_bridge_vec_diag S.μ0 (S.AN (n + 1)) (R (n + 1)).P (R (n + 1)).η
      (hid.bridge (n + 1) (by omega)).1 (hid.bridge (n + 1) (by omega)).2
      (fun j => propagatorW (S.coeff (n + 1)) 0 t (g j).1) hψ
    have hb2 := sa27_bridge_vec_diag S.μ0 (S.AN (n + 1)) P' η' hη'.1 hη'.2
      (fun j => propagatorW (S.coeff (n + 1)) 0 t (g j).1) hψ
    rw [Function.comp_def, Function.comp_def]
    rw [e1, e2, hb1, hb2]
  -- `W₁` between `Jq` and `J t`
  have hJW : ∀ᶠ n : ℕ in atTop,
      wassersteinE 1 (law (R (n + 1)).P (I' (n + 1))) (law P' J) ≤ ENNReal.ofReal (Bn n) := by
    filter_upwards [hfin] with n hn
    rw [hlaw n]
    have hcoup := sa27_time_coupling S L q m m₀ Kadj Kst hm₀ hAdj hAdjL hStab (n + 1) (by omega) hn
      (hA (n + 1) (by omega)).2 (hA (n + 1) (by omega)).1 ht P' η' hη' (Y n) J (hY n) hJ
    have hB0 : 0 ≤ Bn n := mul_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _))
      ENNReal.toReal_nonneg
    refine le_trans (wassersteinE_one_le_two _ _) ?_
    refine le_trans (wassersteinE_le_of_coupling P' 2 (by norm_num) (Y n) J
      (hYm n).aemeasurable hJm.aemeasurable) ?_
    have h2 : ∫⁻ ω, ENNReal.ofReal (‖Y n ω - J ω‖ ^ (2 : ℝ)) ∂P' ≤ ENNReal.ofReal (Bn n ^ 2) := by
      refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hcoup
      rw [Real.rpow_two, sa27_enorm_sq]
    refine le_trans (ENNReal.rpow_le_rpow h2 (by norm_num)) ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    refine le_of_eq ?_
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB0]
    norm_num
  have hJT : Tendsto (fun n : ℕ => wassersteinE 1 (law (R (n + 1)).P (I' (n + 1))) (law P' J))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_ (Eventually.of_forall fun _ => zero_le) hJW
    have := (ENNReal.tendsto_ofReal hBn0)
    simpa using this
  exact hJT

end HRS.MS.MainRdPath
