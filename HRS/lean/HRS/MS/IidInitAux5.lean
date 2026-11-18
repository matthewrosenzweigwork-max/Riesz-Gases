import HRS.MS.IidInitAux4
import HRS.MS.SuppU5M

/-!
# SA27, part 5: fixed-time convergence in `H^{-q}`

For `t ∈ [0,T]` the laws of the transported fields `Iq N t` (empirical) and `Jq N t` (Gaussian bridge) converge to the law of
`J t` (the limit field) in `W₁` on `H^{-q}(ℝ^d)`:

* `sa27_emp_vs_eta`: S.B.2 for the realizations (`X₀` replaced by a measurable version),
* `sa27_fixed_time`: the `L²` coupling `sa27_time_coupling` on the space of the limit bridge, the identity of the law of the
  Gaussian representative with the law of `Jq N t` (finite-dimensional marginals of the bridge,
  `sa27_bridge_vec_diag`, `sa27_hneg_ext`), and the triangle inequality.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

noncomputable section

namespace HRS.MS.IidInit

open HRS HRS.Whole HRS.MP.HNegInfra HRS.MP.RdProp HRS.U5 HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
open HRS.Whole.AppendixALemmas (AdjointInputOneD AdjointDerivInput)

variable {d : ℕ}

theorem sa27_fieldAmp_eq (S : WholeMainData d) (hκ : ∀ N : ℕ, 1 ≤ N → S.κ N = Real.sqrt N) (N : ℕ)
    (hN : 1 ≤ N) : S.AN N = fieldAmp N (S.invβ N) := by
  unfold WholeMainData.AN fieldAmp
  rw [hκ N hN]

theorem sa27_rate_tendsto (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-a) * Real.log ((n + 1 : ℕ) : ℝ) ^ b) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (s := a) b ha).tendsto_div_nhds_zero
  have h2 := h.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_neg (Nat.cast_nonneg _)]
  ring

theorem sa27_bridge_vec_diag (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (a : ℝ)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : Ω' → (Euc d → ℝ) → ℝ)
    (hηm : ∀ ψ : Euc d → ℝ, MemCb 1 ψ → Measurable fun ζ => η ζ ψ)
    (hη : ∀ (p : ℕ) (ψ : Fin p → Euc d → ℝ), (∀ a, MemCb 1 (ψ a)) →
      P'.map (fun ζ => (WithLp.toLp 2 fun a => η ζ (ψ a) : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a b => iidCovW μ (ψ a) (ψ b)))
    {p : ℕ} (ψ : Fin p → Euc d → ℝ) (hψ : ∀ j, MemCb 1 (ψ j)) :
    P'.map (fun ζ => (WithLp.toLp 2 fun c => a * η ζ (ψ c) : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun c c' =>
        ∑ j, ∑ j', (Matrix.diagonal (fun _ : Fin p => a) : Matrix (Fin p) (Fin p) ℝ) c j *
          (Matrix.diagonal (fun _ : Fin p => a) : Matrix (Fin p) (Fin p) ℝ) c' j' *
            iidCovW μ (ψ j) (ψ j')) := by
  have h := u5_bridge_vec_gen P' μ η hη hηm ψ hψ
    (Matrix.diagonal (fun _ : Fin p => a) : Matrix (Fin p) (Fin p) ℝ)
  convert h using 3
  ext ζ c
  simp [Matrix.diagonal_apply]

/-- Law of the vector of pairings of an `H^{-q}`-representative of `φ ↦ a η(U φ)`. -/
theorem sa27_vec_law_ae {q : ℝ} (a : ℝ) {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    (η : Ω' → (Euc d → ℝ) → ℝ) (U : (Euc d → ℝ) → Euc d → ℝ) (Y : Ω' → HNeg d q)
    (hY : ∀ φ, IsSobolevTest q φ → ∀ᵐ ζ ∂P', HNeg.pairing φ (Y ζ) = a * η ζ (U φ))
    {p : ℕ} (g : Fin p → sa27_Tst d q) :
    (fun ζ => sa27_fd (sa27_pf d q) g (Y ζ)) =ᵐ[P']
      (fun ζ => (WithLp.toLp 2 fun c => a * η ζ (U (g c).1) : EuclideanSpace ℝ (Fin p))) := by
  have : ∀ᵐ ζ ∂P', ∀ c : Fin p, HNeg.pairing (g c).1 (Y ζ) = a * η ζ (U (g c).1) :=
    ae_all_iff.2 fun c => hY _ (g c).2
  filter_upwards [this] with ζ hζ
  ext c
  simp [sa27_fd, sa27_pf, hζ c]

/-- S.B.2 for the realizations: `W₁` between the transported empirical and Gaussian fields. -/
theorem sa27_emp_vs_eta (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (hid : IidSettingRd S R) (hX0 : ∀ N : ℕ, 1 ≤ N → Measurable (R N).X₀)
    (q : ℕ) (K : ℝ) (hFI : AdjointFieldInput (q : ℝ) S.coeff S.T K)
    (Iq Jq : ∀ N, ℝ → (R N).Ω → HNeg d (q : ℝ)) (hrepr : IsInitReprRd S R q Iq Jq) :
    ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      wassersteinE 1 (law (R N).P (Iq N t)) (law (R N).P (Jq N t)) ≤
        ENNReal.ofReal (C * S.AN N * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
          Real.log N ^ (1 / (2 * (d : ℝ) + 5))) := by
  haveI := S.hμ0
  obtain ⟨C, hC⟩ := iid_init_field_rd_proof (d := d) S.hd q S.T K (∫ x, ‖x‖ ^ 2 ∂S.μ0)
  refine ⟨C, fun N hN3 t ht => ?_⟩
  have hN : 1 ≤ N := by omega
  have h := hC S.coeff S.invβ S.hinvβ hFI S.μ0 S.hμ0 hid.second_moment le_rfl N hN t ht
  have hA : S.AN N = fieldAmp N (S.invβ N) := sa27_fieldAmp_eq S hid.kappa N hN
  have key := h.2.2 (R N).P (R N).X₀ (hX0 N hN) (hid.law_init N hN) (Iq N t) (hrepr.1 N hN t).1
    (fun φ hφ => by
      filter_upwards [(hrepr.2 N hN t ht φ hφ)] with ζ h1
      rw [h1.1, hid.kappa N hN, hA]; ring)
    (R N).P (R N).η (hid.bridge N hN) (Jq N t) (hrepr.1 N hN t).2
    (fun φ hφ => by
      filter_upwards [(hrepr.2 N hN t ht φ hφ)] with ζ h1
      rw [h1.2, hA])
  rw [hA]
  exact (key.1 hN3).1

/-- Fixed-time `W₁` convergence of both transported fields to the limit field. -/
theorem sa27_fixed_time (S : WholeMainData d) (L : LimitCoeffsRd d) (R : ∀ N, RealizationRd d N)
    (hid : IidSettingRd S R) (hX0 : ∀ N : ℕ, 1 ≤ N → Measurable (R N).X₀) (q m m₀ : ℕ) (Kadj Kst : ℝ)
    (hm₀ : 1 ≤ m₀)
    (hAdj : AdjointDerivInput (q : ℝ) (m₀ + 1) S.coeff S.T Kadj)
    (hAdjL : AdjointInputOneD (q : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj)
    (hStab : AdjointStabilityInputRd S L q (m₀ + 1) m Kst)
    (hΔ : Tendsto (fun N => coeffDiscrepancyRd S L m N) atTop (𝓝 0))
    (Iq Jq : ∀ N, ℝ → (R N).Ω → HNeg d (q : ℝ)) (hrepr : IsInitReprRd S R q Iq Jq)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η' : Ω' → (Euc d → ℝ) → ℝ) (hη' : IsGaussianBridgeW P' S.μ0 η')
    (J : ℝ → Ω' → HNeg d (q : ℝ)) (hJm : ∀ t, Measurable (J t))
    (hJ : ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ φ, IsSobolevTest (q : ℝ) φ → ∀ᵐ ζ ∂P',
      HNeg.pairing φ (J t ζ) = L.A * η' ζ (propagatorW (L.coeff S) 0 t φ))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) :
    Tendsto (fun n : ℕ => wassersteinE 1 (law (R (n + 1)).P (Jq (n + 1) t)) (law P' (J t)))
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => wassersteinE 1 (law (R (n + 1)).P (Iq (n + 1) t)) (law P' (J t)))
      atTop (𝓝 0) := by
  haveI := S.hμ0
  have hj : 1 ≤ m₀ + 1 := by omega
  have hFI := sa27_fieldInput hj hAdj
  obtain ⟨C, hCb⟩ := sa27_emp_vs_eta S R hid hX0 q _ hFI Iq Jq hrepr
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
  have hlaw : ∀ n : ℕ, law (R (n + 1)).P (Jq (n + 1) t) = law P' (Y n) := by
    intro n
    haveI : IsProbabilityMeasure (law (R (n + 1)).P (Jq (n + 1) t)) :=
      inferInstance
    haveI : IsProbabilityMeasure (law P' (Y n)) := inferInstance
    refine sa27_hneg_ext (q : ℝ) _ _ fun p g => ?_
    obtain ⟨hf1, hl1⟩ := sa27_psi_facts hj (hAdj (n + 1) (by omega)) ht
    have hψ : ∀ j : Fin p, MemCb 1 (propagatorW (S.coeff (n + 1)) 0 t (g j).1) :=
      fun j => (hf1 _ (g j).2).1
    have hmeasF : Measurable (sa27_fd (sa27_pf d (q : ℝ)) g) :=
      (sa27_fd_continuous (sa27_pf d (q : ℝ)) (sa27_pf_continuous (q : ℝ)) g).measurable
    rw [Measure.map_map hmeasF (hrepr.1 (n + 1) (by omega) t).2,
      Measure.map_map hmeasF (hYm n)]
    have e1 : (R (n + 1)).P.map (fun ζ => sa27_fd (sa27_pf d (q : ℝ)) g (Jq (n + 1) t ζ)) =
        (R (n + 1)).P.map (fun ζ => (WithLp.toLp 2 fun c => S.AN (n + 1) *
          (R (n + 1)).η ζ (propagatorW (S.coeff (n + 1)) 0 t (g c).1) :
            EuclideanSpace ℝ (Fin p))) := Measure.map_congr (sa27_vec_law_ae (S.AN (n + 1)) (R (n + 1)).P (R (n + 1)).η
      (propagatorW (S.coeff (n + 1)) 0 t) (Jq (n + 1) t)
      (fun φ hφ => by
        filter_upwards [(hrepr.2 (n + 1) (by omega) t ht φ hφ)] with ζ h1
        exact h1.2) g)
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
      wassersteinE 1 (law (R (n + 1)).P (Jq (n + 1) t)) (law P' (J t)) ≤ ENNReal.ofReal (Bn n) := by
    filter_upwards [hfin] with n hn
    rw [hlaw n]
    have hcoup := sa27_time_coupling S L q m m₀ Kadj Kst hm₀ hAdj hAdjL hStab (n + 1) (by omega) hn
      (hA (n + 1) (by omega)).2 (hA (n + 1) (by omega)).1 ht P' η' hη' (Y n) (J t) (hY n) (hJ t ht)
    have hB0 : 0 ≤ Bn n := mul_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _))
      ENNReal.toReal_nonneg
    refine le_trans (wassersteinE_one_le_two _ _) ?_
    refine le_trans (wassersteinE_le_of_coupling P' 2 (by norm_num) (Y n) (J t)
      (hYm n).aemeasurable (hJm t).aemeasurable) ?_
    have h2 : ∫⁻ ω, ENNReal.ofReal (‖Y n ω - J t ω‖ ^ (2 : ℝ)) ∂P' ≤ ENNReal.ofReal (Bn n ^ 2) := by
      refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hcoup
      rw [Real.rpow_two, sa27_enorm_sq]
    refine le_trans (ENNReal.rpow_le_rpow h2 (by norm_num)) ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    refine le_of_eq ?_
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB0]
    norm_num
  have hJT : Tendsto (fun n : ℕ => wassersteinE 1 (law (R (n + 1)).P (Jq (n + 1) t)) (law P' (J t)))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_ (Eventually.of_forall fun _ => zero_le) hJW
    have := (ENNReal.tendsto_ofReal hBn0)
    simpa using this
  refine ⟨hJT, ?_⟩
  -- the empirical field
  have hrate : Tendsto (fun n : ℕ => ENNReal.ofReal (max C 0 * (((n + 1 : ℕ) : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
      Real.log ((n + 1 : ℕ) : ℝ) ^ (1 / (2 * (d : ℝ) + 5))))) atTop (𝓝 0) := by
    have h0 := (sa27_rate_tendsto (1 / (4 * (d : ℝ) + 10)) (1 / (2 * (d : ℝ) + 5)) (by positivity)).const_mul
      (max C 0)
    have := ENNReal.tendsto_ofReal h0
    simpa using this
  have hEW : ∀ᶠ n : ℕ in atTop,
      wassersteinE 1 (law (R (n + 1)).P (Iq (n + 1) t)) (law (R (n + 1)).P (Jq (n + 1) t)) ≤
        ENNReal.ofReal (max C 0 * (((n + 1 : ℕ) : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
          Real.log ((n + 1 : ℕ) : ℝ) ^ (1 / (2 * (d : ℝ) + 5)))) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    refine (hCb (n + 1) (by omega) t ht).trans (ENNReal.ofReal_le_ofReal ?_)
    obtain ⟨hA0, hA1⟩ := hA (n + 1) (by omega)
    have hl : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
        Real.log ((n + 1 : ℕ) : ℝ) ^ (1 / (2 * (d : ℝ) + 5)) := by
      have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (Real.log_nonneg h1) _)
    calc C * S.AN (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
          Real.log ((n + 1 : ℕ) : ℝ) ^ (1 / (2 * (d : ℝ) + 5))
        = (C * S.AN (n + 1)) * (((n + 1 : ℕ) : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
          Real.log ((n + 1 : ℕ) : ℝ) ^ (1 / (2 * (d : ℝ) + 5))) := by ring
      _ ≤ max C 0 * (((n + 1 : ℕ) : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
          Real.log ((n + 1 : ℕ) : ℝ) ^ (1 / (2 * (d : ℝ) + 5))) := by
          refine mul_le_mul_of_nonneg_right ?_ hl
          calc C * S.AN (n + 1) ≤ max C 0 * S.AN (n + 1) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) hA0
            _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left hA1 (le_max_right _ _)
            _ = max C 0 := mul_one _
  haveI : ∀ n, IsProbabilityMeasure (law (R (n + 1)).P (Iq (n + 1) t)) := fun n =>
    inferInstance
  haveI : ∀ n, IsProbabilityMeasure (law (R (n + 1)).P (Jq (n + 1) t)) := fun n =>
    inferInstance
  haveI : IsProbabilityMeasure (law P' (J t)) := inferInstance
  have hETop : Tendsto (fun n : ℕ => wassersteinE 1 (law (R (n + 1)).P (Iq (n + 1) t))
      (law (R (n + 1)).P (Jq (n + 1) t))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrate
      (Eventually.of_forall fun _ => zero_le) hEW
  have hsum := hETop.add hJT
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun n => ?_)
  exact wassersteinE_triangle 1 le_rfl _ (law (R (n + 1)).P (Jq (n + 1) t)) _

end HRS.MS.IidInit
