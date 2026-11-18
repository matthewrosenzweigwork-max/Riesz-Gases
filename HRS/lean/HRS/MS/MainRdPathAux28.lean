import HRS.MS.MainRdPathAux27

/-!
# S.A.10, part 2: `W₁` convergence of the multi-time empirical initial vector

Variant of the empirical part of `HRS.MS.IidInit.sa27_fdd_w1` without continuous versions of the paths: the vectors of the
transported empirical fields at finitely many times and Schwartz tests converge in `W₁` to the limit vector.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.MP.HNegInfra HRS.MP.RdProp HRS.U5 HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
  HRS.MS.IidInit
open HRS.Whole.AppendixALemmas (AdjointInputOneD AdjointDerivInput)

variable {d : ℕ}

theorem sa9_vec_w1 (S : WholeMainData d) (L : LimitCoeffsRd d) (R : ∀ N, RealizationRd d N)
    (hid : IidSettingRd S R) (hX0 : ∀ N : ℕ, 1 ≤ N → Measurable (R N).X₀) (q m m₀ : ℕ)
    (Kadj Kst : ℝ) (hm₀ : 1 ≤ m₀)
    (hAdj : AdjointDerivInput (q : ℝ) (m₀ + 1) S.coeff S.T Kadj)
    (hAdjL : AdjointInputOneD (q : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj)
    (hStab : AdjointStabilityInputRd S L q (m₀ + 1) m Kst)
    (hΔ : Tendsto (fun N => coeffDiscrepancyRd S L m N) atTop (𝓝 0))
    (Iq Jq : ∀ N, ℝ → (R N).Ω → HNeg d (q : ℝ)) (hrepr : IsInitReprRd S R q Iq Jq)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η' : Ω' → (Euc d → ℝ) → ℝ) (hη' : IsGaussianBridgeW P' S.μ0 η')
    {p : ℕ} (g : Fin p → Set.Icc (0 : ℝ) S.T × sa27_Tst d (q : ℝ)) :
    Tendsto (fun n : ℕ => wassersteinE 1
      ((R (n + 1)).P.map (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (g a).2.1
        (Iq (n + 1) ((g a).1.1) ζ) : EuclideanSpace ℝ (Fin p))))
      (P'.map (fun ζ => (WithLp.toLp 2 fun a =>
        L.A * η' ζ (propagatorW (L.coeff S) 0 ((g a).1.1) (g a).2.1) : EuclideanSpace ℝ (Fin p)))))
      atTop (𝓝 0) := by
  haveI := S.hμ0
  have hj : 1 ≤ m₀ + 1 := by omega
  have hFI := sa27_fieldInput hj hAdj
  have htsc : ∀ a, (g a).1.1 ∈ Set.Icc (0 : ℝ) S.T := fun a => (g a).1.2
  have hmeasF : Measurable (sa27_fd (sa27_pathF S.T (sa27_pf d (q : ℝ))) g) :=
    (sa27_fd_continuous _ (sa27_pathF_continuous S.T (sa27_pf d (q : ℝ)) (sa27_pf_continuous (q : ℝ)))
      g).measurable
  -- the limit vector
  set Vinf : Ω' → EuclideanSpace ℝ (Fin p) := fun ζ =>
    WithLp.toLp 2 fun a => L.A * η' ζ (propagatorW (L.coeff S) 0 ((g a).1.1) (g a).2.1) with hVinf
  have hηm : ∀ ψ : Euc d → ℝ, MemCb 1 ψ → Measurable fun ζ => η' ζ ψ := hη'.1
  have hψL : ∀ a, MemCb 1 (propagatorW (L.coeff S) 0 ((g a).1.1) (g a).2.1) := fun a =>
    ((sa27_psi_facts hj hAdjL (htsc a)).1 _ (g a).2.2).1
  have hψN : ∀ N : ℕ, 1 ≤ N → ∀ a, MemCb 1 (propagatorW (S.coeff N) 0 ((g a).1.1) (g a).2.1) :=
    fun N hN a => ((sa27_psi_facts hj (hAdj N hN) (htsc a)).1 _ (g a).2.2).1
  have hVinfm : Measurable Vinf :=
    (MeasurableEquiv.toLp 2 (Fin p → ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => (hηm _ (hψL a)).const_mul L.A)
  obtain ⟨Lc, hLc0, hLc⟩ := sa27_pairVec_lip (fun a => (g a).2)
  obtain ⟨C, hC⟩ := iid_init_field_rd_multitime_proof (d := d) S.hd q S.T ((1 + d) * Kadj)
    (∫ x, ‖x‖ ^ 2 ∂S.μ0) p
  set Ivec : ∀ N, (R N).Ω → PiLp 2 (fun _ : Fin p => HNeg d (q : ℝ)) := fun N ζ =>
    WithLp.toLp 2 fun a => Iq N ((g a).1.1) ζ with hIvec
  set Jvec : ∀ N, (R N).Ω → PiLp 2 (fun _ : Fin p => HNeg d (q : ℝ)) := fun N ζ =>
    WithLp.toLp 2 fun a => Jq N ((g a).1.1) ζ with hJvec
  have hIvm : ∀ N : ℕ, 1 ≤ N → Measurable (Ivec N) := fun N hN =>
    (MeasurableEquiv.toLp 2 (Fin p → HNeg d (q : ℝ))).measurable.comp
      (measurable_pi_iff.2 fun a => (hrepr.1 N hN ((g a).1.1)).1)
  have hJvm : ∀ N : ℕ, 1 ≤ N → Measurable (Jvec N) := fun N hN =>
    (MeasurableEquiv.toLp 2 (Fin p → HNeg d (q : ℝ))).measurable.comp
      (measurable_pi_iff.2 fun a => (hrepr.1 N hN ((g a).1.1)).2)
  have hetaLaw : ∀ n : ℕ, ((R (n + 1)).P.map (Jvec (n + 1))).map (sa27_pairVec (fun a => (g a).2)) =
      P'.map (fun ζ => (WithLp.toLp 2 fun a => S.AN (n + 1) *
        η' ζ (propagatorW (S.coeff (n + 1)) 0 ((g a).1.1) (g a).2.1) : EuclideanSpace ℝ (Fin p))) := by
    intro n
    rw [Measure.map_map (by exact hLc.continuous.measurable) (hJvm (n + 1) (by omega))]
    have h1 : (R (n + 1)).P.map (sa27_pairVec (fun a => (g a).2) ∘ Jvec (n + 1)) =
        (R (n + 1)).P.map (fun ζ => (WithLp.toLp 2 fun a => S.AN (n + 1) *
          (R (n + 1)).η ζ (propagatorW (S.coeff (n + 1)) 0 ((g a).1.1) (g a).2.1) :
            EuclideanSpace ℝ (Fin p))) := by
      refine Measure.map_congr ?_
      have : ∀ᵐ ζ ∂(R (n + 1)).P, ∀ a, HNeg.pairing (g a).2.1 (Jq (n + 1) ((g a).1.1) ζ) =
          S.AN (n + 1) * (R (n + 1)).η ζ (propagatorW (S.coeff (n + 1)) 0 ((g a).1.1) (g a).2.1) :=
        ae_all_iff.2 fun a => by
          filter_upwards [hrepr.2 (n + 1) (by omega) ((g a).1.1) (htsc a) (g a).2.1 (g a).2.2] with ζ h2
          exact h2.2
      filter_upwards [this] with ζ hζ
      ext a
      simp [sa27_pairVec, hJvec, hζ a]
    rw [h1, sa27_bridge_vec_diag S.μ0 (S.AN (n + 1)) (R (n + 1)).P (R (n + 1)).η
      (hid.bridge (n + 1) (by omega)).1 (hid.bridge (n + 1) (by omega)).2 _ (hψN (n + 1) (by omega)),
      sa27_bridge_vec_diag S.μ0 (S.AN (n + 1)) P' η' hη'.1 hη'.2 _ (hψN (n + 1) (by omega))]
  -- the discrepancy
  have hfin : ∀ᶠ n : ℕ in atTop, coeffDiscrepancyRd S L m (n + 1) ≠ ⊤ := by
    have := (hΔ.comp (tendsto_add_atTop_nat 1)).eventually (eventually_lt_nhds ENNReal.zero_lt_top)
    exact this.mono fun n hn => hn.ne
  set Dr : ℕ → ℝ := fun n => (coeffDiscrepancyRd S L m (n + 1)).toReal with hDr
  have hDr0 : Tendsto Dr atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hΔ.comp (tendsto_add_atTop_nat 1))
    simpa [Function.comp_def, hDr] using this
  set cφ : ℝ := sa27_cphi (fun a => (g a).2) with hcφ
  set Bn : ℕ → ℝ := fun n => (max Kst 0 + max Kadj 0) * Dr n * cφ with hBn
  have hBn0 : Tendsto Bn atTop (𝓝 0) := by
    simpa [hBn] using (hDr0.const_mul (max Kst 0 + max Kadj 0)).mul_const cφ
  have hBn_nonneg : ∀ n, 0 ≤ Bn n := fun n =>
    mul_nonneg (mul_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _)) ENNReal.toReal_nonneg)
      (Real.sqrt_nonneg _)
  -- Gaussian closeness
  have hηW : ∀ᶠ n : ℕ in atTop, wassersteinE 1
      (P'.map (fun ζ => (WithLp.toLp 2 fun a => S.AN (n + 1) *
        η' ζ (propagatorW (S.coeff (n + 1)) 0 ((g a).1.1) (g a).2.1) : EuclideanSpace ℝ (Fin p))))
      (P'.map Vinf) ≤ ENNReal.ofReal (Bn n) := by
    filter_upwards [hfin] with n hn
    have hV1m : Measurable (fun ζ => (WithLp.toLp 2 fun a => S.AN (n + 1) *
        η' ζ (propagatorW (S.coeff (n + 1)) 0 ((g a).1.1) (g a).2.1) : EuclideanSpace ℝ (Fin p))) :=
      (MeasurableEquiv.toLp 2 (Fin p → ℝ)).measurable.comp
        (measurable_pi_iff.2 fun a => (hηm _ (hψN (n + 1) (by omega) a)).const_mul _)
    obtain ⟨hA0, hA1⟩ := sa27_AN_bounds S hid.kappa (n + 1) (by omega)
    set b : Fin p → ℝ := fun a => ((max Kst 0 + max Kadj 0) * Dr n) *
      HRS.Whole.sobolevNorm (q : ℝ) (g a).2.1 with hb
    have hbd := fun a => sa27_orbit_bound S L q m m₀ Kadj Kst hAdjL hStab (n + 1) (by omega) hn hA1
      hA0 (htsc a) hj (g a).2.1 (g a).2.2
    refine le_trans (sa27_vec_w2 P' _ Vinf hV1m hVinfm b fun a => ?_) ?_
    · refine le_trans (sa27_bridge_term S.μ0 (S.AN (n + 1)) L.A _ _ (hψN (n + 1) (by omega) a)
        (hψL a) P' η' hηm hη'.2) ?_
      calc ∫⁻ x, ENNReal.ofReal ((S.AN (n + 1) * propagatorW (S.coeff (n + 1)) 0 ((g a).1.1) (g a).2.1 x -
            L.A * propagatorW (L.coeff S) 0 ((g a).1.1) (g a).2.1 x) ^ 2) ∂S.μ0
          ≤ ∫⁻ _x, ENNReal.ofReal (b a ^ 2) ∂S.μ0 := by
            refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
            exact sq_le_sq' (by linarith [(abs_le.1 (hbd a x)).1]) (abs_le.1 (hbd a x)).2
        _ = ENNReal.ofReal (b a ^ 2) := by simp
    · refine ENNReal.ofReal_le_ofReal ?_
      have hs : ∑ a, b a ^ 2 = ((max Kst 0 + max Kadj 0) * Dr n) ^ 2 *
          ∑ a, HRS.Whole.sobolevNorm (q : ℝ) (g a).2.1 ^ 2 := by
        simp only [hb, mul_pow]
        rw [Finset.mul_sum]
      have : Real.sqrt (∑ a, b a ^ 2) = Bn n := by
        rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg
          (add_nonneg (le_max_right _ _) (le_max_right _ _)) ENNReal.toReal_nonneg)]
        simp only [hBn, hcφ, sa27_cphi, hDr]
      rw [this]
  have hηT : Tendsto (fun n : ℕ => wassersteinE 1
      (P'.map (fun ζ => (WithLp.toLp 2 fun a => S.AN (n + 1) *
        η' ζ (propagatorW (S.coeff (n + 1)) 0 ((g a).1.1) (g a).2.1) : EuclideanSpace ℝ (Fin p))))
      (P'.map Vinf)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Eventually.of_forall fun _ => zero_le) hηW
    simpa using ENNReal.tendsto_ofReal hBn0
  have hη1 : Tendsto (fun n : ℕ => wassersteinE 1
      (((R (n + 1)).P.map (Jvec (n + 1))).map (sa27_pairVec (fun a => (g a).2)))
      (P'.map Vinf)) atTop (𝓝 0) := by
    simp_rw [hetaLaw]
    exact hηT
  -- S.B.2, multi-time
  have hmulti : ∀ N : ℕ, 3 ≤ N →
      wassersteinE 1 ((R N).P.map (Ivec N)) ((R N).P.map (Jvec N)) ≤
        ENNReal.ofReal (C * S.AN N * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
          Real.log N ^ (1 / (2 * (d : ℝ) + 5))) := by
    intro N hN3
    have hN : 1 ≤ N := by omega
    have hA : S.AN N = fieldAmp N (S.invβ N) := sa27_fieldAmp_eq S hid.kappa N hN
    have key := hC S.coeff S.invβ S.hinvβ hFI S.μ0 S.hμ0 hid.second_moment le_rfl N hN
      (fun a => (g a).1.1) htsc (R N).P (R N).X₀ (hX0 N hN) (hid.law_init N hN) (Ivec N) (hIvm N hN)
      (fun a φ hφ => by
        filter_upwards [(hrepr.2 N hN ((g a).1.1) (htsc a) φ hφ)] with ζ h1
        show HNeg.pairing φ (Iq N ((g a).1.1) ζ) = _
        rw [h1.1, hid.kappa N hN, hA]; ring)
      (R N).P (R N).η (hid.bridge N hN) (Jvec N) (hJvm N hN)
      (fun a φ hφ => by
        filter_upwards [(hrepr.2 N hN ((g a).1.1) (htsc a) φ hφ)] with ζ h1
        show HNeg.pairing φ (Jq N ((g a).1.1) ζ) = _
        rw [h1.2, hA])
    rw [hA]
    exact (key.1 hN3).1
  -- convergence
  have hrate : Tendsto (fun n : ℕ => (Lc : ℝ≥0∞) * ENNReal.ofReal (max C 0 *
      (((n + 1 : ℕ) : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
        Real.log ((n + 1 : ℕ) : ℝ) ^ (1 / (2 * (d : ℝ) + 5))))) atTop (𝓝 0) := by
    have h0 := (sa27_rate_tendsto (1 / (4 * (d : ℝ) + 10)) (1 / (2 * (d : ℝ) + 5))
      (by positivity)).const_mul (max C 0)
    have := ENNReal.Tendsto.const_mul (a := (Lc : ℝ≥0∞)) (ENNReal.tendsto_ofReal h0)
      (Or.inr ENNReal.coe_ne_top)
    simpa using this
  have hEW : ∀ᶠ n : ℕ in atTop, wassersteinE 1
      (((R (n + 1)).P.map (Ivec (n + 1))).map (sa27_pairVec (fun a => (g a).2)))
      (((R (n + 1)).P.map (Jvec (n + 1))).map (sa27_pairVec (fun a => (g a).2))) ≤
      (Lc : ℝ≥0∞) * ENNReal.ofReal (max C 0 *
        (((n + 1 : ℕ) : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
          Real.log ((n + 1 : ℕ) : ℝ) ^ (1 / (2 * (d : ℝ) + 5)))) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    refine (sa27_w1_map_lip _ Lc hLc0 hLc _ _).trans (mul_le_mul' le_rfl ?_)
    refine (hmulti (n + 1) (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
    obtain ⟨hA0, hA1⟩ := sa27_AN_bounds S hid.kappa (n + 1) (by omega)
    have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
    have hl : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
        Real.log ((n + 1 : ℕ) : ℝ) ^ (1 / (2 * (d : ℝ) + 5)) :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
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
  have hEmpEta : Tendsto (fun n : ℕ => wassersteinE 1
      (((R (n + 1)).P.map (Ivec (n + 1))).map (sa27_pairVec (fun a => (g a).2)))
      (((R (n + 1)).P.map (Jvec (n + 1))).map (sa27_pairVec (fun a => (g a).2))))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrate
      (Eventually.of_forall fun _ => zero_le) hEW
  haveI : ∀ n : ℕ, IsProbabilityMeasure (((R (n + 1)).P.map (Ivec (n + 1))).map
      (sa27_pairVec (fun a => (g a).2))) := fun n => inferInstance
  haveI : ∀ n : ℕ, IsProbabilityMeasure (((R (n + 1)).P.map (Jvec (n + 1))).map
      (sa27_pairVec (fun a => (g a).2))) := fun n => inferInstance
  haveI : IsProbabilityMeasure (P'.map Vinf) := inferInstance
  have hsum := hEmpEta.add hη1
  simp only [add_zero] at hsum
  have hmain : Tendsto (fun n : ℕ => wassersteinE 1
      (((R (n + 1)).P.map (Ivec (n + 1))).map (sa27_pairVec (fun a => (g a).2)))
      (P'.map Vinf)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun n => ?_)
    exact wassersteinE_triangle 1 le_rfl _ _ _
  refine hmain.congr fun n => ?_
  rw [Measure.map_map (by exact hLc.continuous.measurable) (hIvm (n + 1) (by omega))]
  rfl

end HRS.MS.MainRdPath
