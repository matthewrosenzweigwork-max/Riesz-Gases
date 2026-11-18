import HRS.MS.R26T8AV11

/-!
# S8.2 observed-time layer, packet T8A.V12: maximal inequality for the centered compact function along a stationary path

With `M_t = F(X_{u+t}) - F(X_u) - ∫_0^t LF(X_{u+r}) dr` and the reversed process
`Mrev_s = F(X_{u+T-s}) - F(X_{u+T}) - ∫_0^s LF(X_{u+T-r}) dr` one has, for every `t ≤ T` (the generator integrals
cancel exactly): `2 (F(X_{u+t}) - F(X_{u+T})) = M_t + Mrev_{T-t} - M_T`.  Hence
`|Y_t| ≤ |Y_T| + S_M + S_R`, and `E sup |Y|² ≤ 4 (Var F + 2 · 8T/β · E|∇F|²) ≤ 100 (…)` by V10, V11 and stationarity of `Y_T`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

theorem r26t8a_v12_rev_int (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ r, |g r| ≤ C)
    (T s : ℝ) (hs0 : 0 ≤ s) (hsT : s ≤ T) :
    ∫ r in Set.Icc 0 s, g (T - r) =
      (∫ r in Set.Icc 0 T, g r) - ∫ r in Set.Icc 0 (T - s), g r := by
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => by
    refine (Measure.integrableOn_of_bounded (M := C) (by simp) hg.aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => ?_)).intervalIntegrable
    · rw [Real.norm_eq_abs]; exact hC r
  have h1 : ∫ r in Set.Icc 0 s, g (T - r) = ∫ r in (0 : ℝ)..s, g (T - r) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs0]
  have h2 : ∫ r in (0 : ℝ)..s, g (T - r) = ∫ x in (T - s)..(T - 0), g x :=
    intervalIntegral.integral_comp_sub_left g T
  have h3 : (∫ x in (0 : ℝ)..T, g x) - ∫ x in (0 : ℝ)..(T - s), g x = ∫ x in (T - s)..T, g x :=
    intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)
  have h4 : ∀ c : ℝ, 0 ≤ c → ∫ r in Set.Icc 0 c, g r = ∫ x in (0 : ℝ)..c, g x := fun c hc => by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc]
  rw [h1, h2, sub_zero, h4 T (hs0.trans hsT), h4 (T - s) (by linarith), h3]

theorem r26t8a_v12_sq3 (x y z : ℝ≥0∞) : (x + y + z) ^ 2 ≤ 4 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  have h : ∀ p q : ℝ≥0∞, (p + q) ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) := fun p q => by
    have := ENNReal.rpow_add_le_mul_rpow_add_rpow p q (p := 2) (by norm_num)
    simp only [ENNReal.rpow_two] at this
    have h2 : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
    rwa [h2] at this
  calc (x + y + z) ^ 2 ≤ 2 * ((x + y) ^ 2 + z ^ 2) := h _ _
    _ ≤ 2 * (2 * (x ^ 2 + y ^ 2) + z ^ 2) := by gcongr; exact h _ _
    _ ≤ 4 * (x ^ 2 + y ^ 2 + z ^ 2) := by
        have : (2 : ℝ≥0∞) * (2 * (x ^ 2 + y ^ 2) + z ^ 2) = 4 * (x ^ 2 + y ^ 2) + 2 * z ^ 2 := by ring
        rw [this]
        have h4 : (2 : ℝ≥0∞) * z ^ 2 ≤ 4 * z ^ 2 := by gcongr; norm_num
        calc 4 * (x ^ 2 + y ^ 2) + 2 * z ^ 2 ≤ 4 * (x ^ 2 + y ^ 2) + 4 * z ^ 2 := by gcongr
          _ = 4 * (x ^ 2 + y ^ 2 + z ^ 2) := by ring

theorem r26t8a_compact_corrector_maximal (d N : ℕ) (hd : 2≤d) (hN : 2≤N)
    (a beta : ℝ) (ha : 0<a) (hbeta : 0<beta)
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N) (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X)
    (hrev : r26t8a_ReversibleWindows P X)
    (F : EucConfig d N → ℝ) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hFs : tsupport F⊆(eucCollisionSet d N)ᶜ) (u T : ℝ) (hu : 0≤u) (hT : 0<T) :
    let Y := fun t w => centerUnder (canonicalP d N a beta) F (X (u+t).toNNReal w)
    AEMeasurable (fun w => ⨆ t : Set.Icc (0:ℝ) T, ‖Y t w‖ₑ) P ∧
      r26t8a_scalarSupSq P T Y ≤ 100*(evariance F (canonicalP d N a beta)+
        ENNReal.ofReal (T/beta)*∫⁻ x, ∑ i, ‖HRS.MS.Phase2S82.configGrad F x i‖ₑ^2 ∂canonicalP d N a beta) := by
  intro Y
  classical
  obtain ⟨hLFm, CLF, hCLF⟩ := r26t8a_v11a_LF d N (criticalS d) a beta F hF hFc hFs
  have hXm : ∀ t : ℝ≥0, Measurable (X t) := fun t => (hX.solution (t : ℝ)).adapted t
  have hcX : ∀ᵐ w ∂P, Continuous fun t => X t w := by
    filter_upwards [(hX.solution 1).cont] with w hw
    exact continuous_pi hw
  have hV10 := r26t8a_compact_martingale d N hd hN a beta ha hbeta P X0 W X hX F hF hFc hFs u T hu hT
  have hV11 := r26t8a_reversed_compact_maximal d N hd hN a beta ha hbeta P X0 W X hX hrev F hF hFc hFs
    u T hu hT
  obtain ⟨hMm, hMb⟩ := hV10
  obtain ⟨hRm, hRb⟩ := hV11
  set LF := particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F with hLF
  set c : ℝ := ∫ y, F y ∂canonicalP d N a beta with hc
  set M : ℝ → Omega → ℝ := fun t w => F (X (u + t).toNNReal w) - F (X u.toNNReal w) -
    ∫ r in Set.Icc 0 t, LF (X (u + r).toNNReal w) with hM
  set R : ℝ → Omega → ℝ := fun t w => F (X (u + T - t).toNNReal w) - F (X (u + T).toNNReal w) -
    ∫ r in Set.Icc 0 t, LF (X (u + T - r).toNNReal w) with hR
  -- the exact identity
  have hid : ∀ᵐ w ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      2 * (F (X (u + t).toNNReal w) - F (X (u + T).toNNReal w)) = M t w + R (T - t) w - M T w := by
    filter_upwards [hcX] with w hw t ht
    have hcont : Continuous fun r : ℝ => X (u + r).toNNReal w :=
      hw.comp (continuous_real_toNNReal.comp (continuous_const.add continuous_id))
    have hgm : Measurable fun r : ℝ => LF (X (u + r).toNNReal w) := hLFm.comp hcont.measurable
    have hrint := r26t8a_v12_rev_int (fun r => LF (X (u + r).toNNReal w)) hgm CLF
      (fun r => by simpa [Real.norm_eq_abs] using hCLF _ ) T (T - t) (by linarith [ht.2]) (by linarith [ht.1])
    have e1 : ∫ r in Set.Icc (0 : ℝ) (T - t), LF (X (u + T - r).toNNReal w) =
        ∫ r in Set.Icc (0 : ℝ) (T - t), LF (X (u + (T - r)).toNNReal w) := by
      refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
      show LF (X (u + T - r).toNNReal w) = LF (X (u + (T - r)).toNNReal w)
      rw [add_sub_assoc]
    have e2 : u + T - (T - t) = u + t := by ring
    have e3 : T - (T - t) = t := by ring
    simp only [hM, hR]
    rw [e1, hrint, e2, e3]
    ring
  have hsup_le : ∀ᵐ w ∂P, (⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) ≤
      ‖Y T w‖ₑ + ((⨆ t : Set.Icc (0 : ℝ) T, ‖M t w‖ₑ) + ⨆ t : Set.Icc (0 : ℝ) T, ‖R t w‖ₑ) := by
    filter_upwards [hid] with w hw
    refine iSup_le fun t => ?_
    have ht := t.2
    have hT' : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
    have hTt : T - (t : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hMt : ‖M t w‖ₑ ≤ ⨆ t : Set.Icc (0 : ℝ) T, ‖M t w‖ₑ :=
      le_iSup (fun t : Set.Icc (0 : ℝ) T => ‖M t w‖ₑ) t
    have hMT : ‖M T w‖ₑ ≤ ⨆ t : Set.Icc (0 : ℝ) T, ‖M t w‖ₑ :=
      le_iSup (fun t : Set.Icc (0 : ℝ) T => ‖M t w‖ₑ) ⟨T, hT'⟩
    have hRt : ‖R (T - t) w‖ₑ ≤ ⨆ t : Set.Icc (0 : ℝ) T, ‖R t w‖ₑ :=
      le_iSup (fun t : Set.Icc (0 : ℝ) T => ‖R t w‖ₑ) ⟨T - t, hTt⟩
    have hdiff : Y t w = Y T w + (F (X (u + t).toNNReal w) - F (X (u + T).toNNReal w)) := by
      simp only [Y, centerUnder]; ring
    have hkey : ‖F (X (u + t).toNNReal w) - F (X (u + T).toNNReal w)‖ₑ ≤
        (⨆ t : Set.Icc (0 : ℝ) T, ‖M t w‖ₑ) + ⨆ t : Set.Icc (0 : ℝ) T, ‖R t w‖ₑ := by
      set S1 := ⨆ t : Set.Icc (0 : ℝ) T, ‖M t w‖ₑ
      set S2 := ⨆ t : Set.Icc (0 : ℝ) T, ‖R t w‖ₑ
      have h2 : (2 : ℝ≥0∞) * ‖F (X (u + t).toNNReal w) - F (X (u + T).toNNReal w)‖ₑ ≤
          2 * (S1 + S2) := by
        have e : (2 : ℝ≥0∞) * ‖F (X (u + t).toNNReal w) - F (X (u + T).toNNReal w)‖ₑ =
            ‖M t w + R (T - t) w - M T w‖ₑ := by
          rw [← hw t ht, enorm_mul]
          congr 1
          rw [Real.enorm_eq_ofReal (by norm_num), ENNReal.ofReal_ofNat]
        rw [e]
        calc ‖M t w + R (T - t) w - M T w‖ₑ ≤ ‖M t w + R (T - t) w‖ₑ + ‖M T w‖ₑ := enorm_sub_le
          _ ≤ (‖M t w‖ₑ + ‖R (T - t) w‖ₑ) + ‖M T w‖ₑ := by gcongr; exact enorm_add_le _ _
          _ ≤ (S1 + S2) + S1 := by gcongr
          _ ≤ 2 * (S1 + S2) := by
              have : (2 : ℝ≥0∞) * (S1 + S2) = (S1 + S2) + (S1 + S2) := two_mul _
              rw [this]; gcongr; exact le_self_add
      exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by simp)).1 h2
    calc ‖Y t w‖ₑ = ‖Y T w + (F (X (u + t).toNNReal w) - F (X (u + T).toNNReal w))‖ₑ := by rw [← hdiff]
      _ ≤ ‖Y T w‖ₑ + ‖F (X (u + t).toNNReal w) - F (X (u + T).toNNReal w)‖ₑ := enorm_add_le _ _
      _ ≤ _ := by gcongr
  -- measurability of the supremum of `Y`
  obtain ⟨D, hDc, hDs, hDd⟩ := TopologicalSpace.exists_countable_dense_subset (Set.Icc (0 : ℝ) T)
  have hYm : ∀ t, Measurable (Y t) := fun t =>
    (hF.continuous.measurable.comp (hXm _)).sub measurable_const
  have hYsup : ∀ᵐ w ∂P, (⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) = ⨆ q ∈ D, ‖Y q w‖ₑ := by
    filter_upwards [hcX] with w hw
    have hcont : Continuous fun t : ℝ => Y t w :=
      (hF.continuous.comp (hw.comp (continuous_real_toNNReal.comp
        (continuous_const.add continuous_id)))).sub continuous_const
    rw [← iSup_Icc_enorm_eq_of_dense hcont hDs hDd]
    exact (iSup_subtype' (p := fun t => t ∈ Set.Icc (0 : ℝ) T) (f := fun t _ => ‖Y t w‖ₑ)).symm
  have hAm : AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) P :=
    (Measurable.biSup D hDc fun q _ => (hYm q).enorm).aemeasurable.congr (hYsup.mono fun w h => h.symm)
  refine ⟨hAm, ?_⟩
  -- the energy bound
  have hlaw : P.map (X (u + T).toNNReal) = canonicalP d N a beta := by
    have := hX.invariant P (u + T) X0 W X hX.brownian hX.indep hX.init (hX.solution (u + T))
      (u + T).toNNReal (by rw [Real.coe_toNNReal _ (by linarith)])
    exact this
  have hvar : ∫⁻ w, ‖Y T w‖ₑ ^ 2 ∂P = evariance F (canonicalP d N a beta) := by
    have hFm : Measurable fun y : EucConfig d N => ‖F y - c‖ₑ ^ 2 :=
      ((hF.continuous.measurable.sub measurable_const).enorm).pow_const 2
    calc ∫⁻ w, ‖Y T w‖ₑ ^ 2 ∂P = ∫⁻ w, ‖F (X (u + T).toNNReal w) - c‖ₑ ^ 2 ∂P := rfl
      _ = ∫⁻ y, ‖F y - c‖ₑ ^ 2 ∂(P.map (X (u + T).toNNReal)) :=
          (lintegral_map hFm (hXm _)).symm
      _ = ∫⁻ y, ‖F y - c‖ₑ ^ 2 ∂(canonicalP d N a beta) := by rw [hlaw]
      _ = evariance F (canonicalP d N a beta) := rfl
  unfold r26t8a_scalarSupSq at hMb hRb ⊢
  set E := ∫⁻ x, ∑ i, ‖HRS.MS.Phase2S82.configGrad F x i‖ₑ ^ 2 ∂canonicalP d N a beta with hE
  set V := evariance F (canonicalP d N a beta) with hV
  have hAmeas : Measurable fun w => ‖Y T w‖ₑ ^ 2 := ((hYm _).enorm).pow_const 2
  have h8 : ENNReal.ofReal (8 * T / beta) = 8 * ENNReal.ofReal (T / beta) := by
    rw [show 8 * T / beta = 8 * (T / beta) by ring, ENNReal.ofReal_mul (by norm_num)]
    simp
  calc ∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) ^ 2 ∂P
      ≤ ∫⁻ w, 4 * (‖Y T w‖ₑ ^ 2 + (⨆ t : Set.Icc (0 : ℝ) T, ‖M t w‖ₑ) ^ 2 +
          (⨆ t : Set.Icc (0 : ℝ) T, ‖R t w‖ₑ) ^ 2) ∂P := by
        refine lintegral_mono_ae (hsup_le.mono fun w h => ?_)
        calc (⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) ^ 2 ≤ (‖Y T w‖ₑ + ((⨆ t : Set.Icc (0 : ℝ) T, ‖M t w‖ₑ) +
            ⨆ t : Set.Icc (0 : ℝ) T, ‖R t w‖ₑ)) ^ 2 := by gcongr
          _ = (‖Y T w‖ₑ + (⨆ t : Set.Icc (0 : ℝ) T, ‖M t w‖ₑ) +
            ⨆ t : Set.Icc (0 : ℝ) T, ‖R t w‖ₑ) ^ 2 := by rw [add_assoc]
          _ ≤ _ := r26t8a_v12_sq3 _ _ _
    _ = 4 * (∫⁻ w, ‖Y T w‖ₑ ^ 2 ∂P + ∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ‖M t w‖ₑ) ^ 2 ∂P +
          ∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ‖R t w‖ₑ) ^ 2 ∂P) := by
        rw [lintegral_const_mul' _ _ (by norm_num)]
        congr 1
        have hAM : AEMeasurable (fun w => ‖Y T w‖ₑ ^ 2 +
            (⨆ t : Set.Icc (0 : ℝ) T, ‖M t w‖ₑ) ^ 2) P := hAmeas.aemeasurable.add (hMm.pow_const 2)
        rw [lintegral_add_left' hAM, lintegral_add_left' hAmeas.aemeasurable]
    _ ≤ 100 * (V + ENNReal.ofReal (T / beta) * E) := by
        rw [hvar]
        have hMb' : ∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ‖M t w‖ₑ) ^ 2 ∂P ≤
            ENNReal.ofReal (8 * T / beta) * E := hMb
        have hRb' : ∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ‖R t w‖ₑ) ^ 2 ∂P ≤
            ENNReal.ofReal (8 * T / beta) * E := hRb
        calc 4 * (V + ∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ‖M t w‖ₑ) ^ 2 ∂P +
              ∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ‖R t w‖ₑ) ^ 2 ∂P)
            ≤ 4 * (V + ENNReal.ofReal (8 * T / beta) * E + ENNReal.ofReal (8 * T / beta) * E) := by
              gcongr
          _ = 4 * V + 64 * (ENNReal.ofReal (T / beta) * E) := by rw [h8]; ring
          _ ≤ 100 * V + 100 * (ENNReal.ofReal (T / beta) * E) := by
              gcongr <;> norm_num
          _ = 100 * (V + ENNReal.ofReal (T / beta) * E) := by ring

end HRS.MS.R26T8A

end
