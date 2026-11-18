import HRS.MS.WadAux181

/-!
# S8.3, packet S8H2-8: regularity of the pair inverse

`s8h2_bounds`: for `F` with `S8hPair M j F`, doubly centered: the kernels `S_tF = tensorU U t F` (`t > 0`) are `C^j` with jets
`‖D^kS_tF‖ ≤ b(t) w`, where `b` is integrable on `ℝ` (constant on `(0,1]` by `s8h2_P1`, `C e^{-ct}` for `t > 1` by clause (4b)).
`s8h2_psi_reg`: for measurable `S ⊆ (0,∞)`, `Ψ_S = ∫_S S_tF dt` is `C^j` with `‖D^kΨ_S‖ ≤ (∫_S b) w` (`s8h2_parint`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff Convolution

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8h2_pn0_le {M N : ℝ} {F : Euc d × Euc d → ℝ} (h : ∀ z, ‖F z‖ ≤ N * s8h_w M z) :
    pairNormE M 0 (fun x y => F (x, y)) ≤ ENNReal.ofReal N := by
  refine iSup_le fun i => iSup_le fun z => ENNReal.ofReal_le_ofReal ?_
  have hi : (i : ℕ) = 0 := by have := i.2; omega
  rw [hi, norm_iteratedFDeriv_zero]
  have e2 : Function.uncurry (fun x y => F (x, y)) z = F z := rfl
  rw [e2]
  have h1 := h z
  unfold s8h_w at h1
  have hx := Real.rpow_pos_of_pos (s83_jb_pos z.1) M
  have hy := Real.rpow_pos_of_pos (s83_jb_pos z.2) M
  rw [Real.rpow_neg (s83_jb_pos z.1).le, Real.rpow_neg (s83_jb_pos z.2).le]
  calc (jbracket z.1 ^ M)⁻¹ * (jbracket z.2 ^ M)⁻¹ * ‖F z‖
      ≤ (jbracket z.1 ^ M)⁻¹ * (jbracket z.2 ^ M)⁻¹ * (N * (jbracket z.1 ^ M * jbracket z.2 ^ M)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = N := by field_simp

theorem s8h2_param_set {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (j : ℕ)
    {w : V → ℝ} (hw : Continuous w) (hw0 : ∀ z, 0 ≤ w z) {S : Set ℝ} (hS : MeasurableSet S)
    {F : ℝ → V → ℝ} (hcd : ∀ t ∈ S, ContDiff ℝ j (F t)) (hcont : ∀ z, ContinuousOn (fun t => F t z) S)
    {b : ℝ → ℝ} (hbi : IntegrableOn b S) (hb0 : ∀ t ∈ S, 0 ≤ b t)
    (hbd : ∀ t ∈ S, ∀ k ≤ j, ∀ z, ‖iteratedFDeriv ℝ k (F t) z‖ ≤ b t * w z) :
    ContDiff ℝ j (fun z => ∫ t in S, F t z) ∧
    (∀ k ≤ j, ∀ z, iteratedFDeriv ℝ k (fun z => ∫ t in S, F t z) z = ∫ t in S, iteratedFDeriv ℝ k (F t) z) ∧
    ∀ k ≤ j, ∀ z, ‖iteratedFDeriv ℝ k (fun z => ∫ t in S, F t z) z‖ ≤ (∫ t in S, b t) * w z := by
  classical
  set Ft : ℝ → V → ℝ := fun t z => S.piecewise (fun t => F t z) (fun _ => (0 : ℝ)) t with hFt
  have hFt_in : ∀ t ∈ S, Ft t = F t := fun t ht => by
    funext z
    simp only [hFt]
    exact Set.piecewise_eq_of_mem _ _ _ ht
  have hFt_out : ∀ t, t ∉ S → Ft t = fun _ => 0 := fun t ht => by
    funext z
    simp only [hFt]
    exact Set.piecewise_eq_of_notMem _ _ _ ht
  have hcd' : ∀ t, ContDiff ℝ j (Ft t) := fun t => by
    by_cases ht : t ∈ S
    · rw [hFt_in t ht]; exact hcd t ht
    · rw [hFt_out t ht]; exact contDiff_const
  have hmeas : ∀ z, Measurable (fun t => Ft t z) := fun z =>
    ContinuousOn.measurable_piecewise (s := S) (hcont z) continuousOn_const hS
  have hm : ∀ k ≤ j, ∀ z (m : Fin k → V), Measurable (fun t => iteratedFDeriv ℝ k (Ft t) z m) :=
    fun k hk z m => s8h2_meas_iter k Ft (fun t => (hcd' t).of_le (by exact_mod_cast hk)) hmeas z m
  have hbb : ∀ k ≤ j, ∃ b' : ℝ → ℝ, Integrable b' (volume.restrict S) ∧ (∀ t, 0 ≤ b' t) ∧
      ∀ t z, ‖iteratedFDeriv ℝ k (Ft t) z‖ ≤ b' t * w z := by
    intro k hk
    refine ⟨S.indicator b, ((integrable_indicator_iff hS).2 hbi).restrict, fun t => ?_, fun t z => ?_⟩
    · exact Set.indicator_nonneg (fun s hs => hb0 s hs) t
    · by_cases ht : t ∈ S
      · rw [hFt_in t ht, Set.indicator_of_mem ht]; exact hbd t ht k hk z
      · rw [hFt_out t ht, Set.indicator_of_notMem ht]
        simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, zero_mul, le_refl]
  obtain ⟨hC, hform⟩ := s8h2_parint j (W := ℝ) Ft (volume.restrict S) hw hw0 hcd' hm hbb
  have hΨ : (fun z => ∫ t, Ft t z ∂(volume.restrict S)) = fun z => ∫ t in S, F t z := by
    funext z
    refine setIntegral_congr_fun hS (fun t ht => ?_)
    rw [hFt_in t ht]
  rw [hΨ] at hC hform
  have hform' : ∀ k ≤ j, ∀ z, iteratedFDeriv ℝ k (fun z => ∫ t in S, F t z) z =
      ∫ t in S, iteratedFDeriv ℝ k (F t) z := by
    intro k hk z
    rw [hform k hk z]
    refine setIntegral_congr_fun hS (fun t ht => ?_)
    rw [hFt_in t ht]
  refine ⟨hC, hform', fun k hk z => ?_⟩
  rw [hform' k hk z]
  have hint : IntegrableOn (fun t => b t * w z) S := hbi.mul_const _
  refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' hS).2 (Eventually.of_forall fun t ht => ?_))).trans
    (le_of_eq ?_)
  · exact hbd t ht k hk z
  · rw [integral_mul_const]

section Interface

variable {a β : ℝ} {ρβ : Euc d → ℝ} {M : ℝ} {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}

theorem s8h2_bounds (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (h3 : S8eC3 M U) (h4b : S8eC4b a β ρβ M U) (hM : 0 ≤ M) (j : ℕ) {F : Euc d × Euc d → ℝ}
    (hF : S8hPair M j F) (hdc : IsDoublyCentered (HRS.Whole.withDensityReal ρβ) (fun x y => F (x, y))) :
    ∃ b : ℝ → ℝ, Integrable b ∧ (∀ t, 0 ≤ b t) ∧
      (∃ C c : ℝ, 0 < c ∧ ∀ t, 1 < t → b t ≤ C * Real.exp (-c * t)) ∧
      ∀ t, 0 < t → ContDiff ℝ j (s8h2_S U t F) ∧
        ∀ k ≤ j, ∀ z, ‖iteratedFDeriv ℝ k (s8h2_S U t F) z‖ ≤ b t * s8h_w M z := by
  obtain ⟨C1, hC10, hP1⟩ := s8h2_P1 hU h3 hM j zero_le_one
  obtain ⟨N0, hN00, G, -, -, hG⟩ := hP1 hF
  obtain ⟨Cj, c, hc, h4⟩ := h4b j
  obtain ⟨N00, hN00', hN00b⟩ := s8h_bound_of_pair (s8h2_pair_mono (Nat.zero_le j) hF)
  have hN00b' : ∀ z, ‖F z‖ ≤ N00 * s8h_w M z := fun z => by
    have := hN00b 0 le_rfl z
    rwa [norm_iteratedFDeriv_zero] at this
  set Cj' : ℝ := max Cj 0 with hCj'
  have hCj'0 : 0 ≤ Cj' := le_max_right _ _
  refine ⟨fun t => (Set.Ioc (0 : ℝ) 1).indicator (fun _ => C1 * N0) t +
    (Set.Ioi (1 : ℝ)).indicator (fun t => Cj' * N00 * Real.exp (-c * t)) t, ?_, ?_,
    ⟨Cj' * N00, c, hc, fun t ht => ?_⟩, ?_⟩
  · refine Integrable.add ?_ ?_
    · exact (integrable_indicator_iff measurableSet_Ioc).2 (continuous_const.integrableOn_Ioc)
    · refine (integrable_indicator_iff measurableSet_Ioi).2 ?_
      have := (integrableOn_exp_mul_Ioi (a := -c) (by linarith) (1 : ℝ)).const_mul (Cj' * N00)
      exact this
  · intro t
    exact add_nonneg (Set.indicator_nonneg (fun _ _ => mul_nonneg hC10 hN00) t)
      (Set.indicator_nonneg (fun s _ => by positivity) t)
  · have h0 : t ∉ Set.Ioc (0 : ℝ) 1 := fun h => by linarith [h.2]
    simp [Set.indicator_of_notMem h0, Set.indicator_of_mem (show t ∈ Set.Ioi (1 : ℝ) from ht)]
  · intro t ht
    refine ⟨?_, ?_⟩
    · obtain ⟨C', -, hP'⟩ := s8h2_P1 hU h3 hM j ht.le
      obtain ⟨N', -, G', -, -, hG'⟩ := hP' hF
      exact (hG' t ⟨ht.le, le_rfl⟩).1
    · intro k hk z
      by_cases ht1 : t ≤ 1
      · have hmem : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
        have h0 : t ∉ Set.Ioi (1 : ℝ) := fun h => by linarith [h.out]
        simp only [Set.indicator_of_mem hmem, Set.indicator_of_notMem h0, add_zero]
        exact (hG t ⟨ht.le, ht1⟩).2.1 k hk z
      · push Not at ht1
        have h0 : t ∉ Set.Ioc (0 : ℝ) 1 := fun h => by linarith [h.2]
        simp only [Set.indicator_of_notMem h0, Set.indicator_of_mem (show t ∈ Set.Ioi (1 : ℝ) from ht1), zero_add]
        obtain ⟨-, hpn⟩ := h4 t ht1.le (fun x y => F (x, y)) (s8h_pair_iff.2 (s8h2_pair_mono (Nat.zero_le j) hF)) hdc
        have hle : pairNormE M j (tensorU U t (fun x y => F (x, y))) ≤
            ENNReal.ofReal (Cj' * Real.exp (-c * t) * N00) := by
          calc _ ≤ ENNReal.ofReal (Cj * Real.exp (-c * t)) * pairNormE M 0 (fun x y => F (x, y)) := hpn
            _ ≤ ENNReal.ofReal (Cj' * Real.exp (-c * t)) * ENNReal.ofReal N00 :=
                mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
                  (Real.exp_pos _).le)) (s8h2_pn0_le hN00b')
            _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
        have hz : ENNReal.ofReal (jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) *
            ‖iteratedFDeriv ℝ k (s8h2_S U t F) z‖) ≤ pairNormE M j (tensorU U t (fun x y => F (x, y))) :=
          le_iSup₂_of_le (⟨k, by omega⟩ : Fin (j + 1)) z le_rfl
        have h5 := hz.trans hle
        have hx := Real.rpow_pos_of_pos (s83_jb_pos z.1) M
        have hy := Real.rpow_pos_of_pos (s83_jb_pos z.2) M
        rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h5
        rw [Real.rpow_neg (s83_jb_pos z.1).le, Real.rpow_neg (s83_jb_pos z.2).le] at h5
        unfold s8h_w
        have e : ‖iteratedFDeriv ℝ k (s8h2_S U t F) z‖ =
            (jbracket z.1 ^ M * jbracket z.2 ^ M) * ((jbracket z.1 ^ M)⁻¹ * (jbracket z.2 ^ M)⁻¹ *
              ‖iteratedFDeriv ℝ k (s8h2_S U t F) z‖) := by field_simp
        rw [e]
        calc _ ≤ (jbracket z.1 ^ M * jbracket z.2 ^ M) * (Cj' * Real.exp (-c * t) * N00) :=
              mul_le_mul_of_nonneg_left h5 (by positivity)
          _ = _ := by ring

theorem s8h2_psi_reg (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ)
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (h3 : S8eC3 M U) (h4b : S8eC4b a β ρβ M U) (hM : 0 ≤ M) (j : ℕ) {F : Euc d × Euc d → ℝ}
    (hF : S8hPair M j F) (hdc : IsDoublyCentered (HRS.Whole.withDensityReal ρβ) (fun x y => F (x, y))) :
    ∃ b : ℝ → ℝ, Integrable b ∧ (∀ t, 0 ≤ b t) ∧
      (∃ C c : ℝ, 0 < c ∧ ∀ t, 1 < t → b t ≤ C * Real.exp (-c * t)) ∧
      (∀ t, 0 < t → ContDiff ℝ j (s8h2_S U t F) ∧
        ∀ k ≤ j, ∀ z, ‖iteratedFDeriv ℝ k (s8h2_S U t F) z‖ ≤ b t * s8h_w M z) ∧
      ∀ S : Set ℝ, MeasurableSet S → S ⊆ Set.Ioi 0 →
        ContDiff ℝ j (fun z => ∫ t in S, s8h2_S U t F z) ∧
        (∀ k ≤ j, ∀ z, iteratedFDeriv ℝ k (fun z => ∫ t in S, s8h2_S U t F z) z =
          ∫ t in S, iteratedFDeriv ℝ k (s8h2_S U t F) z) ∧
        ∀ k ≤ j, ∀ z, ‖iteratedFDeriv ℝ k (fun z => ∫ t in S, s8h2_S U t F z) z‖ ≤
          (∫ t in S, b t) * s8h_w M z := by
  obtain ⟨b, hbi, hb0, hbe, hbd⟩ := s8h2_bounds hU h3 h4b hM j hF hdc
  refine ⟨b, hbi, hb0, hbe, hbd, fun S hS hSpos => ?_⟩
  exact s8h2_param_set j (s8h_w_cont M) (fun z => (s8h_w_pos M z).le) hS
    (fun t ht => (hbd t (hSpos ht)).1)
    (fun z => (s8h2_S_cont hd ha hβ hρ hU h3 hM hF z).mono (fun t ht => Set.mem_Ici.2 (Set.mem_Ioi.1 (hSpos ht)).le))
    hbi.integrableOn (fun t _ => hb0 t) (fun t ht => (hbd t (hSpos ht)).2)

end Interface

end HRS.MS.Wad
