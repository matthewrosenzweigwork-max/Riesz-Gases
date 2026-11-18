import HRS.Equilibrium.LocalDivMain
open MeasureTheory Set Metric Filter Topology
noncomputable section
namespace HRS.LocalDivAux
variable {d : ℕ}

theorem rpow_intervalIntegrable {b a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IntervalIntegrable (fun r : ℝ => r ^ (-b)) volume a c := by
  apply ContinuousOn.intervalIntegrable
  intro r hr
  have : 0 < min a c := lt_min ha hc
  exact (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt (lt_of_lt_of_le this hr.1)))).continuousWithinAt

theorem E2_bound {b δ η ε : ℝ} (hb : 0 < b) (hδ : 0 < δ) (hη : 0 < η) (hηδ : η ≤ δ) (hε : 0 < ε)
    (hεη : ε ≤ η) :
    |(∫ r in ε..δ, r ^ (-b)) * ε ^ b| ≤ η + δ * η ^ (-b) * ε ^ b := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (rpow_intervalIntegrable hε hη)
    (rpow_intervalIntegrable hη hδ)]
  have h1 : |∫ r in ε..η, r ^ (-b)| ≤ ε ^ (-b) * η := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := ε) (b := η)
      (f := fun r : ℝ => r ^ (-b)) (C := ε ^ (-b)) (fun x hx => by
        rw [uIoc_of_le hεη] at hx
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hε.trans hx.1).le _)]
        exact rpow_neg_mono hε hx.1.le hb.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ η - ε)] at this
    refine this.trans ?_
    have : 0 ≤ ε ^ (-b) := Real.rpow_nonneg hε.le _
    nlinarith
  have h2 : |∫ r in η..δ, r ^ (-b)| ≤ η ^ (-b) * δ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := η) (b := δ)
      (f := fun r : ℝ => r ^ (-b)) (C := η ^ (-b)) (fun x hx => by
        rw [uIoc_of_le hηδ] at hx
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hη.trans hx.1).le _)]
        exact rpow_neg_mono hη hx.1.le hb.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ δ - η)] at this
    refine this.trans ?_
    have : 0 ≤ η ^ (-b) := Real.rpow_nonneg hη.le _
    nlinarith
  have hεb : 0 < ε ^ b := Real.rpow_pos_of_pos hε _
  rw [abs_mul, abs_of_pos hεb]
  calc |(∫ r in ε..η, r ^ (-b)) + ∫ r in η..δ, r ^ (-b)| * ε ^ b
      ≤ (ε ^ (-b) * η + η ^ (-b) * δ) * ε ^ b :=
        mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans (add_le_add h1 h2)) hεb.le
    _ = η * (ε ^ (-b) * ε ^ b) + δ * η ^ (-b) * ε ^ b := by ring
    _ = η + δ * η ^ (-b) * ε ^ b := by
        rw [← Real.rpow_add hε]; simp

theorem E2_small {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ => (∫ r in ε..δ, r ^ (-b)) * ε ^ b) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro γ hγ
  set η : ℝ := min (γ / 2) δ with hη
  have hηpos : 0 < η := lt_min (by linarith) hδ
  have hηδ : η ≤ δ := min_le_right _ _
  have hηγ : η ≤ γ / 2 := min_le_left _ _
  have hpow : Tendsto (fun ε : ℝ => δ * η ^ (-b) * ε ^ b) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => ε ^ b) (𝓝 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const (0 : ℝ) b (Or.inr hb.le)).tendsto
      rwa [Real.zero_rpow hb.ne'] at this
    have h1 : Tendsto (fun ε : ℝ => ε ^ b) (𝓝[>] 0) (𝓝 0) := h0.mono_left nhdsWithin_le_nhds
    have := h1.const_mul (δ * η ^ (-b))
    simpa using this
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), δ * η ^ (-b) * ε ^ b < γ / 4 :=
    hpow.eventually (gt_mem_nhds (by linarith))
  have hle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 η := Ioo_mem_nhdsGT hηpos
  filter_upwards [hsmall, hle] with ε h1 h2
  rw [Real.dist_eq, sub_zero]
  have := E2_bound hb hδ hηpos hηδ h2.1 h2.2.le
  linarith

section Main
variable {s : ℝ} {ρ φ : Torus d → ℝ}

/-- master estimate: `N(ε) = J R(ε) + O(1 + E₂(ε))`. -/
theorem master (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : SmoothPosDensity ρ)
    (hφ : Torus.IsSmooth φ) :
    ∃ δ C0 K2 : ℝ, 0 < δ ∧ 0 ≤ C0 ∧ 0 ≤ K2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      |(∫ p : Torus d × Torus d, canonicalCenter (withDensityReal ρ) (hC d s φ ε) p.1 p.2 ^ 2
          ∂((withDensityReal ρ).prod (withDensityReal ρ))) -
        Jcoef d s ρ φ * ∫ r in ε..δ, r ^ ((d : ℝ) - 1 - 2 * s)| ≤
        C0 + K2 * ∫ r in ε..δ, r ^ ((d : ℝ) - 2 * s) := by
  obtain ⟨δ, K1, K2, hδ, _, hK1, hK2, hQ⟩ := Q_estimate hd hs0 hsd hρ hφ
  obtain ⟨Cc, hCc0, hCc⟩ := center_estimate hd hs0.le hsd hρ hφ
  refine ⟨δ, K1 + Cc, K2, hδ, by positivity, hK2, fun ε hε hεδ => ?_⟩
  have h1 := hQ ε hε hεδ
  have h2 := hCc ε hε
  set N := ∫ p : Torus d × Torus d, canonicalCenter (withDensityReal ρ) (hC d s φ ε) p.1 p.2 ^ 2
          ∂((withDensityReal ρ).prod (withDensityReal ρ)) with hN
  set Q := ∫ p : Torus d × Torus d, hC d s φ ε p.1 p.2 ^ 2
          ∂((withDensityReal ρ).prod (withDensityReal ρ)) with hQd
  calc |N - Jcoef d s ρ φ * ∫ r in ε..δ, r ^ ((d : ℝ) - 1 - 2 * s)|
      = |(N - Q) + (Q - Jcoef d s ρ φ * ∫ r in ε..δ, r ^ ((d : ℝ) - 1 - 2 * s))| := by ring_nf
    _ ≤ |N - Q| + |Q - Jcoef d s ρ φ * ∫ r in ε..δ, r ^ ((d : ℝ) - 1 - 2 * s)| := abs_add_le _ _
    _ ≤ _ := by linarith


theorem critical_main (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (hρ : SmoothPosDensity ρ)
    (hφ : Torus.IsSmooth φ) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀,
      |(∫ p : Torus d × Torus d, canonicalCenter (withDensityReal ρ) (hC d s φ ε) p.1 p.2 ^ 2
          ∂((withDensityReal ρ).prod (withDensityReal ρ))) -
        Jcoef d s ρ φ * Real.log (1 / ε)| ≤ C := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨δ, C0, K2, hδ, hC0, hK2, hM⟩ := master hd hs0 hsd hρ hφ
  refine ⟨C0 + K2 * δ + |Jcoef d s ρ φ| * |Real.log δ|, δ, hδ, fun ε hε => ?_⟩
  have hε0 : 0 < ε := hε.1
  have hεδ : ε < δ := hε.2
  have h2s : (d : ℝ) - 1 - 2 * s = -1 := by rw [hcrit]; ring
  have h2s' : (d : ℝ) - 2 * s = 0 := by rw [hcrit]; ring
  have e1 : ∫ r in ε..δ, r ^ ((d : ℝ) - 1 - 2 * s) = Real.log δ + Real.log (1 / ε) := by
    rw [intervalIntegral.integral_congr (g := fun r => r⁻¹)]
    · rw [integral_inv_of_pos hε0 hδ, Real.log_div hδ.ne' hε0.ne', one_div, Real.log_inv]; ring
    · intro r hr
      have hr0 : 0 < r := by
        rw [uIcc_of_le hεδ.le] at hr
        exact hε0.trans_le hr.1
      simp only [h2s, Real.rpow_neg_one]
  have e2 : ∫ r in ε..δ, r ^ ((d : ℝ) - 2 * s) = δ - ε := by
    simp [h2s']
  have h := hM ε hε0 hεδ.le
  rw [e1, e2] at h
  set N := ∫ p : Torus d × Torus d, canonicalCenter (withDensityReal ρ) (hC d s φ ε) p.1 p.2 ^ 2
          ∂((withDensityReal ρ).prod (withDensityReal ρ)) with hN
  set J := Jcoef d s ρ φ with hJ
  have hlog : |J * Real.log δ| = |J| * |Real.log δ| := abs_mul _ _
  calc |N - J * Real.log (1 / ε)| = |(N - J * (Real.log δ + Real.log (1 / ε))) + J * Real.log δ| := by
        ring_nf
    _ ≤ |N - J * (Real.log δ + Real.log (1 / ε))| + |J * Real.log δ| := abs_add_le _ _
    _ ≤ C0 + K2 * (δ - ε) + |J| * |Real.log δ| := by rw [← hlog]; linarith
    _ ≤ _ := by nlinarith [mul_nonneg hK2 hε0.le]


theorem ratio_algebra (N J e u : ℝ) (hJ : 0 < J) (he : 0 < e) (hu : 0 < u) :
    N / (J / e * u⁻¹) - 1 = (N - J / e * u⁻¹) * (e / J) * u := by
  field_simp

theorem supercritical_main (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d)
    (hρ : SmoothPosDensity ρ) (hφ : Torus.IsSmooth φ) (hJ : 0 < Jcoef d s ρ φ) :
    Tendsto (fun ε : ℝ => (∫ p : Torus d × Torus d,
          canonicalCenter (withDensityReal ρ) (hC d s φ ε) p.1 p.2 ^ 2
          ∂((withDensityReal ρ).prod (withDensityReal ρ))) /
        (Jcoef d s ρ φ / (2 * s - d) * ε ^ ((d : ℝ) - 2 * s))) (𝓝[>] 0) (𝓝 1) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  obtain ⟨δ, C0, K2, hδ, hC0, hK2, hM⟩ := master hd hs0 hsd hρ hφ
  set e : ℝ := 2 * s - d with he
  have he0 : 0 < e := by rw [he]; linarith
  set J := Jcoef d s ρ φ with hJdef
  set N : ℝ → ℝ := fun ε => ∫ p : Torus d × Torus d,
          canonicalCenter (withDensityReal ρ) (hC d s φ ε) p.1 p.2 ^ 2
          ∂((withDensityReal ρ).prod (withDensityReal ρ)) with hN
  have hexp : (d : ℝ) - 2 * s = -e := by rw [he]; ring
  have hR : ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∫ r in ε..δ, r ^ ((d : ℝ) - 1 - 2 * s) = (ε ^ (-e) - δ ^ (-e)) / e := by
    intro ε hε hεδ
    have hr1 : (d : ℝ) - 1 - 2 * s + 1 = -e := by rw [he]; ring
    rw [integral_rpow (Or.inr ⟨by intro h; linarith, by
      rw [uIcc_of_le hεδ]; exact fun h => absurd h.1 (not_le.2 hε)⟩), hr1]
    have : -e ≠ 0 := by linarith
    field_simp
    ring
  have hg : Tendsto (fun ε : ℝ => (e / J) * (C0 * ε ^ e + K2 * ((∫ r in ε..δ, r ^ (-e)) * ε ^ e)) +
      δ ^ (-e) * ε ^ e) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => ε ^ e) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const (0 : ℝ) e (Or.inr he0.le)).tendsto
      rw [Real.zero_rpow he0.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h1 := E2_small he0 hδ
    have := (((h0.const_mul C0).add (h1.const_mul K2)).const_mul (e / J)).add (h0.const_mul (δ ^ (-e)))
    simpa using this
  have hT : Tendsto (fun ε : ℝ => N ε / (J / e * ε ^ ((d : ℝ) - 2 * s)) - 1) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    have hε0 : 0 < ε := hε.1
    have hu : 0 < ε ^ e := Real.rpow_pos_of_pos hε0 _
    have hinv : ε ^ (-e) = (ε ^ e)⁻¹ := Real.rpow_neg hε0.le e
    have hD := hM ε hε0 hε.2.le
    rw [hR ε hε0 hε.2.le, hexp] at hD
    rw [hexp] at *
    have hE2 : 0 ≤ ∫ r in ε..δ, r ^ (-e) :=
      intervalIntegral.integral_nonneg hε.2.le fun r hr => Real.rpow_nonneg (hε0.le.trans hr.1) _
    rw [hinv, ratio_algebra (N ε) J e _ hJ he0 hu, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos hu, abs_of_pos (div_pos he0 hJ)]
    rw [hinv] at hD
    have hdelta : 0 ≤ δ ^ (-e) := Real.rpow_nonneg hδ.le _
    have hb1 : |N ε - J / e * (ε ^ e)⁻¹| ≤ (C0 + K2 * ∫ r in ε..δ, r ^ (-e)) + J / e * δ ^ (-e) := by
      have e1 : N ε - J / e * (ε ^ e)⁻¹ =
          (N ε - J * (((ε ^ e)⁻¹ - δ ^ (-e)) / e)) - J / e * δ ^ (-e) := by ring
      rw [e1]
      refine (abs_sub _ _).trans (add_le_add hD ?_)
      rw [abs_of_nonneg (by positivity)]
    calc |N ε - J / e * (ε ^ e)⁻¹| * (e / J) * ε ^ e
        ≤ ((C0 + K2 * ∫ r in ε..δ, r ^ (-e)) + J / e * δ ^ (-e)) * (e / J) * ε ^ e :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb1 (div_pos he0 hJ).le) hu.le
      _ = _ := by field_simp
  have := hT.add_const 1
  simpa using this

end Main
end HRS.LocalDivAux
