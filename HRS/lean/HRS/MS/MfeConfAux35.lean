import HRS.MS.MfeConfAux34

/-!
# S.B.1, packet F3 (part 16): the logarithm of an absolutely continuous positive function, and the identity of the normaliser
at the smoothed level

* `sb1_log_of_integral_eq`: if `K > 0` on `[0,T]` and `K t = K 0 + ∫_0^t Φ` with `Φ` integrable, then
  `log K t - log K 0 = ∫_0^t Φ/K` (Lebesgue differentiation + the chain rule for absolutely continuous functions);
* `sb1Kpi`, `sb1Phipi`: the normaliser and `Φ = ∫ F P dμ^N` of a smoothed kernel;
* `sb1_Mlevel`: `K_n(t) - K_n(0) = ∫_0^t βN Φ_n` for a regular kernel (`sb1_hasDerivAt_K`, `sb1_dK_eq`, FTC).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_log_lip (m : ℝ) (hm : 0 < m) : LipschitzOnWith (Real.toNNReal (1 / m)) Real.log (Set.Ici m) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hx' : m ≤ x := hx
  have hy' : m ≤ y := hy
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := Real.log) (s := Set.Ici m) (C := 1 / m)
    (fun z hz => Real.differentiableAt_log (by have : m ≤ z := hz; linarith))
    (fun z hz => by
      have hz' : m ≤ z := hz
      rw [Real.deriv_log, norm_inv, Real.norm_eq_abs, abs_of_pos (by linarith)]
      rw [one_div]
      exact inv_anti₀ hm hz')
    (convex_Ici m) hy hx
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact key

theorem sb1_log_of_integral_eq {K Φ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hpos : ∀ t ∈ Set.Icc 0 T, 0 < K t)
    (hΦ : IntervalIntegrable Φ volume 0 T) (hid : ∀ t ∈ Set.Icc 0 T, K t = K 0 + ∫ r in (0 : ℝ)..t, Φ r) :
    ∃ m : ℝ, 0 < m ∧ (∀ t ∈ Set.Icc 0 T, m ≤ K t) ∧
      ∀ t ∈ Set.Icc 0 T, Real.log (K t) - Real.log (K 0) = ∫ r in (0 : ℝ)..t, Φ r / K r := by
  have huI : Set.uIcc (0 : ℝ) T = Set.Icc 0 T := Set.uIcc_of_le hT
  have hAC0 : AbsolutelyContinuousOnInterval (fun x => ∫ r in (0 : ℝ)..x, Φ r) 0 T :=
    hΦ.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp [hT])
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => K 0) 0 T :=
    (LipschitzWith.const (K 0)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hACK : AbsolutelyContinuousOnInterval K 0 T := by
    refine (hconst.add hAC0).congr fun x hx => ?_
    rw [huI] at hx
    simp only [Pi.add_apply]
    exact (hid x hx).symm
  have hcont : ContinuousOn K (Set.Icc 0 T) := by
    have := hACK.continuousOn
    rwa [huI] at this
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hT) hcont
  set m := K x₀ with hmdef
  have hm : 0 < m := hpos x₀ hx₀
  have hmK : ∀ t ∈ Set.Icc (0 : ℝ) T, m ≤ K t := fun t ht => (isMinOn_iff.1 hmin) t ht
  refine ⟨m, hm, hmK, fun t ht => ?_⟩
  have hlogAC : AbsolutelyContinuousOnInterval (Real.log ∘ K) 0 T :=
    (sb1_log_lip m hm).comp_absolutelyContinuousOnInterval (fun x hx => hmK x (by rwa [huI] at hx)) hACK
  have htT : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc 0 T := by
    rw [huI, Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
  have hF := (hlogAC.mono htT).integral_deriv_eq_sub
  simp only [Function.comp] at hF
  rw [← hF]
  refine intervalIntegral.integral_congr_ae ?_
  have hae := hΦ.ae_hasDerivAt_integral
  have hneT : ∀ᵐ x : ℝ, x ≠ T := by simp [ae_iff, measure_singleton]
  filter_upwards [hae, hneT] with x hx hxT hxI
  rw [Set.uIoc_of_le ht.1] at hxI
  have hx0 : 0 < x := hxI.1
  have hxlt : x < T := lt_of_le_of_ne (hxI.2.trans ht.2) hxT
  have hxm : x ∈ Set.uIcc (0 : ℝ) T := by rw [huI]; exact ⟨hx0.le, hxlt.le⟩
  have h0m : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) T := by rw [huI]; exact ⟨le_rfl, hT⟩
  have hD := hx hxm 0 h0m
  have hKd : HasDerivAt K (Φ x) x := by
    have hev : (fun u => K 0 + ∫ r in (0 : ℝ)..u, Φ r) =ᶠ[𝓝 x] K := by
      filter_upwards [Ioo_mem_nhds hx0 hxlt] with u hu
      exact (hid u ⟨hu.1.le, hu.2.le⟩).symm
    exact (hD.const_add (K 0)).congr_of_eventuallyEq hev.symm
  have hKx : K x ≠ 0 := (hpos x ⟨hx0.le, hxlt.le⟩).ne'
  exact (hKd.log hKx).deriv

end HRS.MS.MfeConf
