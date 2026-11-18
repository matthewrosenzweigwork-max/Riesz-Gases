import HRS.MP.KolmChentsov
import HRS.Uniform.Q48dAux3

/-!
# E214F-KC: sup-moment form of the Kolmogorov-Chentsov estimate (prototype of P4, abstract part)

From `HRS.MP.KC` (dyadic Kolmogorov-Chentsov, `mkc_*`) we extract a tail bound for
`sup_{t ∈ [0,T]} ‖X t - X 0‖` (`kc_sup_tail`) and turn tail bounds into moment bounds
(`lintegral_rpow_le_of_tail`, `kc_sup_moment`).  Nothing here is specific to the Riesz setting.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.E214F

section Tail

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E]

/-- Tail bound for the path supremum of an a.s. continuous process with Kolmogorov increment moments.
The constants `c0, K` depend only on `p, β`. -/
theorem kc_sup_tail {p β : ℝ} (hp : 0 < p) (hβ : 0 < β) :
    ∃ c0 K : ℝ, 0 < c0 ∧ 0 < K ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℝ → Ω → E)
      (hX : ∀ t, Measurable (X t))
      {T C : ℝ} (hT : 0 < T)
      (hmom : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
        ∫⁻ ζ, ‖X t ζ - X s ζ‖ₑ ^ p ∂μ ≤ ENNReal.ofReal (C * |t - s| ^ (1 + β)))
      (hcont : ∀ᵐ ζ ∂μ, ContinuousOn (fun t => X t ζ) (Icc 0 T)) (lam : ℝ), 0 < lam →
      μ {ζ | ENNReal.ofReal (c0 * lam) < ⨆ t ∈ Icc (0 : ℝ) T, ‖X t ζ - X 0 ζ‖ₑ} ≤
        ENNReal.ofReal (K * (max C 0 * T ^ (1 + β)) * lam ^ (-p)) := by
  obtain ⟨r, q, hr0, hr1, hq0, hq1, hqr⟩ := HRS.MP.KC.mkc_consts (β := β) (p := p) hβ hp
  refine ⟨HRS.MP.KC.mkc_c r, (1 - q)⁻¹, ?_, ?_, ?_⟩
  · unfold HRS.MP.KC.mkc_c
    have : 0 ≤ 2 * r / (1 - r) := div_nonneg (by linarith) (by linarith)
    linarith
  · exact inv_pos.2 (by linarith)
  intro Ω _ μ X hX T C hT hmom hcont lam hlam
  have hprob := HRS.MP.KC.mkc_prob_bound X T r μ hX hT hp hmom hr0 hq0 hq1 hqr hlam
  have hnull : ∀ᵐ ζ ∂μ, ζ ∈ HRS.MP.KC.mkc_G X T r lam → ∀ t ∈ Icc (0 : ℝ) T,
      HRS.MP.KC.mkc_Zc X T r t ζ = X t ζ := by
    filter_upwards [hcont] with ζ hζ hG t ht
    have h1 := HRS.MP.KC.mkc_Zc_tendsto X T r hT hr0.le hr1 hlam.le hG ht
    have h2 : Tendsto (fun n => HRS.MP.KC.mkc_pt T n (HRS.MP.KC.mkc_idx T n t)) atTop
        (𝓝[Icc 0 T] t) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
        HRS.MP.KC.mkc_pt_mem hT n _ (HRS.MP.KC.mkc_idx_le hT ht.2 n)⟩
      have hlow : Tendsto (fun n : ℕ => t - T / 2 ^ n) atTop (𝓝 t) := by
        have h0 : Tendsto (fun n : ℕ => T / 2 ^ n) atTop (𝓝 0) := by
          have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num)).const_mul T
          rw [mul_zero] at this
          simpa [div_eq_mul_inv, one_div, inv_pow] using this
        simpa using tendsto_const_nhds.sub h0
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
        (fun n => (HRS.MP.KC.mkc_pt_idx hT ht.1 n).1)
      have := (HRS.MP.KC.mkc_pt_idx hT ht.1 n).2
      linarith
    have h3 : Tendsto (fun n => X (HRS.MP.KC.mkc_pt T n (HRS.MP.KC.mkc_idx T n t)) ζ) atTop
        (𝓝 (X t ζ)) := (hζ t ht).tendsto.comp h2
    exact tendsto_nhds_unique h1 h3
  set N : Set Ω := {ζ | ¬ (ζ ∈ HRS.MP.KC.mkc_G X T r lam → ∀ t ∈ Icc (0 : ℝ) T,
      HRS.MP.KC.mkc_Zc X T r t ζ = X t ζ)} with hN
  have hN0 : μ N = 0 := ae_iff.1 hnull
  have hsub : {ζ | ENNReal.ofReal (HRS.MP.KC.mkc_c r * lam) <
      ⨆ t ∈ Icc (0 : ℝ) T, ‖X t ζ - X 0 ζ‖ₑ} ⊆ (HRS.MP.KC.mkc_G X T r lam)ᶜ ∪ N := by
    intro ζ hζ
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨hG, hNn⟩ := hcon
    replace hG : ζ ∈ HRS.MP.KC.mkc_G X T r lam := by simpa using hG
    have hZ : ∀ t ∈ Icc (0 : ℝ) T, HRS.MP.KC.mkc_Zc X T r t ζ = X t ζ := by
      by_contra hh
      exact hNn (fun h => hh (h hG))
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    have hle : (⨆ t ∈ Icc (0 : ℝ) T, ‖X t ζ - X 0 ζ‖ₑ) ≤
        ENNReal.ofReal (HRS.MP.KC.mkc_c r * lam) := by
      refine iSup₂_le fun t ht => ?_
      rw [← hZ t ht, ← hZ 0 h0, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have := HRS.MP.KC.mkc_Zc_dist_le X T r hT hr0.le hr1 hlam.le hG ht h0 0
        (by simpa using abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      simpa using this
    exact absurd hζ (not_lt.2 hle)
  calc μ _ ≤ μ ((HRS.MP.KC.mkc_G X T r lam)ᶜ ∪ N) := measure_mono hsub
    _ ≤ μ (HRS.MP.KC.mkc_G X T r lam)ᶜ + μ N := measure_union_le _ _
    _ = μ (HRS.MP.KC.mkc_G X T r lam)ᶜ := by rw [hN0, add_zero]
    _ ≤ _ := hprob.trans (le_of_eq (by rw [div_eq_inv_mul]; ring_nf))

end Tail

section Moment

theorem tail_term_eq {b θ A p p' : ℝ} (hb : 0 < b) (hθ : 0 < θ) (hA : θ ^ p = A) (j : ℕ) :
    (b * 2 ^ (j + 1)) ^ p' * (A * (θ * 2 ^ j) ^ (-p)) = b ^ p' * 2 ^ p' * (2 ^ p' / 2 ^ p) ^ j := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have e1 : (b * 2 ^ (j + 1)) ^ p' = b ^ p' * 2 ^ p' * (2 ^ p') ^ j := by
    rw [pow_succ, mul_comm ((2 : ℝ) ^ j) 2, ← mul_assoc, Real.mul_rpow (by positivity) h2j.le,
      Real.mul_rpow hb.le h2.le, ← Real.rpow_pow_comm h2.le p' j]
  have e2 : (θ * 2 ^ j) ^ (-p) = θ ^ (-p) * ((2 ^ p) ^ j)⁻¹ := by
    rw [Real.mul_rpow hθ.le h2j.le, Real.rpow_neg h2j.le, Real.rpow_pow_comm h2.le p j]

  have e3 : A * θ ^ (-p) = 1 := by
    rw [← hA, ← Real.rpow_add hθ]; simp
  have hw : (0 : ℝ) < (2 : ℝ) ^ p := Real.rpow_pos_of_pos h2 p
  rw [e1, e2, div_pow]
  calc (b ^ p' * 2 ^ p' * (2 ^ p') ^ j) * (A * (θ ^ (-p) * ((2 ^ p) ^ j)⁻¹))
      = (A * θ ^ (-p)) * (b ^ p' * 2 ^ p' * ((2 ^ p') ^ j * ((2 ^ p) ^ j)⁻¹)) := by ring
    _ = _ := by rw [e3, one_mul, div_eq_mul_inv]

/-- Pointwise dyadic-shell bound. -/
theorem rpow_le_shells {b p' : ℝ} (hb : 0 < b) (hp' : 0 < p') (s : ℝ≥0∞) :
    s ^ p' ≤ ENNReal.ofReal (b ^ p') + ∑' j : ℕ,
      {x : ℝ≥0∞ | ENNReal.ofReal (b * 2 ^ j) < x}.indicator
        (fun _ => ENNReal.ofReal ((b * 2 ^ (j + 1)) ^ p')) s := by
  by_cases h0 : s ≤ ENNReal.ofReal b
  · refine le_trans ?_ le_self_add
    calc s ^ p' ≤ (ENNReal.ofReal b) ^ p' := ENNReal.rpow_le_rpow h0 hp'.le
      _ = _ := ENNReal.ofReal_rpow_of_nonneg hb.le hp'.le
  · push Not at h0
    refine le_trans ?_ le_add_self
    by_cases hsT : s = ⊤
    · subst hsT
      have hterm : ∀ j : ℕ, ENNReal.ofReal ((b * 2) ^ p') ≤
          {x : ℝ≥0∞ | ENNReal.ofReal (b * 2 ^ j) < x}.indicator
            (fun _ => ENNReal.ofReal ((b * 2 ^ (j + 1)) ^ p')) ⊤ := by
        intro j
        rw [Set.indicator_of_mem (by simp [ENNReal.ofReal_lt_top])]
        refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) ?_ hp'.le)
        have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        rw [pow_succ]; nlinarith
      have hpos : ENNReal.ofReal ((b * 2) ^ p') ≠ 0 := by
        simpa using Real.rpow_pos_of_pos (by positivity : 0 < b * 2) p'
      have htop : ∑' j : ℕ, ENNReal.ofReal ((b * 2) ^ p') = ⊤ :=
        ENNReal.tsum_const_eq_top_of_ne_zero hpos
      have hh := ENNReal.tsum_le_tsum hterm
      rw [htop] at hh
      calc (⊤ : ℝ≥0∞) ^ p' = ⊤ := ENNReal.top_rpow_of_pos hp'
        _ ≤ _ := hh
    · have hex : ∃ m : ℕ, s ≤ ENNReal.ofReal (b * 2 ^ m) := by
        obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (s.toReal / b) (by norm_num : (1 : ℝ) < 2)
        refine ⟨m, ?_⟩
        rw [← ENNReal.ofReal_toReal hsT]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_lt_iff₀ hb] at hm
        linarith
      classical
      set m := Nat.find hex with hm
      have hm1 : s ≤ ENNReal.ofReal (b * 2 ^ m) := Nat.find_spec hex
      have hm0 : m ≠ 0 := by
        intro h0'
        rw [h0'] at hm1
        simp at hm1
        exact absurd h0 (not_lt.2 hm1)
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have hjlt : ¬ s ≤ ENNReal.ofReal (b * 2 ^ j) := Nat.find_min hex (by omega)
      push Not at hjlt
      have hsj : s ≤ ENNReal.ofReal (b * 2 ^ (j + 1)) := by
        have : j + 1 = m := hj.symm
        rw [this]; exact hm1
      calc s ^ p' ≤ (ENNReal.ofReal (b * 2 ^ (j + 1))) ^ p' := ENNReal.rpow_le_rpow hsj hp'.le
        _ = {x : ℝ≥0∞ | ENNReal.ofReal (b * 2 ^ j) < x}.indicator
              (fun _ => ENNReal.ofReal ((b * 2 ^ (j + 1)) ^ p')) s := by
            rw [Set.indicator_of_mem (show s ∈ {x : ℝ≥0∞ | ENNReal.ofReal (b * 2 ^ j) < x} from hjlt), ENNReal.ofReal_rpow_of_nonneg (by positivity) hp'.le]
        _ ≤ _ := ENNReal.le_tsum (f := fun j : ℕ => {x : ℝ≥0∞ | ENNReal.ofReal (b * 2 ^ j) < x}.indicator
              (fun _ => ENNReal.ofReal ((b * 2 ^ (j + 1)) ^ p')) s) j

/-- Tail bound `μ{S > cλ} ≤ A λ^{-p}` gives the moment bound `∫ S^{p'} ≲ (c A^{1/p})^{p'}`, `p' < p`. -/
theorem lintegral_rpow_le_of_tail {p p' : ℝ} (hp' : 0 < p') (hpp : p' < p) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (S : Ω → ℝ≥0∞), AEMeasurable S μ →
      ∀ {c A : ℝ}, 0 < c → 0 < A →
      (∀ lam : ℝ, 0 < lam →
        μ {ω | ENNReal.ofReal (c * lam) < S ω} ≤ ENNReal.ofReal (A * lam ^ (-p))) →
      ∫⁻ ω, S ω ^ p' ∂μ ≤ ENNReal.ofReal (Cs * (c * A ^ (1 / p)) ^ p') := by
  have hp : 0 < p := hp'.trans hpp
  have h2 : (0 : ℝ) < 2 := by norm_num
  set rr : ℝ := 2 ^ p' / 2 ^ p with hrr
  have hrr0 : 0 < rr := by positivity
  have hrr1 : rr < 1 := by
    rw [hrr, div_lt_one (Real.rpow_pos_of_pos h2 p)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hpp
  have hsum : Summable fun j : ℕ => rr ^ j := summable_geometric_of_lt_one hrr0.le hrr1
  refine ⟨1 + 2 ^ p' * ∑' j : ℕ, rr ^ j, by positivity, ?_⟩
  intro Ω _ μ _ S hS c A hc hA htail
  set θ : ℝ := A ^ (1 / p) with hθdef
  have hθ : 0 < θ := Real.rpow_pos_of_pos hA _
  have hθp : θ ^ p = A := by
    rw [hθdef, ← Real.rpow_mul hA.le, one_div_mul_cancel hp.ne', Real.rpow_one]
  set b : ℝ := c * θ with hbdef
  have hb : 0 < b := mul_pos hc hθ
  have hmeas : ∀ j : ℕ, NullMeasurableSet {ω | ENNReal.ofReal (b * 2 ^ j) < S ω} μ := fun j =>
    nullMeasurableSet_lt aemeasurable_const hS
  have hpt : ∀ ω, S ω ^ p' ≤ ENNReal.ofReal (b ^ p') + ∑' j : ℕ,
      {ω | ENNReal.ofReal (b * 2 ^ j) < S ω}.indicator
        (fun _ => ENNReal.ofReal ((b * 2 ^ (j + 1)) ^ p')) ω := fun ω =>
    rpow_le_shells hb hp' (S ω)
  calc ∫⁻ ω, S ω ^ p' ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal (b ^ p') + ∑' j : ℕ,
        {ω | ENNReal.ofReal (b * 2 ^ j) < S ω}.indicator
          (fun _ => ENNReal.ofReal ((b * 2 ^ (j + 1)) ^ p')) ω) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (b ^ p') * μ Set.univ + ∑' j : ℕ, ENNReal.ofReal ((b * 2 ^ (j + 1)) ^ p') *
          μ {ω | ENNReal.ofReal (b * 2 ^ j) < S ω} := by
        rw [lintegral_add_left measurable_const, lintegral_const,
          lintegral_tsum (fun j => aemeasurable_const.indicator₀ (hmeas j))]
        congr 1
        exact tsum_congr fun j => lintegral_indicator_const₀ (hmeas j) _
    _ ≤ ENNReal.ofReal (b ^ p') * 1 + ∑' j : ℕ, ENNReal.ofReal (b ^ p' * 2 ^ p' * rr ^ j) := by
        rw [measure_univ]
        gcongr with j
        have h1 := htail (θ * 2 ^ j) (by positivity)
        have e : c * (θ * 2 ^ j) = b * 2 ^ j := by rw [hbdef]; ring
        rw [e] at h1
        calc ENNReal.ofReal ((b * 2 ^ (j + 1)) ^ p') * μ {ω | ENNReal.ofReal (b * 2 ^ j) < S ω}
            ≤ ENNReal.ofReal ((b * 2 ^ (j + 1)) ^ p') * ENNReal.ofReal (A * (θ * 2 ^ j) ^ (-p)) :=
              by gcongr
          _ = ENNReal.ofReal ((b * 2 ^ (j + 1)) ^ p' * (A * (θ * 2 ^ j) ^ (-p))) :=
              (ENNReal.ofReal_mul (by positivity)).symm
          _ = _ := by rw [tail_term_eq hb hθ hθp j]
    _ = ENNReal.ofReal (b ^ p' * (1 + 2 ^ p' * ∑' j : ℕ, rr ^ j)) := by
        rw [mul_one, ← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
          (by simpa [mul_assoc] using (hsum.mul_left (b ^ p' * 2 ^ p'))),
          ← ENNReal.ofReal_add (by positivity) (tsum_nonneg fun j => by positivity)]
        congr 1
        rw [tsum_mul_left]; ring
    _ = _ := by rw [hbdef, hθdef]; ring_nf

end Moment

section SupMoment

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E]

/-- Sup-moment form of Kolmogorov-Chentsov: `E sup_t ‖X t - X 0‖^{p'} ≲ (C T^{1+β})^{p'/p}` for `p' < p`.
The constant `C1` depends only on `p, p', β`. -/
theorem kc_sup_moment {p p' β : ℝ} (hp' : 0 < p') (hpp : p' < p) (hβ : 0 < β) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℝ → Ω → E)
      (hX : ∀ t, Measurable (X t)) {T C : ℝ} (hT : 0 < T) (hC : 0 < C)
      (hmom : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
        ∫⁻ ζ, ‖X t ζ - X s ζ‖ₑ ^ p ∂μ ≤ ENNReal.ofReal (C * |t - s| ^ (1 + β)))
      (hcont : ∀ᵐ ζ ∂μ, ContinuousOn (fun t => X t ζ) (Icc 0 T)),
      ∫⁻ ζ, (⨆ t ∈ Icc (0 : ℝ) T, ‖X t ζ - X 0 ζ‖ₑ) ^ p' ∂μ ≤
        ENNReal.ofReal (C1 * (C * T ^ (1 + β)) ^ (p' / p)) := by
  have hp : 0 < p := hp'.trans hpp
  obtain ⟨c0, K, hc0, hK0, hmain⟩ := kc_sup_tail (E := E) hp hβ
  obtain ⟨Cs, hCs, hmom'⟩ := lintegral_rpow_le_of_tail hp' hpp
  refine ⟨Cs * c0 ^ p' * K ^ (p' / p), by positivity, ?_⟩
  intro Ω _ μ _ X hX T C hT hC hmom hcont
  have hTC : 0 < C * T ^ (1 + β) := mul_pos hC (Real.rpow_pos_of_pos hT _)
  have hA : 0 < K * (C * T ^ (1 + β)) := mul_pos hK0 hTC
  have hS : AEMeasurable (fun ζ => ⨆ t ∈ Icc (0 : ℝ) T, ‖X t ζ - X 0 ζ‖ₑ) μ :=
    HRS.Uniform.Q48d.aemeasurable_supIcc (f := fun t ζ => X t ζ - X 0 ζ) hT.le
      (fun t _ => ((hX t).sub (hX 0)).aestronglyMeasurable)
      (by filter_upwards [hcont] with ζ hζ using hζ.sub continuousOn_const)
  have h := hmom' μ _ hS hc0 hA (fun lam hlam => by
    have := hmain μ X hX hT hmom hcont lam hlam
    rwa [max_eq_left hC.le] at this)
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [Real.mul_rpow hc0.le (Real.rpow_nonneg hA.le _), ← Real.rpow_mul hA.le,
    Real.mul_rpow hK0.le hTC.le]
  rw [show 1 / p * p' = p' / p by ring]
  ring

end SupMoment

end HRS.MC.E214F

end
