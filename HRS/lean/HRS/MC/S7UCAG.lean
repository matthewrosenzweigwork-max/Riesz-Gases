import HRS.MC.S7FCG
import HRS.MC.S7UCDefs

/-!
# S7UCAG: FC-G uniform in `t ≥ 0` (UC-G)

`s7_UC_G_strong_tail_unif_proof`: the proof of `s7_FC_G_strong_tail_proof` (`S7FCG.lean`) with the supremum over
`t ≥ 0` inside.  All constants are uniform in `t ≥ 0`; the size `A_t L` is bounded by `A' L` built from the time-`0`
product measure through `μ^t ≤ (M₀/m₀) μ⁰`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCA

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCH4
open HRS.MC.Sec7.FCG

variable {d : ℕ}

theorem s7_UC_G_strong_tail_unif_proof (R : Regime d) (k : NonzeroLattice d)
    (hL : ℕ → Torus d → Torus d → ℝ) (hLd : ∀ L, s7_IsFiniteRankSmooth (hL L))
    (B c : ℝ) (hc : EnvelopeConst (d := d) R.D.s c)
    (hLB : ∀ L x y, x ≠ y → |hL L x y| ≤ B * (periodicRiesz d R.D.s (x - y) + c))
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    (ε : ℝ) (hε : 0 < ε) (hεs : (2 + ε) * R.D.s < d)
    (hconv : Tendsto (fun L : ℕ => eLpNorm (fun p : Torus d × Torus d =>
        hL L p.1 p.2 - hTransport d R.D.s (Torus.realMode k) p.1 p.2) (ENNReal.ofReal (2 + ε))
        ((withDensityReal (R.ρ 0)).prod (withDensityReal (R.ρ 0)))) atTop (𝓝 0))
    (q : ℝ) (hq : 1 ≤ q) :
    Tendsto (fun L : ℕ => ⨆ t : {t : ℝ // 0 ≤ t}, ⨆ N : {N : ℕ // 2 ≤ N},
        ∫⁻ ω, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy
            (fun x y => hL L x y - hTransport d R.D.s (Torus.realMode k) x y)
            (X N t.1.toNNReal ω) (withDensityReal (R.ρ t.1))| ^ q) ∂(P N)) atTop (𝓝 0) := by
  have hd := R.hd
  have hs0 := R.D.hs0
  have hs := R.hs
  have hsd : R.D.s < (d : ℝ) := R.D.hsd
  -- the constants of `alltime_Lp`
  obtain ⟨⟨p, hp1, C1, hC1⟩, h2, h3⟩ := alltime_Lp_proof' R c hc
  obtain ⟨C2, hC2⟩ := h2 2 (by norm_num)
  obtain ⟨m₀, M₀, hm₀, hbd⟩ := R.bounds
  have hM₀ : 0 < M₀ := lt_of_lt_of_le hm₀ ((hbd 0 le_rfl 0).1.trans (hbd 0 le_rfl 0).2)
  set φ : Torus d → ℝ := Torus.realMode k with hφdef
  have hφ : Torus.IsSmooth φ := HRS.FieldSingAux.isSmooth_realMode k
  obtain ⟨Bh, hBh0, hBh⟩ := fcg_hT_env hd hs0 hs hc hφ
  obtain ⟨cB, CB, hcB, hCB⟩ := h3 (max B 0 + Bh)
  set kk : ℕ → Torus d → Torus d → ℝ := fun L x y => hL L x y - hTransport d R.D.s φ x y with hkk
  have hkk' : ∀ L, Measurable (Function.uncurry (kk L)) ∧ (∀ x y, kk L x y = kk L y x) ∧
      ∀ x y, x ≠ y → |kk L x y| ≤ (max B 0 + Bh) * (periodicRiesz d R.D.s (x - y) + c) :=
    fun L => fcg_diff_kernel hsd hc hφ hBh (hLd L) (hLB L)
  -- time `0`
  set μ0 : Measure (Torus d) := withDensityReal (R.ρ 0) with hμ0
  have h0dens : IsProbDensity (R.ρ 0) := (R.mf 1 one_pos).density 0 ⟨le_rfl, zero_le_one⟩
  have hprob0 : IsProbabilityMeasure μ0 := isProb_withDensityReal h0dens
  set κ : ℝ := M₀ / m₀ with hκ
  set a0 : ℕ → ℝ≥0∞ := fun L => ∫⁻ z : Torus d × Torus d, ENNReal.ofReal (kk L z.1 z.2 ^ 2) ∂(μ0.prod μ0)
    with ha0
  have ha0lim : Tendsto a0 atTop (𝓝 0) := by
    refine fcg_small (μ0 := μ0) (μt := μ0) (κ := 1) (by simp) (fun L => (hkk' L).1) hε hconv
  have hev0 : ∀ᶠ L in atTop, a0 L < ⊤ := ha0lim.eventually (gt_mem_nhds (by simp))
  -- the uniform size
  set A' : ℕ → ℝ := fun L => 7 * (ENNReal.ofReal κ * ENNReal.ofReal κ * a0 L).toReal with hA'
  have hA'lim : Tendsto A' atTop (𝓝 0) := by
    have h1 : Tendsto (fun L => ENNReal.ofReal κ * ENNReal.ofReal κ * a0 L) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul ha0lim
        (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) : _ ∨ _)
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    rw [ENNReal.toReal_zero] at h2
    simpa [hA'] using h2.const_mul 7
  -- the pointwise (in `t`, `L`) bound
  have key : ∀ t : ℝ, 0 ≤ t → ∀ L, a0 L < ⊤ → ∀ N : {N : ℕ // 2 ≤ N},
      ∫⁻ ω, ENNReal.ofReal (|(N.1 : ℝ) * modulatedEnergy (kk L)
          (X N.1 t.toNNReal ω) (withDensityReal (R.ρ t))| ^ q) ∂(P N.1) ≤
        fcgBound C1 C2 (fcgM q p cB CB) p (A' L) := by
    intro t ht0 L hL0 N
    set μt : Measure (Torus d) := withDensityReal (R.ρ t) with hμt
    have hdens : IsProbDensity (R.ρ t) := (R.mf (t + 1) (by linarith)).density t ⟨ht0, by linarith⟩
    have hprob : IsProbabilityMeasure μt := isProb_withDensityReal hdens
    have hle : μt ≤ ENNReal.ofReal κ • μ0 :=
      fcg_withDensity_le hm₀ hM₀ (fun x => (hbd 0 le_rfl x).1) (fun x => (hbd t ht0 x).2)
    have hprod : μt.prod μt ≤ (ENNReal.ofReal κ * ENNReal.ofReal κ) • μ0.prod μ0 := by
      calc μt.prod μt ≤ (ENNReal.ofReal κ • μ0).prod (ENNReal.ofReal κ • μ0) := Measure.prod_mono hle hle
        _ = (ENNReal.ofReal κ * ENNReal.ofReal κ) • μ0.prod μ0 := by
          rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    have hbnd : ∫⁻ z : Torus d × Torus d, ENNReal.ofReal (kk L z.1 z.2 ^ 2) ∂(μt.prod μt) ≤
        ENNReal.ofReal κ * ENNReal.ofReal κ * a0 L := by
      calc _ ≤ ∫⁻ z : Torus d × Torus d, ENNReal.ofReal (kk L z.1 z.2 ^ 2)
            ∂((ENNReal.ofReal κ * ENNReal.ofReal κ) • μ0.prod μ0) := lintegral_mono' hprod le_rfl
        _ = _ := by rw [lintegral_smul_measure]; rfl
    have hfin : ENNReal.ofReal κ * ENNReal.ofReal κ * a0 L ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hL0.ne
    have hL' : ∫⁻ z : Torus d × Torus d, ENNReal.ofReal (kk L z.1 z.2 ^ 2) ∂(μt.prod μt) < ⊤ :=
      lt_of_le_of_lt hbnd hfin.lt_top
    have hAt : 7 * ∫ z : Torus d × Torus d, kk L z.1 z.2 ^ 2 ∂(μt.prod μt) ≤ A' L := by
      have h2 : ∫ z : Torus d × Torus d, kk L z.1 z.2 ^ 2 ∂(μt.prod μt) =
          (∫⁻ z : Torus d × Torus d, ENNReal.ofReal (kk L z.1 z.2 ^ 2) ∂(μt.prod μt)).toReal :=
        integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => sq_nonneg _)
          ((((hkk' L).1.pow_const 2)).aestronglyMeasurable)
      rw [h2]
      simp only [hA']
      gcongr
    obtain ⟨N, hN⟩ := N
    have hN1 : 1 ≤ N := by omega
    obtain ⟨hm, hsy, hev'⟩ := hkk' L
    have hint : Integrable (fun z : Torus d × Torus d => kk L z.1 z.2 ^ 2) (μt.prod μt) := by
      refine ⟨((hm.pow_const 2)).aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      refine lt_of_le_of_lt (le_of_eq ?_) hL'
      refine lintegral_congr fun z => ?_
      rw [Real.enorm_eq_ofReal (sq_nonneg _)]
    obtain ⟨hZm, hZ2⟩ := fcg_L2 μt hm hsy hint N hN1
    have : IsProbabilityMeasure (Measure.pi fun _ : Fin N => μt) := inferInstance
    have hQprob : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d R.D.s) N R.β μt) :=
      HRS.Q32c.q32c_Q_isProb hd hs0 hsd R.hβ (Λ := max M₀ 1) (le_max_right _ _) hdens
        (fun x => (hbd t ht0 x).2.trans (le_max_left _ _)) (by omega)
    obtain ⟨hPQ, hd1⟩ := hC1 N hN (P N) (X₀ N) (W N) (X N) (hreal N hN1) t ht0
    obtain ⟨hQP, hd2⟩ := hC2 N hN t ht0
    obtain ⟨hmeasX⟩ : Nonempty (Measurable (X N t.toNNReal)) :=
      ⟨((hreal N hN1).solution (t + 1)).adapted t.toNNReal⟩
    have hexp : ∫⁻ x, ENNReal.ofReal (Real.exp (cB * |(N : ℝ) * modulatedEnergy (kk L) x μt|))
        ∂(modulatedGibbs (periodicRiesz d R.D.s) N R.β μt) ≤ ENNReal.ofReal CB := by
      refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) (hCB N hN t ht0 (kk L) hm hsy hev')
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
      congr 2; ring
    have : IsFiniteMeasure ((P N).map (X N t.toNNReal)) := inferInstance
    have hZ2' : ∫⁻ x, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy (kk L) x μt| ^ (2 : ℕ))
        ∂(Measure.pi fun _ : Fin N => μt) ≤ ENNReal.ofReal (A' L) :=
      hZ2.trans (ENNReal.ofReal_le_ofReal hAt)
    have htr := fcg_transfer (E := Config d N) (Measure.pi fun _ : Fin N => μt)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β μt) ((P N).map (X N t.toNNReal)) hQP hPQ hp1 hcB
      hd1 hd2 hZm hexp hZ2' hq
    have hmap := lintegral_map (μ := P N)
      (f := fun x => ENNReal.ofReal (|(N : ℝ) * modulatedEnergy (kk L) x μt| ^ q))
      (ENNReal.measurable_ofReal.comp (hZm.abs.pow_const q)) hmeasX
    rw [hmap] at htr
    exact htr
  -- conclusion
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (fcg_bound_tendsto C1 C2 (fcgM q p cB CB) p hp1 hA'lim) (Filter.Eventually.of_forall fun L => zero_le) ?_
  filter_upwards [hev0] with L hL0
  exact iSup_le fun t => iSup_le fun N => key t.1 t.2 L hL0 N

end HRS.MC.Sec7.S7UCA

end
