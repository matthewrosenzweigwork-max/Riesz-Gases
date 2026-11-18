import HRS.MC.S7FCGAbs
import HRS.MC.S7FCGKer
import HRS.MC.S7FCGSmall
import HRS.PDE.MovFinalConsumers
import HRS.Equilibrium.Q32cAux2

/-!
# FC-G: removal of the pair-kernel approximation (`s7_FC_G_strong_tail`, relocated proof)

Route: transfer `f_N^t << Q_N^t << (mu^t)^{otimes N}` (the `alltime_Lp` items 1-2), the exponential pair
moment (item 3) for the envelope kernel `h_L - h`, and the `L^2` bound `q08_energy_L2` (the time-`0`
`L^{2+eps}` convergence is moved to time `t` by `mu^t <= (M_0/m_0) mu^0`); Holder + Cauchy--Schwarz
interpolation (`S7FCGAbs`).  Packet prefix `fcg`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.FCG

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ}

/-- `mu^t <= (M_0/m_0) mu^0` from the uniform bounds `m_0 <= rho <= M_0`. -/
theorem fcg_withDensity_le {ρ ρ₀ : Torus d → ℝ} {m₀ M₀ : ℝ} (hm₀ : 0 < m₀) (hM₀ : 0 < M₀)
    (h0 : ∀ x, m₀ ≤ ρ₀ x) (h1 : ∀ x, ρ x ≤ M₀) :
    withDensityReal ρ ≤ ENNReal.ofReal (M₀ / m₀) • withDensityReal ρ₀ := by
  refine Measure.le_iff.2 fun s hs => ?_
  unfold withDensityReal
  rw [withDensity_apply _ hs, Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  have hκ : 0 ≤ M₀ / m₀ := by positivity
  rw [← ENNReal.ofReal_mul hκ]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ρ x ≤ M₀ := h1 x
    _ = (M₀ / m₀) * m₀ := by field_simp
    _ ≤ (M₀ / m₀) * ρ₀ x := mul_le_mul_of_nonneg_left (h0 x) hκ

theorem s7_FC_G_strong_tail_proof (R : Regime d) (T : ℝ) (hT : 0 < T) (k : NonzeroLattice d)
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
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (q : ℝ) (hq : 1 ≤ q) :
    Tendsto (fun L : ℕ => ⨆ N : {N : ℕ // 2 ≤ N},
        ∫⁻ ω, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy
            (fun x y => hL L x y - hTransport d R.D.s (Torus.realMode k) x y)
            (X N t.toNNReal ω) (withDensityReal (R.ρ t))| ^ q) ∂(P N)) atTop (𝓝 0) := by
  have hd := R.hd
  have hs0 := R.D.hs0
  have hs := R.hs
  have hsd : R.D.s < (d : ℝ) := R.D.hsd
  have ht0 : 0 ≤ t := ht.1
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
  -- the time-`t` background
  set μt : Measure (Torus d) := withDensityReal (R.ρ t) with hμt
  have hdens : IsProbDensity (R.ρ t) := (R.mf T hT).density t ht
  have hprob : IsProbabilityMeasure μt := isProb_withDensityReal hdens
  have h0dens : IsProbDensity (R.ρ 0) := (R.mf T hT).density 0 ⟨le_rfl, hT.le⟩
  have hprob0 : IsProbabilityMeasure (withDensityReal (R.ρ 0)) := isProb_withDensityReal h0dens
  -- smallness of the `L^2` norm
  have hle : μt ≤ ENNReal.ofReal (M₀ / m₀) • withDensityReal (R.ρ 0) :=
    fcg_withDensity_le hm₀ hM₀ (fun x => (hbd 0 le_rfl x).1) (fun x => (hbd t ht0 x).2)
  have hsmall := fcg_small hle (fun L => (hkk' L).1) hε hconv
  -- eventually the squares are integrable
  have hev : ∀ᶠ L in atTop, ∫⁻ z : Torus d × Torus d, ENNReal.ofReal (kk L z.1 z.2 ^ 2)
      ∂(μt.prod μt) < ⊤ := hsmall.eventually (gt_mem_nhds (by simp))
  -- the real size
  set A : ℕ → ℝ := fun L => 7 * ∫ z : Torus d × Torus d, kk L z.1 z.2 ^ 2 ∂(μt.prod μt) with hA
  have hAlim : Tendsto A atTop (𝓝 0) := by
    have h1 : Tendsto (fun L => (∫⁻ z : Torus d × Torus d, ENNReal.ofReal (kk L z.1 z.2 ^ 2)
        ∂(μt.prod μt)).toReal) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsmall
      rw [ENNReal.toReal_zero] at this
      exact this
    have h2 : ∀ L, ∫ z : Torus d × Torus d, kk L z.1 z.2 ^ 2 ∂(μt.prod μt) =
        (∫⁻ z : Torus d × Torus d, ENNReal.ofReal (kk L z.1 z.2 ^ 2) ∂(μt.prod μt)).toReal := fun L =>
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => sq_nonneg _)
        (((hkk' L).1.pow_const 2).aestronglyMeasurable)
    simp only [hA, h2]
    simpa using h1.const_mul 7
  -- the pointwise (in `L`) bound
  have key : ∀ L, (∫⁻ z : Torus d × Torus d, ENNReal.ofReal (kk L z.1 z.2 ^ 2) ∂(μt.prod μt) < ⊤) →
      ∀ N : {N : ℕ // 2 ≤ N}, ∫⁻ ω, ENNReal.ofReal (|(N.1 : ℝ) * modulatedEnergy (kk L)
          (X N.1 t.toNNReal ω) μt| ^ q) ∂(P N.1) ≤
        fcgBound C1 C2 (fcgM q p cB CB) p (A L) := by
    intro L hL' N
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
      ⟨((hreal N hN1).solution T).adapted t.toNNReal⟩
    have hexp : ∫⁻ x, ENNReal.ofReal (Real.exp (cB * |(N : ℝ) * modulatedEnergy (kk L) x μt|))
        ∂(modulatedGibbs (periodicRiesz d R.D.s) N R.β μt) ≤ ENNReal.ofReal CB := by
      refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) (hCB N hN t ht0 (kk L) hm hsy hev')
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
      congr 2; ring
    have : IsFiniteMeasure ((P N).map (X N t.toNNReal)) := inferInstance
    have htr := fcg_transfer (E := Config d N) (Measure.pi fun _ : Fin N => μt)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β μt) ((P N).map (X N t.toNNReal)) hQP hPQ hp1 hcB
      hd1 hd2 hZm hexp hZ2 hq
    have hmap := lintegral_map (μ := P N)
      (f := fun x => ENNReal.ofReal (|(N : ℝ) * modulatedEnergy (kk L) x μt| ^ q))
      (ENNReal.measurable_ofReal.comp (hZm.abs.pow_const q)) hmeasX
    rw [hmap] at htr
    exact htr
  -- conclusion
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (fcg_bound_tendsto C1 C2 (fcgM q p cB CB) p hp1 hAlim) (Filter.Eventually.of_forall fun L => zero_le) ?_
  filter_upwards [hev] with L hL'
  exact iSup_le fun N => key L hL' N

end HRS.MC.Sec7.FCG

end
