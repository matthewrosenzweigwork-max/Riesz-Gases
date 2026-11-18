import HRS.MC.S7FCG
import HRS.Dynamics.InitialData

/-!
# FC-G2: uniform-in-`(L, N, t)` bound for the dominated convergence in `t` (packet `s7fcw6_`)

Route: the proof of `s7_FC_G_strong_tail_proof` (`HRS/MC/S7FCG.lean`) with the `L`-dependent constant `A L` replaced
by a bound uniform in `L` and `t ∈ [0,T]`.  The `L`-uniform bound comes from the envelope `|kk_L(x,y)| ≤ B' (g(x-y)+c)`
(off the diagonal, which is `μ⁰⊗μ⁰`-null) and the integrability of `g(x-y)²` under `μ⁰ ⊗ μ⁰`
(`HRS.periodicRiesz_sq_integrable`, `2s < d`); the time-`t` law is compared with `μ⁰` via `μ^t ≤ (M₀/m₀) μ⁰`.
No `hconv`/`ε` hypothesis is used.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.S7FCW6

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.Sec7.FCG

variable {d : ℕ}

/-- The diagonal is `(μ ⊗ μ)`-null for `μ = ρ dx`. -/
theorem s7fcw6_diag_ae (ρ : Torus d → ℝ) (hd : 1 ≤ d) :
    ∀ᵐ z ∂((withDensityReal ρ).prod (withDensityReal ρ)), z.1 ≠ z.2 := by
  have hm : MeasurableSet {z : Torus d × Torus d | z.1 ≠ z.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  rw [Measure.ae_prod_iff_ae_ae hm]
  refine Eventually.of_forall fun x => ?_
  have h0 : withDensityReal ρ {x} = 0 :=
    (HRS.InitialDataAux.withDensityReal_ac ρ) (volume_singleton_torus hd x)
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) h0
  have hxy : x = y := by
    by_contra hne
    exact hy (by simpa using hne)
  exact Set.mem_singleton_iff.2 hxy.symm

/-- The `L`-uniform, `t`-uniform bound for the `L²` part; FC-G with the constants of `alltime_Lp` kept. -/
theorem s7_FC_G2_unif_proof (R : Regime d) (T : ℝ) (hT : 0 < T) (k : NonzeroLattice d)
    (hL : ℕ → Torus d → Torus d → ℝ) (hLd : ∀ L, s7_IsFiniteRankSmooth (hL L))
    (B c : ℝ) (hc : EnvelopeConst (d := d) R.D.s c)
    (hLB : ∀ L x y, x ≠ y → |hL L x y| ≤ B * (periodicRiesz d R.D.s (x - y) + c))
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ L : ℕ, ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy
          (fun x y => hL L x y - hTransport d R.D.s (Torus.realMode k) x y)
          (X N t.toNNReal ω) (withDensityReal (R.ρ t))| ^ q) ∂(P N) ≤ ENNReal.ofReal C := by
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
  set Bt : ℝ := max B 0 + Bh with hBt
  -- the reference background `μ⁰ = ρ⁰ dx`
  have h0dens : IsProbDensity (R.ρ 0) := (R.mf T hT).density 0 ⟨le_rfl, hT.le⟩
  have hprob0 : IsProbabilityMeasure (withDensityReal (R.ρ 0)) := isProb_withDensityReal h0dens
  -- the integrable majorant `2 Bt² g(x-y)² + 2 Bt² c²` of the kernel squared
  set F0 : Torus d × Torus d → ℝ := fun z =>
    2 * Bt ^ 2 * periodicRiesz d R.D.s (z.1 - z.2) ^ 2 + 2 * Bt ^ 2 * c ^ 2 with hF0
  have hsq := HRS.periodicRiesz_sq_integrable hd hs0 hs (R.ρ 0) h0dens M₀ (fun x => (hbd 0 le_rfl x).2)
  have hFint : Integrable F0 ((withDensityReal (R.ρ 0)).prod (withDensityReal (R.ρ 0))) :=
    (hsq.const_mul (2 * Bt ^ 2)).add (integrable_const (2 * Bt ^ 2 * c ^ 2))
  set S : ENNReal := ∫⁻ z, ENNReal.ofReal (F0 z) ∂((withDensityReal (R.ρ 0)).prod (withDensityReal (R.ρ 0)))
    with hSdef
  have hS : S < ⊤ := hFint.lintegral_lt_top
  have hdiag := s7fcw6_diag_ae (R.ρ 0) (by omega)
  -- the `L`-uniform bound off the diagonal
  have hL0 : ∀ L, ∫⁻ z, ENNReal.ofReal (kk L z.1 z.2 ^ 2)
      ∂((withDensityReal (R.ρ 0)).prod (withDensityReal (R.ρ 0))) ≤ S := by
    intro L
    refine lintegral_mono_ae ?_
    filter_upwards [hdiag] with z hz
    apply ENNReal.ofReal_le_ofReal
    have h1 := (hkk' L).2.2 z.1 z.2 hz
    have h2 : kk L z.1 z.2 ^ 2 ≤ (Bt * (periodicRiesz d R.D.s (z.1 - z.2) + c)) ^ 2 := by
      have := abs_le.1 h1
      exact sq_le_sq' this.1 this.2
    have h3 : (Bt * (periodicRiesz d R.D.s (z.1 - z.2) + c)) ^ 2 ≤ F0 z := by
      simp only [hF0]
      nlinarith [mul_nonneg (sq_nonneg Bt) (sq_nonneg (periodicRiesz d R.D.s (z.1 - z.2) - c))]
    linarith
  -- comparison of the time-`t` product law with `μ⁰ ⊗ μ⁰`
  set κ : ℝ≥0∞ := ENNReal.ofReal (M₀ / m₀) * ENNReal.ofReal (M₀ / m₀) with hκ
  have hLt : ∀ L, ∀ t : ℝ, 0 ≤ t → ∫⁻ z, ENNReal.ofReal (kk L z.1 z.2 ^ 2)
      ∂((withDensityReal (R.ρ t)).prod (withDensityReal (R.ρ t))) ≤ κ * S := by
    intro L t ht0
    have hle : withDensityReal (R.ρ t) ≤ ENNReal.ofReal (M₀ / m₀) • withDensityReal (R.ρ 0) :=
      fcg_withDensity_le hm₀ hM₀ (fun x => (hbd 0 le_rfl x).1) (fun x => (hbd t ht0 x).2)
    have hprod : (withDensityReal (R.ρ t)).prod (withDensityReal (R.ρ t)) ≤
        κ • (withDensityReal (R.ρ 0)).prod (withDensityReal (R.ρ 0)) := by
      calc (withDensityReal (R.ρ t)).prod (withDensityReal (R.ρ t))
          ≤ (ENNReal.ofReal (M₀ / m₀) • withDensityReal (R.ρ 0)).prod
              (ENNReal.ofReal (M₀ / m₀) • withDensityReal (R.ρ 0)) := Measure.prod_mono hle hle
        _ = κ • (withDensityReal (R.ρ 0)).prod (withDensityReal (R.ρ 0)) := by
          rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    calc ∫⁻ z, ENNReal.ofReal (kk L z.1 z.2 ^ 2)
          ∂((withDensityReal (R.ρ t)).prod (withDensityReal (R.ρ t)))
        ≤ ∫⁻ z, ENNReal.ofReal (kk L z.1 z.2 ^ 2)
          ∂(κ • (withDensityReal (R.ρ 0)).prod (withDensityReal (R.ρ 0))) := lintegral_mono' hprod le_rfl
      _ = κ * ∫⁻ z, ENNReal.ofReal (kk L z.1 z.2 ^ 2)
          ∂((withDensityReal (R.ρ 0)).prod (withDensityReal (R.ρ 0))) := by
          rw [lintegral_smul_measure]; rfl
      _ ≤ κ * S := by gcongr; exact hL0 L
  set Lbig : ℝ≥0∞ := κ * S with hLbig
  have hLbig_ne : Lbig ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hS.ne
  set Acap : ℝ := 7 * Lbig.toReal with hAcap
  have hbound_int : ∀ L, ∀ t : ℝ, 0 ≤ t → ∫ z : Torus d × Torus d, kk L z.1 z.2 ^ 2
      ∂((withDensityReal (R.ρ t)).prod (withDensityReal (R.ρ t))) ≤ Lbig.toReal := by
    intro L t ht0
    obtain ⟨hm, -, -⟩ := hkk' L
    have hm2 : Measurable (fun z : Torus d × Torus d => kk L z.1 z.2) := hm
    have hmeas : AEStronglyMeasurable (fun z : Torus d × Torus d => kk L z.1 z.2 ^ 2)
        ((withDensityReal (R.ρ t)).prod (withDensityReal (R.ρ t))) :=
      (hm2.pow_const 2).aestronglyMeasurable
    have hnn : (0 : (Torus d × Torus d) → ℝ) ≤ᵐ[(withDensityReal (R.ρ t)).prod (withDensityReal (R.ρ t))]
        (fun z : Torus d × Torus d => kk L z.1 z.2 ^ 2) :=
      Eventually.of_forall fun z => sq_nonneg _
    rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
    exact ENNReal.toReal_mono hLbig_ne (hLt L t ht0)
  -- the transfer bound at the uniform constant
  have key : ∀ L : ℕ, ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy (kk L) (X N t.toNNReal ω)
        (withDensityReal (R.ρ t))| ^ q) ∂(P N) ≤
        fcgBound C1 C2 (fcgM q p cB CB) p Acap := by
    intro L N hN t ht
    have hN1 : 1 ≤ N := by omega
    have ht0 : 0 ≤ t := ht.1
    have hdens : IsProbDensity (R.ρ t) := (R.mf T hT).density t ht
    have hprob : IsProbabilityMeasure (withDensityReal (R.ρ t)) := isProb_withDensityReal hdens
    obtain ⟨hm, hsy, hev'⟩ := hkk' L
    have hint : Integrable (fun z : Torus d × Torus d => kk L z.1 z.2 ^ 2)
        ((withDensityReal (R.ρ t)).prod (withDensityReal (R.ρ t))) := by
      refine ⟨((hm.pow_const 2)).aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun z => ?_))
        (lt_of_le_of_lt (hLt L t ht0) (lt_top_iff_ne_top.2 hLbig_ne))
      rw [Real.enorm_eq_ofReal (sq_nonneg _)]
    obtain ⟨hZm, hZ2⟩ := fcg_L2 (withDensityReal (R.ρ t)) hm hsy hint N hN1
    have : IsProbabilityMeasure (Measure.pi fun _ : Fin N => withDensityReal (R.ρ t)) := inferInstance
    have hQprob : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))) :=
      HRS.Q32c.q32c_Q_isProb hd hs0 hsd R.hβ (Λ := max M₀ 1) (le_max_right _ _) hdens
        (fun x => (hbd t ht0 x).2.trans (le_max_left _ _)) (by omega)
    obtain ⟨hPQ, hd1⟩ := hC1 N hN (P N) (X₀ N) (W N) (X N) (hreal N hN1) t ht0
    obtain ⟨hQP, hd2⟩ := hC2 N hN t ht0
    obtain ⟨hmeasX⟩ : Nonempty (Measurable (X N t.toNNReal)) :=
      ⟨((hreal N hN1).solution T).adapted t.toNNReal⟩
    have hexp : ∫⁻ x, ENNReal.ofReal (Real.exp (cB * |(N : ℝ) * modulatedEnergy (kk L) x
          (withDensityReal (R.ρ t))|))
        ∂(modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))) ≤ ENNReal.ofReal CB := by
      refine le_trans (le_of_eq (lintegral_congr fun x => ?_))
        (hCB N hN t ht0 (kk L) hm hsy hev')
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
      congr 2; ring
    have : IsFiniteMeasure ((P N).map (X N t.toNNReal)) := inferInstance
    have hA : ∫⁻ x, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy (kk L) x (withDensityReal (R.ρ t))| ^ (2 : ℕ))
        ∂(Measure.pi fun _ : Fin N => withDensityReal (R.ρ t)) ≤ ENNReal.ofReal Acap :=
      hZ2.trans (ENNReal.ofReal_le_ofReal (by linarith [hbound_int L t ht0]))
    have htr := fcg_transfer (E := Config d N) (Measure.pi fun _ : Fin N => withDensityReal (R.ρ t))
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t)))
      ((P N).map (X N t.toNNReal)) hQP hPQ hp1 hcB hd1 hd2 hZm hexp hA hq
    have hmap := lintegral_map (μ := P N)
      (f := fun x => ENNReal.ofReal (|(N : ℝ) * modulatedEnergy (kk L) x (withDensityReal (R.ρ t))| ^ q))
      (ENNReal.measurable_ofReal.comp (hZm.abs.pow_const q)) hmeasX
    rw [hmap] at htr
    exact htr
  -- finiteness of the uniform constant
  have hfb_ne : fcgBound C1 C2 (fcgM q p cB CB) p Acap ≠ ⊤ := by
    unfold fcgBound
    have h1 : ENNReal.ofReal Acap ^ (1 / (2 : ℝ)) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    have h2 : ENNReal.ofReal Acap ^ (1 / (2 : ℝ)) * ENNReal.ofReal C2 ≠ ⊤ :=
      ENNReal.mul_ne_top h1 ENNReal.ofReal_ne_top
    have h3 : (ENNReal.ofReal Acap ^ (1 / (2 : ℝ)) * ENNReal.ofReal C2) ^ (1 / (2 : ℝ)) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) h2
    have h4 : ENNReal.ofReal (fcgM q p cB CB) ^ (1 / (2 : ℝ)) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    have h5 : (ENNReal.ofReal Acap ^ (1 / (2 : ℝ)) * ENNReal.ofReal C2) ^ (1 / (2 : ℝ)) *
        ENNReal.ofReal (fcgM q p cB CB) ^ (1 / (2 : ℝ)) ≠ ⊤ := ENNReal.mul_ne_top h3 h4
    have hcj : 1 < Real.conjExponent p := (Real.HolderConjugate.conjExponent hp1).symm.lt
    have h6 : ((ENNReal.ofReal Acap ^ (1 / (2 : ℝ)) * ENNReal.ofReal C2) ^ (1 / (2 : ℝ)) *
        ENNReal.ofReal (fcgM q p cB CB) ^ (1 / (2 : ℝ))) ^ (1 / Real.conjExponent p) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (div_nonneg zero_le_one (by linarith)) h5
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h6
  refine ⟨(fcgBound C1 C2 (fcgM q p cB CB) p Acap).toReal, fun L N hN t ht => ?_⟩
  rw [ENNReal.ofReal_toReal hfb_ne]
  exact key L N hN t ht

end HRS.MC.Sec7.S7FCW6

end
