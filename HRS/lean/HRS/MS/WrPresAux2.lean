import HRS.MS.WrPresAux1

/-!
# HRS.MS.WrPresAux2 -- Euclidean weak pressure upper bound `K^q_{N,β}(μ) ≤ e^{C N δ_N}` (WR-5, part 2)

Packet WR-5 of `docs/SUPP_FOUND_PACKETS.md` (Track D).  Whole-space port of
`HRS.weak_pressure_upper_aux` (`HRS/Energy/WeakReference.lean:6234`), and of the intermediate
`HRS.WeakRef.variance_at` (`:5639`), with the torus data `(c₀, Λ, cstar, periodicRiesz)` replaced by the
Euclidean data `ρ ≤ M` only (no lower bound, no smoothness; flag F5) and the envelope
`q x y ≤ A (1 + rieszWeight s (x - y))` for `x ≠ y`.

* `wr5_variance_at_E` (generic measurable space): the variance of the energy `N F_N^q` under the Gibbs law
  `pairGibbsLawE q N t μ` is `≤ 8 E C_b ψ₂(2NP/t) + (12 (1 + 2 E C_a)² + 12 + 12 E C_m²) ψ₂(N)`, given the
  row bounds `hr1, hr2` and the marginal `L²` bound at `t`.
* `weak_pressure_upper_E`: there are `a₀ > 0` and `C` (depending only on `(d, s, βm, βp, M, A)`, quantified
  before `ρ, q, a, N, β`) with `K^q_{N,β}(ρ dx) = pairPartitionE ≤ exp (C N δ_N)` for all probability
  densities `ρ ≤ M`, symmetric nonnegative measurable kernels with the envelope and row bound `a < a₀`,
  `N ≥ 2`, `β ∈ [βm, βp]`.
* `weak_pressure_upper_pairNormalizer_E`: the same bound for the frozen Bochner normaliser
  `HRS.Whole.pairNormalizer`, together with `GibbsWellDefined`, `1 ≤ pairNormalizer`, and the real logarithm
  form `Real.log (pairNormalizer) ≤ C N δ_N` (not a junk value: the normaliser is `≥ 1`, hence positive).

Differences from the torus statement (all harmless): the instance `IsProbabilityMeasure` follows from
`IsProbDensity`; the conclusion is stated for `pairPartitionE` (`ℝ≥0∞`, definitionally the torus
`pairPartition`) and then for the frozen `pairNormalizer`.  Helper lemmas carry the prefix `wr5_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.External

variable {E : Type*} [MeasurableSpace E] {d : ℕ}

set_option maxHeartbeats 1600000 in
/-- **Variance of the energy** under the weak Gibbs law at inverse temperature `t` (port of
`HRS.WeakRef.variance_at`, generic measurable space `E`). -/
theorem wr5_variance_at_E (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {μ : Measure E} [IsProbabilityMeasure μ] {a : ℝ} {q : E → E → ℝ}
    (hK : EWeakKernel μ a q) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {Ca Cb Cm P E' : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCm : 0 ≤ Cm) (hP : 1 ≤ P)
    (hE : E' = Real.exp (2 * P))
    (hr1 : ∀ x, ∀ L : ℝ, 0 < L →
      ∫ y, max (q x y - L) 0 ∂μ ≤ Ca * L ^ (1 - (d : ℝ) / HRS.WeakRef.sigmaOf d s))
    (hr2 : ∀ x, ∀ L : ℝ, 1 ≤ L →
      ∫ y, (min (q x y) L) ^ 2 ∂μ ≤ Cb * HRS.WeakRef.psi2 d s L)
    {N : ℕ} (hN : 2 ≤ N) {t : ℝ} (ht : 0 < t) (htP : t ≤ P) (hta : t * a ≤ 1 / (16 * E'))
    (hmarg : ∃ f : E → ℝ≥0∞,
      (pairGibbsLawE q N t μ).map (fun X => X ⟨0, by omega⟩) = μ.withDensity f ∧ Measurable f ∧
        ∫ x, ((f x).toReal - 1) ^ 2 ∂μ ≤ (Cm * deltaN d s N) ^ 2) :
    variance (enGE q μ N) (pairGibbsLawE q N t μ)
      ≤ 8 * E' * Cb * HRS.WeakRef.psi2 d s (2 * N * P / t)
        + (12 * (1 + 2 * E' * Ca) ^ 2 + 12 + 12 * E' * Cm ^ 2) * HRS.WeakRef.psi2 d s N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hσ0 := HRS.WeakRef.sigmaOf_pos hd hs0
  have hE1 : 1 ≤ E' := by rw [hE]; exact Real.one_le_exp (by linarith)
  have hE0 : 0 < E' := by linarith
  have hNR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hN1R : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
  set V := mkV_E hK ha0 ht.le with hV
  have hVM : V.M = t * a := rfl
  have hVM' : V.M' = 0 := rfl
  have hVγ : V.γ = a := rfl
  have hVq : V.q = q := rfl
  set D : ℝ := Real.exp (V.M + V.M' + t * V.γ) with hDdef
  have hta0 : 0 ≤ t * a := mul_nonneg ht.le ha0
  have hDe : D = Real.exp (t * a + t * a) := by
    simp only [hDdef, hVM, hVM', hVγ]; congr 1; ring
  have htaP : t * a ≤ P := by
    have : 1 / (16 * E') ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hDE : D ≤ E' := by
    rw [hDe, hE]; exact Real.exp_le_exp.2 (by linarith)
  have hD1 : 1 ≤ D := by rw [hDe]; exact Real.one_le_exp (by linarith)
  have hD0 : 0 ≤ D := by linarith
  have hκ : weakKappa V t ≤ 1 / 2 := by
    have : weakKappa V t = 4 * D * (t * a) := by
      simp only [weakKappa, hDdef, hVγ]
    rw [this]
    have h1 : D * (t * a) ≤ E' * (1 / (16 * E')) := mul_le_mul hDE hta hta0 hE0.le
    have h2 : E' * (1 / (16 * E')) = 1 / 16 := by field_simp
    linarith
  have hκ0 : 0 ≤ weakKappa V t := weakKappa_nonneg V ht.le
  rw [pairGibbsLawE_eq_pinnedLaw_E hK ha0 ht.le (Nat.succ_pos n)] at hmarg ⊢
  obtain ⟨f, hfmap, hfm, hfint⟩ := hmarg
  have hle := HRS.WeakRef.Abs.pinned_marginal_le_const V ht.le (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩
  obtain ⟨g, hgm, hg, hgπ, hgf⟩ := HRS.WeakRef.Abs.clamp_density hfm hfmap hD0 hle
  -- the energy and the centred version
  set Nr : ℝ := ((n + 1 : ℕ) : ℝ) with hNr
  set I₂ : ℝ := ∫ p : E × E, q p.1 p.2 ∂(μ.prod μ) with hI₂
  have hI₂' : ∫ x, ∫ y, q x y ∂μ ∂μ = I₂ := by
    rw [hI₂, integral_prod _ hK.wr1_integrable_prod]
  set G : (Fin (n + 1) → E) → ℝ := fun X => enGE q μ (n + 1) X - Nr / 2 * I₂ with hGdef
  have hG : ∀ X, G X = (1 / Nr) * HRS.External.pairEnergy V X - ∑ k, ∫ y, V.q (X k) y ∂μ := by
    intro X
    simp only [hGdef, enGE, modEnergyE, HRS.External.pairEnergy, hVq, hI₂']
    rw [← hNr]
    field_simp
    ring
  -- Qb
  set L : ℝ := 2 * Nr * P / t with hL
  have hLge : 2 * Nr ≤ L := by
    rw [hL, le_div_iff₀ ht]
    nlinarith
  have hL1 : 1 ≤ L := by linarith
  have hQb : ∀ x, ∫ z, V.q x z ^ 2 * Real.exp (-((t / Nr) * V.q z x)) ∂μ
      ≤ Cb * HRS.WeakRef.psi2 d s L := by
    intro x
    refine le_trans ?_ (hr2 x L hL1)
    have hqx : Measurable (q x) := hK.wr1_measurable_left x
    have hmin : Measurable fun y => (min (q x y) L) ^ 2 := (hqx.min measurable_const).pow_const 2
    have hint : Integrable (fun y => (min (q x y) L) ^ 2) μ :=
      HRS.WeakRef.Abs.intg_bdd hmin (C := L ^ 2) fun y => by
        rw [abs_of_nonneg (sq_nonneg _)]
        have h0 : 0 ≤ min (q x y) L := le_min (hK.nonneg x y) (by linarith)
        exact pow_le_pow_left₀ h0 (min_le_right _ _) 2
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => ?_) hint
      (Filter.Eventually.of_forall fun z => ?_)
    · exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    · simp only [hVq]
      rw [hK.symm z x]
      refine HRS.WeakRef.sq_exp_le_min (hK.nonneg x z) (by positivity) ?_
      have : t / Nr * L = 2 * P := by rw [hL]; field_simp
      rw [this]; linarith
  -- Thb
  set σ := HRS.WeakRef.sigmaOf d s with hσ
  set Lp : ℝ := Nr ^ (σ / d) with hLp
  have hLp0 : 0 < Lp := Real.rpow_pos_of_pos hNR _
  have hexp1 : Lp / Nr = Nr ^ (σ / d - 1) := by
    rw [hLp, Real.rpow_sub hNR, Real.rpow_one]
  have hexp2 : Lp ^ (1 - (d : ℝ) / σ) = Nr ^ (σ / d - 1) := by
    rw [hLp, ← Real.rpow_mul hNR.le]
    congr 1
    field_simp
  have hThb : ∀ (x : E) (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      ν₁ ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + t * V.γ)) • μ →
      ν₂ ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + t * V.γ)) • μ →
      (∀ A, MeasurableSet A → |ν₁.real A - ν₂.real A| ≤ 2 * weakKappa V t / Nr) →
      |∫ z, V.q x z ∂ν₁ - ∫ z, V.q x z ∂ν₂| ≤ (1 + 2 * E' * Ca) * Nr ^ (σ / d - 1) := by
    intro x ν₁ ν₂ h1 h2 hν₁ hν₂ hTV
    have := HRS.WeakRef.Abs.theta_abstract (μ := μ) (q := q) hK.meas hK.nonneg
      hK.wr1_integrable_row (L := Lp)
      (a₂ := Ca * Lp ^ (1 - (d : ℝ) / σ)) (D := D) (ε₀ := 2 * weakKappa V t / Nr) hLp0.le
      (fun y => hr1 y Lp hLp0) hD0 x ν₁ ν₂ hν₁ hν₂ hTV
    refine this.trans ?_
    rw [hexp2]
    have e1 : 2 * weakKappa V t / Nr * Lp ≤ Nr ^ (σ / d - 1) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hNR]
      have : Nr ^ (σ / d - 1) * Nr = Lp := by
        rw [← hexp1]; field_simp
      rw [this]
      have : 2 * weakKappa V t ≤ 1 := by linarith
      nlinarith
    have e2 : 2 * (D * (Ca * Nr ^ (σ / d - 1))) ≤ 2 * E' * Ca * Nr ^ (σ / d - 1) := by
      have h0 : 0 ≤ Nr ^ (σ / d - 1) := Real.rpow_nonneg hNR.le _
      have : D * (Ca * Nr ^ (σ / d - 1)) ≤ E' * (Ca * Nr ^ (σ / d - 1)) :=
        mul_le_mul_of_nonneg_right hDE (by positivity)
      nlinarith
    nlinarith
  have hgf' : ∫ y, (g y - 1) ^ 2 ∂μ ≤ (Cm * deltaN d s (n + 1)) ^ 2 := by rw [hgf]; exact hfint
  have hvar := HRS.WeakRef.Abs.variance_G_le V ht hn hκ (fun e : Empty => e.elim)
    (Qb := Cb * HRS.WeakRef.psi2 d s L)
    (Thb := (1 + 2 * E' * Ca) * Nr ^ (σ / d - 1)) (εf := Cm * deltaN d s (n + 1))
    hQb hThb g hgm hg hgπ hgf' G hG
  have hGm : Measurable G := ((hK.wr5_measurable_enG (n + 1)).sub_const _)
  have hvc : variance (enGE q μ (n + 1)) (pinnedLaw V (t / Nr) (n + 1) (fun e : Empty => e.elim))
      = variance G (pinnedLaw V (t / Nr) (n + 1) (fun e : Empty => e.elim)) := by
    have hP : IsProbabilityMeasure (pinnedLaw V (t / Nr) (n + 1) (fun e : Empty => e.elim)) :=
      isProb_pinnedLaw V (div_nonneg ht.le hNR.le) _ _
    have := variance_add_const hGm.aestronglyMeasurable (Nr / 2 * I₂)
      (μ := pinnedLaw V (t / Nr) (n + 1) (fun e : Empty => e.elim))
    have e : (fun ω => G ω + Nr / 2 * I₂) = enGE q μ (n + 1) := by
      funext X; simp only [hGdef]; ring
    rw [e] at this
    exact this
  rw [hvc]
  refine hvar.trans ?_
  -- arithmetic
  have hδ0 := deltaN_nonneg (d := d) s (show 1 ≤ n + 1 by omega)
  have hδ1 := HRS.WeakRef.deltaN_le_one hd hs0 hsd (show 1 ≤ n + 1 by omega)
  have hNδ := HRS.WeakRef.mul_deltaN_eq_psi2 (d := d) s (show 1 ≤ n + 1 by omega)
  have hpN := HRS.WeakRef.psi2_ge_one hd hs0 hN1R
  have hTh : Nr * ((1 + 2 * E' * Ca) * Nr ^ (σ / d - 1)) ^ 2
      ≤ (1 + 2 * E' * Ca) ^ 2 * HRS.WeakRef.psi2 d s Nr := by
    have := HRS.WeakRef.sq_rpow_le_psi2 hd hs0 hsd hN1R
    rw [mul_pow]
    have h2 : 0 ≤ (1 + 2 * E' * Ca) ^ 2 := sq_nonneg _
    calc Nr * ((1 + 2 * E' * Ca) ^ 2 * (Nr ^ (σ / d - 1)) ^ 2)
        = (1 + 2 * E' * Ca) ^ 2 * (Nr * (Nr ^ (σ / d - 1)) ^ 2) := by ring
      _ ≤ (1 + 2 * E' * Ca) ^ 2 * HRS.WeakRef.psi2 d s Nr :=
          mul_le_mul_of_nonneg_left this h2
  have hQb0 : 0 ≤ Cb * HRS.WeakRef.psi2 d s L :=
    mul_nonneg hCb (by linarith [HRS.WeakRef.psi2_ge_one hd hs0 hL1])
  have := HRS.WeakRef.var_alg (Nr := Nr) (m := (n : ℝ)) (D := D) (E := E') (a := a)
    (Qb := Cb * HRS.WeakRef.psi2 d s L)
    (Thb := (1 + 2 * E' * Ca) * Nr ^ (σ / d - 1)) (εf := Cm * deltaN d s (n + 1)) (Cb := Cb)
    (pL := HRS.WeakRef.psi2 d s L) (c₁ := (1 + 2 * E' * Ca) ^ 2)
    (pN := HRS.WeakRef.psi2 d s Nr) (Cm := Cm)
    (δ := deltaN d s (n + 1)) (by rw [hNr]; push_cast; ring) (Nat.cast_nonneg n) hD0 hDE hQb0
    le_rfl hCb hTh ha0 ha1 hδ0 hδ1 hNδ hpN rfl (sq_nonneg _) hCm
  exact this

set_option maxHeartbeats 1600000 in
/-- **Euclidean weak pressure upper bound** (whole-space port of `HRS.weak_pressure_upper_aux`).
Only `ρ ≤ M` is used.  `a₀ > 0` and `C` depend only on `(d, s, βm, βp, M, A)`. -/
theorem weak_pressure_upper_E (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (βm βp : ℝ) (hβm : 0 < βm) (M A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ q : Euc d → Euc d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) →
        (∀ x y, x ≠ y → q x y ≤ A * (1 + HRS.Whole.rieszWeight s (x - y))) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp,
        pairPartitionE q N β (HRS.Whole.withDensityReal ρ) ≤
          ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  obtain ⟨a₀', Cm, ha₀', hmarg⟩ := weak_marginal_strong_E hd s hs0 hsd βm βp hβm M A
  obtain ⟨Ca, Cb, hCa, hCb, hrows⟩ := wr3_row_bounds_real_integral hd hs0 hsd A M
  set P : ℝ := max βp 0 + 1 with hP
  have hP1 : 1 ≤ P := by have := le_max_right βp 0; linarith
  have hP0 : 0 < P := by linarith
  set E' : ℝ := Real.exp (2 * P) with hE
  have hE1 : 1 ≤ E' := Real.one_le_exp (by linarith)
  have hE0 : 0 < E' := by linarith
  obtain ⟨Cw, hCw0, hWex⟩ := HRS.WeakRef.exists_W hd hs0 hsd hP1 hβm
  set Cm' : ℝ := |Cm| with hCm'
  have hCm0 : 0 ≤ Cm' := abs_nonneg _
  set A₁ : ℝ := 8 * E' * Cb with hA₁
  set A₂ : ℝ := 12 * (1 + 2 * E' * Ca) ^ 2 + 12 + 12 * E' * Cm' ^ 2 with hA₂
  have hA₁0 : 0 ≤ A₁ := by positivity
  have hA₂0 : 0 ≤ A₂ := by positivity
  refine ⟨min a₀' (min 1 (1 / (16 * E' * P))), P * (1 / 2 + A₁ * Cw + A₂ * P),
    lt_min ha₀' (lt_min one_pos (by positivity)), ?_⟩
  intro ρ hρ hM q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ
  haveI hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ : Measure (Euc d) := HRS.Whole.withDensityReal ρ with hμ
  have hK : EWeakKernel μ a q := ⟨hqm, hqs, hq0, hrow⟩
  have hrowsx := fun x => hrows ρ hρ hM q hqm hq0 hqA x
  have ha₁ : a < a₀' := lt_of_lt_of_le ha (min_le_left _ _)
  have ha1 : a < 1 := lt_of_lt_of_le ha ((min_le_right _ _).trans (min_le_left _ _))
  have haE : a < 1 / (16 * E' * P) :=
    lt_of_lt_of_le ha ((min_le_right _ _).trans (min_le_right _ _))
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hβP : β ≤ P := by have := hβ.2; have := le_max_left βp 0; linarith
  have hN1 : 1 ≤ N := by omega
  obtain ⟨W₁, hW₁d, hW₁c, hW₁0, hW₁b⟩ := hWex N hN1
  have hpsiN := HRS.WeakRef.psi2_ge_one hd hs0 (show (1 : ℝ) ≤ N by exact_mod_cast hN1)
  have hNδ := HRS.WeakRef.mul_deltaN_eq_psi2 (d := d) s hN1
  set V : ℝ → ℝ := fun t => A₁ * HRS.WeakRef.psi2 d s (2 * N * P / t)
    + A₂ * HRS.WeakRef.psi2 d s N with hVdef
  set W : ℝ → ℝ := fun t => A₁ * W₁ t + A₂ * HRS.WeakRef.psi2 d s N * t with hWdef
  have hup := hK.pairPartition_upper_E ha0 (show 0 < N by omega) hβ0 (V := V) (W := W)
    ?_ ?_ ?_ ?_ ?_
  · refine hup.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have hWβ : W β ≤ (A₁ * Cw + A₂ * P) * HRS.WeakRef.psi2 d s N := by
      have h1 := hW₁b β hβ.1 hβP
      have h2 : A₂ * HRS.WeakRef.psi2 d s N * β ≤ A₂ * P * HRS.WeakRef.psi2 d s N := by
        have : 0 ≤ A₂ * HRS.WeakRef.psi2 d s N := by positivity
        nlinarith
      simp only [hWdef]
      nlinarith [mul_le_mul_of_nonneg_left h1 hA₁0]
    have hS0 : 0 ≤ (1 / 2 + A₁ * Cw + A₂ * P) * HRS.WeakRef.psi2 d s N := by
      have : 0 ≤ 1 / 2 + A₁ * Cw + A₂ * P := by positivity
      exact mul_nonneg this (by linarith)
    have hx : a / 2 + W β ≤ (1 / 2 + A₁ * Cw + A₂ * P) * HRS.WeakRef.psi2 d s N := by nlinarith
    calc β * (a / 2 + W β) ≤ β * ((1 / 2 + A₁ * Cw + A₂ * P) * HRS.WeakRef.psi2 d s N) :=
          mul_le_mul_of_nonneg_left hx hβ0.le
      _ ≤ P * ((1 / 2 + A₁ * Cw + A₂ * P) * HRS.WeakRef.psi2 d s N) :=
          mul_le_mul_of_nonneg_right hβP hS0
      _ = P * (1 / 2 + A₁ * Cw + A₂ * P) * ((N : ℝ) * deltaN d s N) := by rw [hNδ]; ring
      _ = _ := by ring
  · intro t ht
    have htβ : t ≤ β := ht.2
    have htP : t ≤ P := htβ.trans hβP
    have hτ : t / β ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1.le hβ0.le, (div_le_one hβ0).2 htβ⟩
    obtain ⟨f, hf1, hf2, -, -, hf4⟩ :=
      hmarg ρ hρ hM q hqm hqs hq0 hqA a ha0 ha₁ hrow N hN β hβ (t / β) hτ
    rw [div_mul_cancel₀ _ hβ0.ne'] at hf1
    have hta : t * a ≤ 1 / (16 * E') := by
      have h1 : t * a ≤ P * a := mul_le_mul_of_nonneg_right htP ha0
      have h2 : P * a ≤ P * (1 / (16 * E' * P)) := mul_le_mul_of_nonneg_left haE.le hP0.le
      have h3 : P * (1 / (16 * E' * P)) = 1 / (16 * E') := by field_simp
      linarith
    have hf5 : ∫ x, ((f x).toReal - 1) ^ 2 ∂μ ≤ (Cm' * deltaN d s N) ^ 2 := by
      refine hf4.trans (le_of_eq ?_)
      rw [hCm', mul_pow, mul_pow, sq_abs]
    exact wr5_variance_at_E hd hs0 hsd hK ha0 ha1.le hCa hCb hCm0 hP1 hE
      (fun x L hL => ((hrowsx x).1 L hL).2) (fun x L hL => ((hrowsx x).2 L hL).2)
      hN ht.1 htP hta ⟨f, hf1, hf2, hf5⟩
  · intro t ht
    have htP : t ≤ P := ht.2.trans hβP
    have hL : (1 : ℝ) ≤ 2 * N * P / t := by
      rw [le_div_iff₀ ht.1]
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      nlinarith
    have := HRS.WeakRef.psi2_ge_one hd hs0 hL
    exact add_nonneg (mul_nonneg hA₁0 (by linarith)) (mul_nonneg hA₂0 (by linarith))
  · intro t ht
    have h := ((hW₁d t ht).const_mul A₁).add
      ((hasDerivAt_id t).const_mul (A₂ * HRS.WeakRef.psi2 d s N))
    exact h.congr_deriv (by simp [hVdef])
  · exact (hW₁c.const_mul A₁).add ((continuous_const.mul continuous_id).continuousWithinAt)
  · simp [hWdef, hW₁0]

/-- The weak pressure bound for the frozen Bochner normaliser `HRS.Whole.pairNormalizer`:
`GibbsWellDefined`, `1 ≤ K ≤ e^{C N δ_N}`, and `0 ≤ log K ≤ C N δ_N` (the logarithm is not a junk value
since `K ≥ 1`). -/
theorem weak_pressure_upper_pairNormalizer_E (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (βm βp : ℝ) (hβm : 0 < βm) (M A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ q : Euc d → Euc d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) →
        (∀ x y, x ≠ y → q x y ≤ A * (1 + HRS.Whole.rieszWeight s (x - y))) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp,
        HRS.Whole.GibbsWellDefined q N β (HRS.Whole.withDensityReal ρ) ∧
        1 ≤ HRS.Whole.pairNormalizer q N β (HRS.Whole.withDensityReal ρ) ∧
        HRS.Whole.pairNormalizer q N β (HRS.Whole.withDensityReal ρ)
          ≤ Real.exp (C * N * deltaN d s N) ∧
        0 ≤ Real.log (HRS.Whole.pairNormalizer q N β (HRS.Whole.withDensityReal ρ)) ∧
        Real.log (HRS.Whole.pairNormalizer q N β (HRS.Whole.withDensityReal ρ))
          ≤ C * N * deltaN d s N := by
  obtain ⟨a₀, C, ha₀, H⟩ := weak_pressure_upper_E hd s hs0 hsd βm βp hβm M A
  refine ⟨a₀, C, ha₀, ?_⟩
  intro ρ hρ hM q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ
  haveI hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hK : EWeakKernel (HRS.Whole.withDensityReal ρ) a q := ⟨hqm, hqs, hq0, hrow⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  obtain ⟨hW, h1⟩ := hK.gibbsWellDefined_E ha0 hβ0.le (show 0 < N by omega)
  have hup := H ρ hρ hM q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ
  have heq := (pairNormalizer_eq_toReal_pairPartitionE hW).1
  have hZ : HRS.Whole.pairNormalizer q N β (HRS.Whole.withDensityReal ρ)
      ≤ Real.exp (C * N * deltaN d s N) := by
    rw [heq]
    exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hup
  have hpos : 0 < HRS.Whole.pairNormalizer q N β (HRS.Whole.withDensityReal ρ) := by linarith
  refine ⟨hW, h1, hZ, Real.log_nonneg h1, ?_⟩
  exact (Real.log_le_iff_le_exp hpos).2 hZ

/-- Non-vacuity: for the zero kernel the partition function is `1`, so the bound
`weak_pressure_upper_E` is a statement about an actual quantity (`1 ≤ e^{C N δ_N}` for `C ≥ 0`). -/
theorem wr5_pairPartitionE_zero (μ : Measure E) [IsProbabilityMeasure μ] (N : ℕ) (β : ℝ) :
    pairPartitionE (fun _ _ : E => (0 : ℝ)) N β μ = 1 := by
  unfold pairPartitionE pairWeightE modEnergyE
  simp

end HRS.MS.Wr
