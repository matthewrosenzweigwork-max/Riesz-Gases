import HRS.MC.S7FCDefs
import HRS.PDE.MovFinalConsumers
import HRS.Sections.AllTimeAux2
import HRS.MC.SEdgeB4c
import HRS.Equilibrium.Q32cAux2

/-!
# FC-F1 (linear moments of the particle fluctuation), packet `S7FCW3`

Proves `s7_FC_F1_linear` (copied verbatim into `S7FCPlan.lean` by the Tie file). Route: item 1 of `alltime_Lp`
(density of the law of `X_t` in `L^p` w.r.t. the Gibbs law `Q_t`), item 2 with exponent `2` (density of `Q_t` in `L^2`
w.r.t. the product law `μ_t^{⊗N}`), Hölder twice, and the uniform (in `μ`) sixth-power style moment bound of
`sed_B4c` (the constant of `b4c_main` is made explicit, see `s7fcw3_b4c_unif`).  Scaling `a = M·b`, `|b| ≤ 1`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCW3

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec

variable {d : ℕ}

theorem s7fcw3_b4c_unif (d : ℕ) (M : ℝ) (m : ℕ) :
    ∃ C : ℝ, ∀ (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (u : Torus d → ℝ), Measurable u →
      (∀ x, |u x| ≤ M) → ∀ N : ℕ, 1 ≤ N →
      ∫ X : Config d N, (pair (empirical X) u - pair μ u) ^ (2 * m)
        ∂(Measure.pi fun _ : Fin N => μ) ≤ C / (N : ℝ) ^ m := by
  set κ : ℝ≥0 := (‖M - -M‖₊ / 2) ^ 2 with hκ
  refine ⟨2 * ((2 * m).factorial : ℝ) * Real.exp ((κ : ℝ) / 2), ?_⟩
  intro μ _ u hum hb N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set ν : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hν
  -- sub-Gaussian coordinates
  have h1 : HasSubgaussianMGF (fun x => u x - μ[u]) κ μ :=
    hasSubgaussianMGF_of_mem_Icc (a := -M) (b := M) hum.aemeasurable
      (ae_of_all _ fun x => abs_le.1 (hb x))
  have h2 : ∀ i : Fin N, HasSubgaussianMGF (fun ω : Config d N => u (ω i) - μ[u]) κ ν := by
    intro i
    have hY : AEMeasurable (fun ω : Config d N => ω i) ν := (measurable_pi_apply i).aemeasurable
    have := HasSubgaussianMGF.of_map (μ := ν) hY
      (by rwa [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq] : HasSubgaussianMGF
        (fun x => u x - μ[u]) κ (ν.map fun ω : Config d N => ω i))
    exact this
  have hind : iIndepFun (fun (i : Fin N) (ω : Config d N) => u (ω i) - μ[u]) ν :=
    iIndepFun_pi (X := fun _ : Fin N => fun x : Torus d => u x - μ[u]) (μ := fun _ => μ)
      (fun _ => (hum.sub_const _).aemeasurable)
  have h3 := HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ) (fun i _ => h2 i)
  set Z : Config d N → ℝ := fun ω => ∑ i, (u (ω i) - μ[u]) with hZ
  have hZmeas : Measurable Z := by
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (hum.comp (measurable_pi_apply i)).sub_const _
  have hcoe : ((∑ _i : Fin N, κ : ℝ≥0) : ℝ) = N * κ := by simp
  -- the quantity
  have hq : ∀ X : Config d N, pair (empirical X) u - pair μ u = Z X / N := by
    intro X
    rw [HRS.MC.SEdge.B4c.b4c_pair_empirical X hum]
    simp only [hZ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, pair]
    field_simp
  simp_rw [hq]
  -- the pointwise bound
  set s : ℝ := 1 / Real.sqrt N with hs
  have hs2 : s ^ 2 = 1 / N := by
    rw [hs, div_pow, Real.sq_sqrt hNpos.le]; ring
  have hpt : ∀ ω, (N : ℝ) ^ m * (Z ω / N) ^ (2 * m) ≤
      ((2 * m).factorial : ℝ) * (Real.exp (s * Z ω) + Real.exp (-s * Z ω)) := by
    intro ω
    have := HRS.MC.SEdge.B4c.b4c_pow_le m (s * Z ω)
    have heq : (s * Z ω) ^ (2 * m) = (N : ℝ) ^ m * (Z ω / N) ^ (2 * m) := by
      calc (s * Z ω) ^ (2 * m) = ((s * Z ω) ^ 2) ^ m := pow_mul _ _ _
        _ = ((N : ℝ) * (Z ω / N) ^ 2) ^ m := by
          congr 1
          rw [mul_pow, hs2]
          field_simp
        _ = (N : ℝ) ^ m * ((Z ω / N) ^ 2) ^ m := mul_pow _ _ _
        _ = (N : ℝ) ^ m * (Z ω / N) ^ (2 * m) := by rw [pow_mul]
    rw [heq] at this
    simpa [neg_mul] using this
  have hint1 : Integrable (fun ω => Real.exp (s * Z ω)) ν := h3.integrable_exp_mul s
  have hint2 : Integrable (fun ω => Real.exp (-s * Z ω)) ν := h3.integrable_exp_mul (-s)
  have hg : Integrable (fun ω => ((2 * m).factorial : ℝ) *
      (Real.exp (s * Z ω) + Real.exp (-s * Z ω))) ν := (hint1.add hint2).const_mul _
  have hfmeas : Measurable fun ω => (N : ℝ) ^ m * (Z ω / N) ^ (2 * m) :=
    measurable_const.mul ((hZmeas.div_const _).pow_const _)
  have hfnn : ∀ ω, 0 ≤ (N : ℝ) ^ m * (Z ω / N) ^ (2 * m) := fun ω => by
    have : 0 ≤ (Z ω / N) ^ (2 * m) := by rw [pow_mul]; positivity
    positivity
  have hf : Integrable (fun ω => (N : ℝ) ^ m * (Z ω / N) ^ (2 * m)) ν :=
    hg.mono' hfmeas.aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (hfnn ω)]; exact hpt ω)
  have hmono := integral_mono hf hg hpt
  rw [integral_const_mul, integral_const_mul, integral_add hint1 hint2] at hmono
  have hm1 : ∫ ω, Real.exp (s * Z ω) ∂ν ≤ Real.exp ((κ : ℝ) / 2) := by
    have := h3.mgf_le s
    unfold mgf at this
    refine this.trans (le_of_eq ?_)
    rw [hcoe, hs2]; congr 1; field_simp
  have hm2 : ∫ ω, Real.exp (-s * Z ω) ∂ν ≤ Real.exp ((κ : ℝ) / 2) := by
    have := h3.mgf_le (-s)
    unfold mgf at this
    refine this.trans (le_of_eq ?_)
    rw [hcoe, neg_sq, hs2]; congr 1; field_simp
  have hfac : (0 : ℝ) < ((2 * m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hNm : (0 : ℝ) < (N : ℝ) ^ m := by positivity
  rw [le_div_iff₀ hNm, mul_comm]
  calc (N : ℝ) ^ m * ∫ ω, (Z ω / N) ^ (2 * m) ∂ν
      ≤ ((2 * m).factorial : ℝ) * (∫ ω, Real.exp (s * Z ω) ∂ν + ∫ ω, Real.exp (-s * Z ω) ∂ν) := by
        exact hmono
    _ ≤ ((2 * m).factorial : ℝ) * (Real.exp ((κ : ℝ) / 2) + Real.exp ((κ : ℝ) / 2)) := by
        gcongr
    _ = 2 * ((2 * m).factorial : ℝ) * Real.exp ((κ : ℝ) / 2) := by ring


theorem s7fcw3_rpow_le {x : ℝ} (hx : 0 ≤ x) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) (hrn : r ≤ (n : ℝ)) :
    x ^ r ≤ 1 + x ^ n := by
  rcases le_total x 1 with h | h
  · have h1 : x ^ r ≤ 1 := Real.rpow_le_one hx h hr
    have h2 : 0 ≤ x ^ n := pow_nonneg hx n
    linarith
  · have h1 : x ^ r ≤ x ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le h hrn
    rw [Real.rpow_natCast] at h1
    linarith

theorem s7fcw3_pair_meas {N : ℕ} {b : Torus d → ℝ} (hb : Measurable b) :
    Measurable (fun Y : Config d N => pair (empirical Y) b) := by
  have h : (fun Y : Config d N => pair (empirical Y) b) = fun Y => (∑ i, b (Y i)) / (N : ℝ) := by
    funext Y
    exact HRS.MC.SEdge.B4c.b4c_pair_empirical Y hb
  rw [h]
  exact (Finset.measurable_sum _ fun i _ => hb.comp (measurable_pi_apply i)).div_const _

theorem s7fcw3_pair_emp_le_one {N : ℕ} (hN : 1 ≤ N) {b : Torus d → ℝ} (hb : Measurable b)
    (hb1 : ∀ x, |b x| ≤ 1) (Y : Config d N) : |pair (empirical Y) b| ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [HRS.MC.SEdge.B4c.b4c_pair_empirical Y hb, abs_div, abs_of_pos hNpos, div_le_one hNpos]
  calc |∑ i, b (Y i)| ≤ ∑ i, |b (Y i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => hb1 _
    _ = N := by simp

theorem s7fcw3_pair_prob_le_one (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {b : Torus d → ℝ}
    (hb1 : ∀ x, |b x| ≤ 1) : |pair μ b| ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := b) (C := 1)
    (ae_of_all _ fun x => by simpa using hb1 x)
  simpa [pair, Real.norm_eq_abs] using h

theorem s7fcw3_mom (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {b : Torus d → ℝ}
    (hb : Measurable b) (hb1 : ∀ x, |b x| ≤ 1) (m : ℕ) (C : ℝ)
    (hC : ∀ N : ℕ, 1 ≤ N → ∫ X : Config d N, (pair (empirical X) b - pair μ b) ^ (2 * m)
        ∂(Measure.pi fun _ : Fin N => μ) ≤ C / (N : ℝ) ^ m)
    (N : ℕ) (hN : 1 ≤ N) :
    ∫⁻ X : Config d N, ENNReal.ofReal (|Real.sqrt N * (pair (empirical X) b - pair μ b)| ^ (2 * m))
      ∂(Measure.pi fun _ : Fin N => μ) ≤ ENNReal.ofReal C := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNm : (0 : ℝ) < (N : ℝ) ^ m := pow_pos hNpos m
  have hev : Even (2 * m) := even_two_mul m
  have hYm : Measurable (fun X : Config d N => pair (empirical X) b - pair μ b) :=
    (s7fcw3_pair_meas hb).sub measurable_const
  have hYb : ∀ X : Config d N, |pair (empirical X) b - pair μ b| ≤ 2 := fun X => by
    have h1 := s7fcw3_pair_emp_le_one hN hb hb1 X
    have h2 := s7fcw3_pair_prob_le_one μ hb1
    have h3 := abs_sub (pair (empirical X) b) (pair μ b)
    linarith
  have hbd : ∀ X : Config d N, ‖(pair (empirical X) b - pair μ b) ^ (2 * m)‖ ≤ 2 ^ (2 * m) := by
    intro X
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hYb X) _
  have hint : Integrable (fun X : Config d N => (pair (empirical X) b - pair μ b) ^ (2 * m))
      (Measure.pi fun _ : Fin N => μ) :=
    Integrable.of_bound (hYm.pow_const _).aestronglyMeasurable _ (ae_of_all _ hbd)
  have hnn : 0 ≤ᵐ[Measure.pi fun _ : Fin N => μ]
      (fun X : Config d N => (N : ℝ) ^ m * (pair (empirical X) b - pair μ b) ^ (2 * m)) :=
    ae_of_all _ fun X => mul_nonneg hNm.le (hev.pow_nonneg _)
  have hs : (Real.sqrt N) ^ (2 * m) = (N : ℝ) ^ m := by
    rw [pow_mul, Real.sq_sqrt hNpos.le]
  have hpt : ∀ X : Config d N, |Real.sqrt N * (pair (empirical X) b - pair μ b)| ^ (2 * m)
      = (N : ℝ) ^ m * (pair (empirical X) b - pair μ b) ^ (2 * m) := fun X => by
    rw [hev.pow_abs, mul_pow, hs]
  calc ∫⁻ X : Config d N, ENNReal.ofReal (|Real.sqrt N * (pair (empirical X) b - pair μ b)| ^ (2 * m))
        ∂(Measure.pi fun _ : Fin N => μ)
      = ∫⁻ X : Config d N, ENNReal.ofReal ((N : ℝ) ^ m * (pair (empirical X) b - pair μ b) ^ (2 * m))
        ∂(Measure.pi fun _ : Fin N => μ) := by
        congr 1
        funext X
        rw [hpt X]
    _ = ENNReal.ofReal (∫ X : Config d N, (N : ℝ) ^ m * (pair (empirical X) b - pair μ b) ^ (2 * m)
        ∂(Measure.pi fun _ : Fin N => μ)) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) hnn).symm
    _ ≤ ENNReal.ofReal C := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_const_mul]
        calc (N : ℝ) ^ m * ∫ X : Config d N, (pair (empirical X) b - pair μ b) ^ (2 * m)
              ∂(Measure.pi fun _ : Fin N => μ)
            ≤ (N : ℝ) ^ m * (C / (N : ℝ) ^ m) := mul_le_mul_of_nonneg_left (hC N hN) hNm.le
          _ = C := by field_simp

/-- Abstract Hölder chain: `∫ G dLaw ≤ A · (B · K^{1/2})^{1/p'}`. -/
theorem s7fcw3_chain {Y : Type*} [MeasurableSpace Y] (Law Q PP : Measure Y)
    [Measure.HaveLebesgueDecomposition Law Q] [Measure.HaveLebesgueDecomposition Q PP]
    {p p' : ℝ} (hpq : p.HolderConjugate p') (hLQ : Law ≪ Q) (hQPP : Q ≪ PP)
    {A B K : ℝ≥0∞} (hA : (∫⁻ y, Law.rnDeriv Q y ^ p ∂Q) ^ (1 / p) ≤ A)
    (hB : (∫⁻ y, Q.rnDeriv PP y ^ (2 : ℝ) ∂PP) ^ (1 / (2 : ℝ)) ≤ B)
    (G : Y → ℝ≥0∞) (hG : Measurable G) (hK : ∫⁻ y, (G y ^ p') ^ (2 : ℝ) ∂PP ≤ K) :
    ∫⁻ y, G y ∂Law ≤ A * (B * K ^ (1 / (2 : ℝ))) ^ (1 / p') := by
  have hm1 : Measurable (Law.rnDeriv Q) := Measure.measurable_rnDeriv _ _
  have hm2 : Measurable (Q.rnDeriv PP) := Measure.measurable_rnDeriv _ _
  have hGp : Measurable fun y => G y ^ p' := hG.pow_const _
  have hp'0 : 0 ≤ p' := hpq.symm.nonneg
  have hcs : ∫⁻ y, G y ^ p' ∂Q ≤ B * K ^ (1 / (2 : ℝ)) := by
    rw [← lintegral_rnDeriv_mul hQPP hGp.aemeasurable]
    refine (ENNReal.lintegral_mul_le_Lp_mul_Lq PP Real.HolderConjugate.two_two
      hm2.aemeasurable hGp.aemeasurable).trans ?_
    exact mul_le_mul' hB (ENNReal.rpow_le_rpow hK (by norm_num))
  calc ∫⁻ y, G y ∂Law = ∫⁻ y, Law.rnDeriv Q y * G y ∂Q :=
        (lintegral_rnDeriv_mul hLQ hG.aemeasurable).symm
    _ ≤ (∫⁻ y, Law.rnDeriv Q y ^ p ∂Q) ^ (1 / p) * (∫⁻ y, G y ^ p' ∂Q) ^ (1 / p') :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq Q hpq hm1.aemeasurable hG.aemeasurable
    _ ≤ A * (B * K ^ (1 / (2 : ℝ))) ^ (1 / p') :=
        mul_le_mul' hA (ENNReal.rpow_le_rpow hcs (by positivity))

theorem s7fcw3_pt {x q s : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q) (hs : 0 ≤ s) (n : ℕ) (hn : q * s ≤ (n : ℝ)) :
    (ENNReal.ofReal (x ^ q) ^ s) ^ (2 : ℝ) ≤ ENNReal.ofReal (1 + x ^ (2 * n)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hx _) hs,
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hx _) _) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.rpow_mul hx, ← Real.rpow_mul hx]
  apply s7fcw3_rpow_le hx (by positivity) (2 * n)
  push_cast
  nlinarith

theorem s7fcw3_core (R : Regime d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → Config d N)
        (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        PreparedRealization R.D P (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
          X₀ W X →
        ∀ t : ℝ, 0 ≤ t → ∀ b : Torus d → ℝ, Measurable b → (∀ x, |b x| ≤ 1) →
          Integrable (fun ω => |Real.sqrt N * (pair (empirical (X t.toNNReal ω)) b -
            pair (withDensityReal (R.ρ t)) b)| ^ q) P ∧
          ∫ ω, |Real.sqrt N * (pair (empirical (X t.toNNReal ω)) b -
            pair (withDensityReal (R.ρ t)) b)| ^ q ∂P ≤ C0 := by
  obtain ⟨p, hp1, C1, hC1⟩ := movfin_alltime_item1 R
  obtain ⟨C2, hC2⟩ := alltime_item2 R 2 (by norm_num)
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp1
  have hp'0 : 0 ≤ p.conjExponent := hpq.symm.nonneg
  have hp0 : 0 < p := by linarith
  obtain ⟨Cm, hCm⟩ := s7fcw3_b4c_unif d 1 ⌈q * p.conjExponent⌉₊
  refine ⟨max C1 0 * (max C2 0 * (1 + max Cm 0) ^ (1 / (2 : ℝ))) ^ (1 / p.conjExponent), ?_, ?_⟩
  · apply mul_nonneg (le_max_right _ _)
    apply Real.rpow_nonneg
    apply mul_nonneg (le_max_right _ _)
    apply Real.rpow_nonneg
    linarith [le_max_right Cm 0]
  intro N hN Ω _ P _ X₀ W X hprep t ht b hb hb1
  have hN1 : 1 ≤ N := by omega
  have hρ : IsProbDensity (R.ρ t) := (alltime_traj R t).mf.density t ⟨ht, le_rfl⟩
  haveI : IsProbabilityMeasure (withDensityReal (R.ρ t)) := isProb_withDensityReal hρ
  obtain ⟨m₀, M₀, hm₀, hbdR⟩ := R.bounds
  haveI : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d R.D.s) N R.β
      (withDensityReal (R.ρ t))) :=
    HRS.Q32c.q32c_Q_isProb (d := d) (by have := R.hd; omega) (alltime_hs0 R) (alltime_hsd R) R.hβ
      (Λ := max 1 M₀) (le_max_left _ _) hρ (fun x => (hbdR t ht x).2.trans (le_max_right _ _))
      (by omega)
  obtain ⟨hac, hdens⟩ := hC1 N hN P X₀ W X hprep t ht
  obtain ⟨hQPP, hdensQ⟩ := hC2 N hN t ht
  have hXm : Measurable (X t.toNNReal) := (hprep.solution t).adapted t.toNNReal
  have hFm : Measurable (fun Y : Config d N => |Real.sqrt N * (pair (empirical Y) b -
      pair (withDensityReal (R.ρ t)) b)| ^ q) :=
    ((continuous_abs.measurable.comp (((s7fcw3_pair_meas hb).sub measurable_const).const_mul
      (Real.sqrt N))).pow_const q)
  have hGm : Measurable (fun Y : Config d N => ENNReal.ofReal (|Real.sqrt N * (pair (empirical Y) b -
      pair (withDensityReal (R.ρ t)) b)| ^ q)) := hFm.ennreal_ofReal
  -- the lintegral over the law
  have hLaw : ∫⁻ ω, ENNReal.ofReal (|Real.sqrt N * (pair (empirical (X t.toNNReal ω)) b -
      pair (withDensityReal (R.ρ t)) b)| ^ q) ∂P
      = ∫⁻ Y, ENNReal.ofReal (|Real.sqrt N * (pair (empirical Y) b -
      pair (withDensityReal (R.ρ t)) b)| ^ q) ∂(Measure.map (X t.toNNReal) P) :=
    (lintegral_map hGm hXm).symm
  -- density bound
  have hA : (∫⁻ y, (Measure.map (X t.toNNReal) P).rnDeriv
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))) y ^ p
      ∂(modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t)))) ^ (1 / p)
      ≤ ENNReal.ofReal (max C1 0) := by
    have h := hdens
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne'
      ENNReal.ofReal_ne_top (Measure.measurable_rnDeriv _ _).aestronglyMeasurable] at h
    simp only [ENNReal.toReal_ofReal hp0.le, enorm_eq_self] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hB : (∫⁻ y, (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))).rnDeriv
      (Measure.pi fun _ : Fin N => withDensityReal (R.ρ t)) y ^ (2 : ℝ)
      ∂(Measure.pi fun _ : Fin N => withDensityReal (R.ρ t))) ^ (1 / (2 : ℝ))
      ≤ ENNReal.ofReal (max C2 0) := by
    have h := hdensQ
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 (by norm_num)).ne'
      ENNReal.ofReal_ne_top (Measure.measurable_rnDeriv _ _).aestronglyMeasurable] at h
    simp only [ENNReal.toReal_ofReal (show (0:ℝ) ≤ 2 by norm_num), enorm_eq_self] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- second moment of the density powers
  have hK : ∫⁻ y, (ENNReal.ofReal (|Real.sqrt N * (pair (empirical y) b -
      pair (withDensityReal (R.ρ t)) b)| ^ q) ^ p.conjExponent) ^ (2 : ℝ)
      ∂(Measure.pi fun _ : Fin N => withDensityReal (R.ρ t))
      ≤ ENNReal.ofReal (1 + max Cm 0) := by
    have hpt : ∀ y : Config d N,
        (ENNReal.ofReal (|Real.sqrt N * (pair (empirical y) b -
          pair (withDensityReal (R.ρ t)) b)| ^ q) ^ p.conjExponent) ^ (2 : ℝ)
        ≤ ENNReal.ofReal (1 + |Real.sqrt N * (pair (empirical y) b -
          pair (withDensityReal (R.ρ t)) b)| ^ (2 * ⌈q * p.conjExponent⌉₊)) := fun y =>
      s7fcw3_pt (abs_nonneg _) (by linarith) hp'0 _ (Nat.le_ceil _)
    have hmom := s7fcw3_mom (withDensityReal (R.ρ t)) hb hb1 ⌈q * p.conjExponent⌉₊ Cm
      (fun N' hN' => hCm _ b hb hb1 N' hN') N hN1
    have hpt' : ∀ y : Config d N,
        (ENNReal.ofReal (|Real.sqrt N * (pair (empirical y) b -
          pair (withDensityReal (R.ρ t)) b)| ^ q) ^ p.conjExponent) ^ (2 : ℝ)
        ≤ 1 + ENNReal.ofReal (|Real.sqrt N * (pair (empirical y) b -
          pair (withDensityReal (R.ρ t)) b)| ^ (2 * ⌈q * p.conjExponent⌉₊)) := fun y =>
      (hpt y).trans (ENNReal.ofReal_add_le.trans (by rw [ENNReal.ofReal_one]))
    have hI := lintegral_mono (μ := Measure.pi fun _ : Fin N => withDensityReal (R.ρ t)) hpt'
    have h1 : ∫⁻ _y : Config d N, (1 : ℝ≥0∞) ∂(Measure.pi fun _ : Fin N => withDensityReal (R.ρ t)) = 1 := by
      simp
    rw [lintegral_add_left measurable_const, h1] at hI
    refine hI.trans ?_
    rw [ENNReal.ofReal_add zero_le_one (le_max_right _ _), ENNReal.ofReal_one]
    exact add_le_add le_rfl (hmom.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hfin : ∫⁻ Y, ENNReal.ofReal (|Real.sqrt N * (pair (empirical Y) b -
      pair (withDensityReal (R.ρ t)) b)| ^ q) ∂(Measure.map (X t.toNNReal) P)
      ≤ ENNReal.ofReal (max C1 0 * (max C2 0 * (1 + max Cm 0) ^ (1 / (2 : ℝ))) ^ (1 / p.conjExponent)) := by
    refine (s7fcw3_chain (Measure.map (X t.toNNReal) P)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t)))
      (Measure.pi fun _ : Fin N => withDensityReal (R.ρ t)) (p := p) (p' := p.conjExponent) hpq hac hQPP
      hA hB _ hGm hK).trans (le_of_eq ?_)
    have ha : 0 ≤ max C1 0 := le_max_right _ _
    have hb' : 0 ≤ max C2 0 := le_max_right _ _
    have hk : 0 ≤ 1 + max Cm 0 := by linarith [le_max_right Cm 0]
    have hZ : 0 ≤ max C2 0 * (1 + max Cm 0) ^ (1 / (2 : ℝ)) :=
      mul_nonneg hb' (Real.rpow_nonneg hk _)
    rw [ENNReal.ofReal_rpow_of_nonneg hk (by norm_num), ← ENNReal.ofReal_mul hb',
      ENNReal.ofReal_rpow_of_nonneg hZ (one_div_nonneg.2 hp'0), ← ENNReal.ofReal_mul ha]
  have hPfin : ∫⁻ ω, ENNReal.ofReal (|Real.sqrt N * (pair (empirical (X t.toNNReal ω)) b -
      pair (withDensityReal (R.ρ t)) b)| ^ q) ∂P
      ≤ ENNReal.ofReal (max C1 0 * (max C2 0 * (1 + max Cm 0) ^ (1 / (2 : ℝ))) ^ (1 / p.conjExponent)) := by
    rw [hLaw]; exact hfin
  have hnn : 0 ≤ᵐ[P] (fun ω => |Real.sqrt N * (pair (empirical (X t.toNNReal ω)) b -
      pair (withDensityReal (R.ρ t)) b)| ^ q) :=
    ae_of_all _ fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hmeasω : AEStronglyMeasurable (fun ω => |Real.sqrt N * (pair (empirical (X t.toNNReal ω)) b -
      pair (withDensityReal (R.ρ t)) b)| ^ q) P :=
    (hFm.comp hXm).aestronglyMeasurable
  refine ⟨⟨hmeasω, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hPfin ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmeasω]
    exact ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (mul_nonneg (le_max_right _ _)
        (Real.rpow_nonneg (by linarith [le_max_right Cm 0]) _)) _)) hPfin

theorem s7_FC_F1_linear_proof (R : Regime d) (q M : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        PreparedRealization R.D P (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
          X₀ W X →
        ∀ t : ℝ, 0 ≤ t → ∀ a : Torus d → ℝ, Measurable a → (∀ x, |a x| ≤ M) →
          Integrable (fun ω => |Real.sqrt N * (pair (empirical (X t.toNNReal ω)) a -
            pair (withDensityReal (R.ρ t)) a)| ^ q) P ∧
          ∫ ω, |Real.sqrt N * (pair (empirical (X t.toNNReal ω)) a -
            pair (withDensityReal (R.ρ t)) a)| ^ q ∂P ≤ C * M ^ q
  := by
  obtain ⟨C0, hC0, hcore⟩ := s7fcw3_core R q hq
  refine ⟨C0, ?_⟩
  intro N hN Ω _ P _ X₀ W X hprep t ht a ha hM
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hq0 : 0 < q := by linarith
  rcases hM0.eq_or_lt with hM0 | hMpos
  · subst hM0
    have ha0 : a = fun _ => 0 := funext fun x => abs_nonpos_iff.1 (hM x)
    subst ha0
    simp [HRS.pair, Real.zero_rpow hq0.ne']
  · have hb : Measurable (fun x => a x / M) := ha.div_const M
    have hb1 : ∀ x, |a x / M| ≤ 1 := fun x => by
      rw [abs_div, abs_of_pos hMpos, div_le_one hMpos]; exact hM x
    obtain ⟨hint, hbound⟩ := hcore N hN P X₀ W X hprep t ht (fun x => a x / M) hb hb1
    have hlin : ∀ μ' : Measure (Torus d), pair μ' a = M * pair μ' (fun x => a x / M) := by
      intro μ'
      unfold HRS.pair
      rw [← integral_const_mul]
      congr 1
      funext x
      field_simp
    have key : (fun ω => |Real.sqrt N * (pair (empirical (X t.toNNReal ω)) a -
        pair (withDensityReal (R.ρ t)) a)| ^ q) = fun ω => M ^ q *
        |Real.sqrt N * (pair (empirical (X t.toNNReal ω)) (fun x => a x / M) -
        pair (withDensityReal (R.ρ t)) (fun x => a x / M))| ^ q := by
      funext ω
      rw [hlin (empirical (X t.toNNReal ω)), hlin (withDensityReal (R.ρ t)),
        show Real.sqrt N * (M * pair (empirical (X t.toNNReal ω)) (fun x => a x / M) -
          M * pair (withDensityReal (R.ρ t)) (fun x => a x / M)) =
          M * (Real.sqrt N * (pair (empirical (X t.toNNReal ω)) (fun x => a x / M) -
          pair (withDensityReal (R.ρ t)) (fun x => a x / M))) by ring,
        abs_mul, abs_of_pos hMpos, Real.mul_rpow hMpos.le (abs_nonneg _)]
    rw [key]
    refine ⟨hint.const_mul _, ?_⟩
    rw [integral_const_mul]
    calc M ^ q * ∫ ω, |Real.sqrt N * (pair (empirical (X t.toNNReal ω)) (fun x => a x / M) -
          pair (withDensityReal (R.ρ t)) (fun x => a x / M))| ^ q ∂P
        ≤ M ^ q * C0 := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hM0 _)
      _ = C0 * M ^ q := mul_comm _ _

end HRS.MC.Sec7.S7FCW3

end
