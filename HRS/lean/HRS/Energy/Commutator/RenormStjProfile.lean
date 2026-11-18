import HRS.Energy.Commutator.RenormFinal

/-!
# Route S, packet STJ (step S4, Stieltjes case): the Yukawa profile and its `l`-integrals

Generic slice infrastructure (`docs/external/super_core_proof.md` §2-3, §10):
* `cfl d l r = -Γ_l'(r) r^{d-1}` is the sphere coefficient of the smearing charge `σ_{l,η}`;
  it is decreasing in `r` (flux monotonicity), `≤ κ_d = 1/|S^{d-1}|`;
* `l Γ_l(η) (η/2)^d ≤ cfl(η/2)` (the ball coefficient is controlled by the sphere coefficient at half radius);
* `cfl(ρ) ≤ ρ^{d-1} (2/ρ) (Γ_l(ρ/2) - Γ_l(ρ))`, hence by the Euclidean Stieltjes identity
  `∫ l^{-β} cfl(ρ) dl ≤ C ρ^{d-2-s}` (L4);
* `∫ f_{l,η} ≤ min(η²/(2d), 1/l)`, hence `∫ l^{-β} ∫ f_{l,η} dl ≤ C η^{d-s}` (L3).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.Stj

variable {d : ℕ}

/-- the sphere coefficient `c_l(r) = -Γ_l'(r) r^{d-1}` of `σ_{l,η}` -/
def cfl (d : ℕ) (l r : ℝ) : ℝ := -(deriv (yukawa d l) r) * r ^ (d - 1)

theorem cfl_pos (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {r : ℝ} (hr : 0 < r) : 0 < cfl d l r :=
  mul_pos (neg_pos.mpr (SmearAux.deriv_yukawa_neg hd hl hr)) (pow_pos hr _)

theorem cfl_eq_kappa (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {r : ℝ} (hr : 0 < r) :
    cfl d l r = SmearAux.kappa d - SmearAux.Aint d l r := by
  have := SmearAux.qq_eq hd hl hr
  unfold cfl
  linarith

theorem cfl_le_kappa (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {r : ℝ} (hr : 0 < r) :
    cfl d l r ≤ SmearAux.kappa d := by
  rw [cfl_eq_kappa hd hl hr]
  linarith [SmearAux.Aint_nonneg hd hl r]

theorem cfl_antitone (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    cfl d l b ≤ cfl d l a := by
  rw [cfl_eq_kappa hd hl ha, cfl_eq_kappa hd hl (ha.trans_le hab)]
  linarith [SmearAux.Aint_mono hd hl ha (ha.trans_le hab) hab]

/-- `B_l = |S| c_l ≤ 1` -/
theorem sphere_coef_le (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Euc d)).toSphere.real univ * cfl d l r ≤ 1 := by
  have h := cfl_le_kappa hd hl hr
  have hS : 0 ≤ (volume : Measure (Euc d)).toSphere.real univ := measureReal_nonneg
  calc (volume : Measure (Euc d)).toSphere.real univ * cfl d l r
      ≤ (volume : Measure (Euc d)).toSphere.real univ * SmearAux.kappa d :=
        mul_le_mul_of_nonneg_left h hS
    _ = 1 := SmearAux.kappa_mul hd

theorem cfl_le_diff (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {ρ : ℝ} (hρ : 0 < ρ) :
    cfl d l ρ ≤ ρ ^ (d - 1) * (2 / ρ) * (yukawa d l (ρ / 2) - yukawa d l ρ) := by
  have hρ2 : 0 < ρ / 2 := half_pos hρ
  have hcont : ContinuousOn (yukawa d l) (Icc (ρ / 2) ρ) := fun x hx =>
    (SmearAux.hasDerivAt_yukawa hd hl (lt_of_lt_of_le hρ2 hx.1)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (yukawa d l) (Ioo (ρ / 2) ρ) := fun x hx =>
    (SmearAux.hasDerivAt_yukawa hd hl (lt_trans hρ2 hx.1)).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (yukawa d l) (half_lt_self hρ) hcont hdiff
  have hc0 : 0 < c := lt_trans hρ2 hc.1
  have h1 := cfl_antitone hd hl hc0 hc.2.le
  have e1 : ρ - ρ / 2 = ρ / 2 := by ring
  rw [e1] at hcd
  have hb : -(deriv (yukawa d l) c) = (2 / ρ) * (yukawa d l (ρ / 2) - yukawa d l ρ) := by
    rw [hcd]; field_simp; ring
  have hbpos : 0 < -(deriv (yukawa d l) c) := neg_pos.mpr (SmearAux.deriv_yukawa_neg hd hl hc0)
  calc cfl d l ρ ≤ cfl d l c := h1
    _ = (-(deriv (yukawa d l) c)) * c ^ (d - 1) := rfl
    _ ≤ (-(deriv (yukawa d l) c)) * ρ ^ (d - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0.le hc.2.le _) hbpos.le
    _ = ρ ^ (d - 1) * (2 / ρ) * (yukawa d l (ρ / 2) - yukawa d l ρ) := by rw [hb]; ring

theorem ball_coef_le_cfl (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {η : ℝ} (hη : 0 < η) :
    l * yukawa d l η * (η / 2) ^ d ≤ cfl d l (η / 2) := by
  have hη2 : 0 < η / 2 := half_pos hη
  set q : ℝ → ℝ := fun r => r ^ (d - 1) * deriv (yukawa d l) r with hq
  have hqd : ∀ r, 0 < r → HasDerivAt q (l * r ^ (d - 1) * yukawa d l r) r :=
    fun r hr => SmearAux.hasDerivAt_flux hd hl hr
  have hcont : ContinuousOn q (Icc (η / 2) η) := fun x hx =>
    (hqd x (lt_of_lt_of_le hη2 hx.1)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ q (Ioo (η / 2) η) := fun x hx =>
    (hqd x (lt_trans hη2 hx.1)).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope q (half_lt_self hη) hcont hdiff
  have hc0 : 0 < c := lt_trans hη2 hc.1
  rw [(hqd c hc0).deriv] at hcd
  have e1 : η - η / 2 = η / 2 := by ring
  rw [e1] at hcd
  have hG : yukawa d l η ≤ yukawa d l c := by
    rcases eq_or_lt_of_le hc.2.le with h | h
    · rw [h]
    · exact ((yukawa_ode hd hl).2.1 c η hc0 h).le
  have hpow : (η / 2) ^ (d - 1) ≤ c ^ (d - 1) := pow_le_pow_left₀ hη2.le hc.1.le _
  have hΓ0 : 0 < yukawa d l η := (yukawa_ode hd hl).1 η hη
  have h2 : l * (η / 2) ^ (d - 1) * yukawa d l η ≤ l * c ^ (d - 1) * yukawa d l c := by
    have := mul_le_mul hpow hG hΓ0.le (pow_pos hc0 _).le
    nlinarith [mul_le_mul_of_nonneg_left this hl.le]
  have h3 : q η - q (η / 2) = (η / 2) * (l * c ^ (d - 1) * yukawa d l c) := by
    rw [hcd]; field_simp
  have h4 : q η - q (η / 2) = cfl d l (η / 2) - cfl d l η := by
    simp only [hq, cfl]; ring
  have h5 : 0 < cfl d l η := cfl_pos hd hl hη
  have hpd : (η / 2) ^ d = (η / 2) ^ (d - 1) * (η / 2) := by
    rw [← pow_succ]; congr 1; omega
  have h6 : (η / 2) * (l * (η / 2) ^ (d - 1) * yukawa d l η) ≤ q η - q (η / 2) := by
    rw [h3]; exact mul_le_mul_of_nonneg_left h2 hη2.le
  calc l * yukawa d l η * (η / 2) ^ d = (η / 2) * (l * (η / 2) ^ (d - 1) * yukawa d l η) := by
        rw [hpd]; ring
    _ ≤ q η - q (η / 2) := h6
    _ ≤ cfl d l (η / 2) := by rw [h4]; linarith

/-! ### Measurability in `(l, r)` -/

theorem measurable_yukawa_uncurry (d : ℕ) : Measurable fun p : ℝ × ℝ => yukawa d p.1 p.2 := by
  unfold yukawa
  have hm : Measurable fun q : (ℝ × ℝ) × ℝ => Real.exp (-q.1.1 * q.2) *
      ((4 * Real.pi * q.2) ^ (-(d : ℝ) / 2) * Real.exp (-q.1.2 ^ 2 / (4 * q.2))) := by
    refine Measurable.mul (Real.measurable_exp.comp (measurable_fst.fst.neg.mul measurable_snd))
      (Measurable.mul ?_ ?_)
    · exact (measurable_const.mul measurable_snd).pow_const _
    · exact Real.measurable_exp.comp ((measurable_fst.snd.pow_const 2).neg.div (measurable_const.mul measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

theorem measurable_yukawa_l (d : ℕ) (r : ℝ) : Measurable fun l : ℝ => yukawa d l r :=
  (measurable_yukawa_uncurry d).comp (measurable_id.prodMk measurable_const)

theorem aemeasurable_cfl (hd : 1 ≤ d) (ρ : ℝ) (hρ : 0 < ρ) :
    AEMeasurable (fun l : ℝ => cfl d l ρ) (volume.restrict (Ioi (0 : ℝ))) := by
  have hm : Measurable fun l : ℝ => SmearAux.kappa d - l * ∫ s in Ioc (0 : ℝ) ρ, s ^ (d - 1) * yukawa d l s := by
    refine measurable_const.sub (measurable_id.mul ?_)
    have h : Measurable fun q : ℝ × ℝ => q.2 ^ (d - 1) * yukawa d q.1 q.2 :=
      (measurable_snd.pow_const _).mul ((measurable_yukawa_uncurry d).comp (measurable_fst.prodMk measurable_snd))
    exact (h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) ρ))).measurable
  refine hm.aemeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun l hl => ?_)
  have hl' : (0 : ℝ) < l := hl
  beta_reduce
  rw [cfl_eq_kappa hd hl' hρ]
  rfl


theorem measurable_fTrunc_uncurry (d : ℕ) (η : ℝ) :
    Measurable fun p : ℝ × Torus d => fTrunc d p.1 η p.2 := by
  have : (fun p : ℝ × Torus d => fTrunc d p.1 η p.2) =
      fun p => max (yukawa d p.1 (KernelGrad.tdist p.2 0) - yukawa d p.1 η) 0 := by
    funext p; simp [fTrunc, KernelGrad.tdist]
  rw [this]
  refine Measurable.max (Measurable.sub ?_ ?_) measurable_const
  · exact (measurable_yukawa_uncurry d).comp (measurable_fst.prodMk (EnergyAux.measurable_tdist_zero.comp measurable_snd))
  · exact (measurable_yukawa_uncurry d).comp (measurable_fst.prodMk measurable_const)

/-! ### `l`-integral of the sphere coefficient (L4) -/

theorem selfScale_half_sub_pos {s : ℝ} (hs0 : 0 ≤ s) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < selfScale d s (ρ / 2) - selfScale d s ρ := by
  unfold selfScale
  split_ifs with h0
  · have : Real.log (ρ / 2) = Real.log ρ - Real.log 2 := Real.log_div hρ.ne' two_ne_zero
    rw [this]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
    exact sub_pos.mpr (Real.rpow_lt_rpow_of_neg (half_pos hρ) (half_lt_self hρ) (by linarith))

theorem selfScale_half_sub_le {s : ℝ} (hs0 : 0 ≤ s) {ρ : ℝ} (hρ : 0 < ρ) :
    selfScale d s (ρ / 2) - selfScale d s ρ ≤ 2 ^ s * ρ ^ (-s) := by
  unfold selfScale
  split_ifs with h0
  · subst h0
    have : Real.log (ρ / 2) = Real.log ρ - Real.log 2 := Real.log_div hρ.ne' two_ne_zero
    rw [this]
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    simp only [neg_zero, Real.rpow_zero, mul_one]
    linarith
  · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
    have e : (ρ / 2) ^ (-s) = 2 ^ s * ρ ^ (-s) := by
      rw [Real.div_rpow hρ.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    rw [e]
    have : 0 ≤ ρ ^ (-s) := Real.rpow_nonneg hρ.le _
    linarith

theorem rho_pow_id (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) :
    ρ ^ (d - 1) * (2 / ρ) * ρ ^ (-s) = 2 * ρ ^ ((d : ℝ) - 2 - s) := by
  have h1 : ρ ^ (d - 1) = ρ ^ ((d : ℝ) - 1) := by
    rw [← Real.rpow_natCast]; congr 1; rw [Nat.cast_sub hd]; simp
  have h2 : 2 / ρ = 2 * ρ ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; ring
  rw [h1, h2]
  have h3 : ρ ^ ((d : ℝ) - 2 - s) = ρ ^ ((d : ℝ) - 1) * ρ ^ (-1 : ℝ) * ρ ^ (-s) := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ]; congr 1; ring
  rw [h3]; ring

theorem cfl_stieltjes (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ ρ : ℝ, 0 < ρ →
      IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * cfl d l ρ) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * cfl d l ρ ≤ Cp * ρ ^ ((d : ℝ) - 2 - s) := by
  obtain ⟨c', hc', hyk⟩ := yukawa_stieltjes hd hs0 hs hsd
  refine ⟨2 * c' * 2 ^ s, by positivity, fun ρ hρ => ?_⟩
  set D : ℝ → ℝ := fun l => yukawa d l (ρ / 2) - yukawa d l ρ with hD
  have hV : ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * D l =
      c' * (selfScale d s (ρ / 2) - selfScale d s ρ) := hyk (ρ / 2) ρ (half_pos hρ) hρ
  have hVpos : 0 < c' * (selfScale d s (ρ / 2) - selfScale d s ρ) :=
    mul_pos hc' (selfScale_half_sub_pos hs0 hρ)
  have hDi : IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * D l) (Ioi 0) := by
    by_contra h
    rw [integral_undef h] at hV
    linarith
  have hmeas : AEStronglyMeasurable (fun l : ℝ => l ^ (-bexp d s) * cfl d l ρ) (volume.restrict (Ioi (0 : ℝ))) :=
    ((measurable_id.pow_const _).aemeasurable.mul (aemeasurable_cfl hd ρ hρ)).aestronglyMeasurable
  have hdom : ∀ l ∈ Ioi (0 : ℝ), l ^ (-bexp d s) * cfl d l ρ ≤
      (ρ ^ (d - 1) * (2 / ρ)) * (l ^ (-bexp d s) * D l) := by
    intro l hl
    have hl' : (0 : ℝ) < l := hl
    have := cfl_le_diff hd hl' hρ
    have hp : 0 ≤ l ^ (-bexp d s) := Real.rpow_nonneg hl'.le _
    calc l ^ (-bexp d s) * cfl d l ρ ≤ l ^ (-bexp d s) * (ρ ^ (d - 1) * (2 / ρ) * D l) :=
          mul_le_mul_of_nonneg_left this hp
      _ = _ := by ring
  have hdomi : IntegrableOn (fun l : ℝ => (ρ ^ (d - 1) * (2 / ρ)) * (l ^ (-bexp d s) * D l)) (Ioi 0) :=
    hDi.const_mul _
  have hint : IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * cfl d l ρ) (Ioi 0) := by
    refine Integrable.mono' hdomi hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun l hl => ?_)
    have hl' : (0 : ℝ) < l := hl
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hl'.le _) (cfl_pos hd hl' hρ).le)]
    exact hdom l hl
  refine ⟨hint, ?_⟩
  calc ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * cfl d l ρ
      ≤ ∫ l in Ioi (0 : ℝ), (ρ ^ (d - 1) * (2 / ρ)) * (l ^ (-bexp d s) * D l) :=
        setIntegral_mono_on hint hdomi measurableSet_Ioi hdom
    _ = (ρ ^ (d - 1) * (2 / ρ)) * (c' * (selfScale d s (ρ / 2) - selfScale d s ρ)) := by
        rw [integral_const_mul, hV]
    _ ≤ (ρ ^ (d - 1) * (2 / ρ)) * (c' * (2 ^ s * ρ ^ (-s))) := by
        have h0 : 0 ≤ ρ ^ (d - 1) * (2 / ρ) := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (selfScale_half_sub_le hs0 hρ) hc'.le) h0
    _ = (2 * c' * 2 ^ s) * ρ ^ ((d : ℝ) - 2 - s) := by
        have := rho_pow_id hd hρ s
        calc (ρ ^ (d - 1) * (2 / ρ)) * (c' * (2 ^ s * ρ ^ (-s)))
            = c' * 2 ^ s * (ρ ^ (d - 1) * (2 / ρ) * ρ ^ (-s)) := by ring
          _ = _ := by rw [this]; ring


/-! ### Total mass of the slice charge -/

/-- total mass `m_l(η) = σ_{l,η}(𝕋^d)` -/
def mass (d : ℕ) (l η : ℝ) : ℝ := (smearT d l η).real univ

theorem mass_eq (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) :
    mass d l η = l * yukawa d l η * (η ^ d * (volume : Measure (Euc d)).real (Metric.ball 0 1)) +
      cfl d l η * (volume : Measure (Euc d)).toSphere.real univ := by
  unfold mass
  rw [SmearAux.smearT_real_eq, smearEuc_real_univ hd hl hη]
  rfl

theorem mass_nonneg (d : ℕ) (l η : ℝ) : 0 ≤ mass d l η := measureReal_nonneg

theorem mass_le_one (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) :
    mass d l η ≤ 1 := by
  unfold mass
  rw [smearT_real_univ hd hl hη hη2]
  have : 0 ≤ ∫ z : Torus d, fTrunc d l η z := integral_nonneg fun z => le_max_right _ _
  nlinarith

theorem ball_coef_le_mass (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) :
    l * yukawa d l η * (η ^ d * (volume : Measure (Euc d)).real (Metric.ball 0 1)) ≤ mass d l η := by
  rw [mass_eq hd hl hη]
  have : 0 ≤ cfl d l η * (volume : Measure (Euc d)).toSphere.real univ :=
    mul_nonneg (cfl_pos hd hl hη).le measureReal_nonneg
  linarith

theorem sphere_coef_le_mass (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) :
    cfl d l η * (volume : Measure (Euc d)).toSphere.real univ ≤ mass d l η := by
  rw [mass_eq hd hl hη]
  have : 0 ≤ l * yukawa d l η * (η ^ d * (volume : Measure (Euc d)).real (Metric.ball 0 1)) :=
    mul_nonneg (mul_nonneg hl.le ((yukawa_ode hd hl).1 η hη).le) (mul_nonneg (pow_nonneg hη.le _) measureReal_nonneg)
  linarith

theorem mass_le_cfl_half (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) :
    mass d l η ≤ (2 ^ d * (volume : Measure (Euc d)).real (Metric.ball 0 1) +
      (volume : Measure (Euc d)).toSphere.real univ) * cfl d l (η / 2) := by
  rw [mass_eq hd hl hη]
  have h1 := ball_coef_le_cfl hd hl hη
  have h2 := cfl_antitone hd hl (half_pos hη) (half_le_self hη.le)
  have hω : 0 ≤ (volume : Measure (Euc d)).real (Metric.ball 0 1) := measureReal_nonneg
  have hS : 0 ≤ (volume : Measure (Euc d)).toSphere.real univ := measureReal_nonneg
  have e : l * yukawa d l η * (η ^ d * (volume : Measure (Euc d)).real (Metric.ball 0 1)) =
      (2 ^ d * (volume : Measure (Euc d)).real (Metric.ball 0 1)) * (l * yukawa d l η * (η / 2) ^ d) := by
    rw [div_pow]; field_simp
  rw [e]
  have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 ^ d * (volume : Measure (Euc d)).real (Metric.ball 0 1))
  have h4 := mul_le_mul_of_nonneg_right h2 hS
  nlinarith

theorem mass_integral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ η : ℝ, 0 < η → η < 1 / 2 →
      IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * mass d l η) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * mass d l η ≤ Cm * η ^ ((d : ℝ) - 2 - s) := by
  obtain ⟨Cp, hCp, hcs⟩ := cfl_stieltjes hd hs0 hs hsd
  set K0 : ℝ := 2 ^ d * (volume : Measure (Euc d)).real (Metric.ball 0 1) +
      (volume : Measure (Euc d)).toSphere.real univ with hK0
  have hK00 : 0 ≤ K0 := by
    have : 0 ≤ (volume : Measure (Euc d)).real (Metric.ball 0 1) := measureReal_nonneg
    have : 0 ≤ (volume : Measure (Euc d)).toSphere.real univ := measureReal_nonneg
    positivity
  refine ⟨K0 * Cp * 2 ^ ((s : ℝ) + 2 - d), by positivity, fun η hη hη2 => ?_⟩
  obtain ⟨hI, hJ⟩ := hcs (η / 2) (half_pos hη)
  have hmeas : AEStronglyMeasurable (fun l : ℝ => l ^ (-bexp d s) * mass d l η) (volume.restrict (Ioi (0 : ℝ))) := by
    have h1 : AEMeasurable (fun l : ℝ => mass d l η) (volume.restrict (Ioi (0 : ℝ))) := by
      have h2 : AEMeasurable (fun l : ℝ => l * yukawa d l η * (η ^ d * (volume : Measure (Euc d)).real (Metric.ball 0 1)) +
          cfl d l η * (volume : Measure (Euc d)).toSphere.real univ) (volume.restrict (Ioi (0 : ℝ))) :=
        (((measurable_id.mul (measurable_yukawa_l d η)).mul measurable_const).aemeasurable).add
          ((aemeasurable_cfl hd η hη).mul aemeasurable_const)
      refine h2.congr ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun l hl => ?_)
      exact (mass_eq hd (show (0 : ℝ) < l from hl) hη).symm
    exact ((measurable_id.pow_const _).aemeasurable.mul h1).aestronglyMeasurable
  have hdom : ∀ l ∈ Ioi (0 : ℝ), l ^ (-bexp d s) * mass d l η ≤ K0 * (l ^ (-bexp d s) * cfl d l (η / 2)) := by
    intro l hl
    have hl' : (0 : ℝ) < l := hl
    have := mass_le_cfl_half hd hl' hη
    calc l ^ (-bexp d s) * mass d l η ≤ l ^ (-bexp d s) * (K0 * cfl d l (η / 2)) :=
          mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hl'.le _)
      _ = _ := by ring
  have hdomi : IntegrableOn (fun l : ℝ => K0 * (l ^ (-bexp d s) * cfl d l (η / 2))) (Ioi 0) := hI.const_mul _
  have hint : IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * mass d l η) (Ioi 0) := by
    refine Integrable.mono' hdomi hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun l hl => ?_)
    have hl' : (0 : ℝ) < l := hl
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hl'.le _) (mass_nonneg d l η))]
    exact hdom l hl
  refine ⟨hint, ?_⟩
  calc ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * mass d l η
      ≤ ∫ l in Ioi (0 : ℝ), K0 * (l ^ (-bexp d s) * cfl d l (η / 2)) :=
        setIntegral_mono_on hint hdomi measurableSet_Ioi hdom
    _ = K0 * ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * cfl d l (η / 2) := integral_const_mul _ _
    _ ≤ K0 * (Cp * (η / 2) ^ ((d : ℝ) - 2 - s)) := mul_le_mul_of_nonneg_left hJ hK00
    _ = (K0 * Cp * 2 ^ ((s : ℝ) + 2 - d)) * η ^ ((d : ℝ) - 2 - s) := by
        rw [Real.div_rpow hη.le (by norm_num)]
        have : (2 : ℝ) ^ ((d : ℝ) - 2 - s) = (2 ^ ((s : ℝ) + 2 - d))⁻¹ := by
          rw [← Real.rpow_neg (by norm_num)]; congr 1; ring
        rw [this]
        have hp : (0 : ℝ) < 2 ^ ((s : ℝ) + 2 - d) := by positivity
        field_simp

/-! ### The mass defect `∫ f_{l,η}` (L3) -/

theorem Fint_le_inv (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∫ z : Torus d, fTrunc d l η z ≤ 1 / l := by
  have h := smearT_real_univ hd hl hη hη2
  have h0 : 0 ≤ (smearT d l η).real univ := measureReal_nonneg
  rw [le_div_iff₀ hl]
  nlinarith

theorem fTrunc_anti_ae (hd : 1 ≤ d) {l l' η : ℝ} (hl' : 0 < l') (hll : l' ≤ l) (hη : 0 < η) :
    ∀ᵐ z : Torus d, fTrunc d l η z ≤ fTrunc d l' η z := by
  have hl : 0 < l := lt_of_lt_of_le hl' hll
  filter_upwards [KernelAux.torus_ae_ne (by omega : 0 < d)] with z hz
  have hr : 0 < KernelGrad.tdist z 0 := KernelGrad.tdist_pos hz
  have hn : ‖KernelGrad.centeredRep z‖ = KernelGrad.tdist z 0 := EnergyAux.norm_centeredRep_eq z
  unfold fTrunc
  rw [hn]
  by_cases hrη : KernelGrad.tdist z 0 ≤ η
  · refine max_le_max ?_ le_rfl
    set r := KernelGrad.tdist z 0 with hrdef
    have hI1 := SliceAux.integrableOn_yk hl hd hr
    have hI2 := SliceAux.integrableOn_yk hl hd hη
    have hI1' := SliceAux.integrableOn_yk hl' hd hr
    have hI2' := SliceAux.integrableOn_yk hl' hd hη
    have hy : ∀ l r : ℝ, yukawa d l r = ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * SliceAux.gprof d t r :=
      fun l r => rfl
    have e1 : yukawa d l r - yukawa d l η = ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) *
        (SliceAux.gprof d t r - SliceAux.gprof d t η) := by
      rw [hy, hy, ← integral_sub hI1 hI2]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      ring
    have e2 : yukawa d l' r - yukawa d l' η = ∫ t in Ioi (0 : ℝ), Real.exp (-l' * t) *
        (SliceAux.gprof d t r - SliceAux.gprof d t η) := by
      rw [hy, hy, ← integral_sub hI1' hI2']
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      ring
    rw [e1, e2]
    have hi1 : IntegrableOn (fun t : ℝ => Real.exp (-l * t) * (SliceAux.gprof d t r - SliceAux.gprof d t η)) (Ioi 0) := by
      have := hI1.sub hI2
      refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply]; ring
    have hi2 : IntegrableOn (fun t : ℝ => Real.exp (-l' * t) * (SliceAux.gprof d t r - SliceAux.gprof d t η)) (Ioi 0) := by
      have := hI1'.sub hI2'
      refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply]; ring
    refine setIntegral_mono_on hi1 hi2 measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    have hg : 0 ≤ SliceAux.gprof d t r - SliceAux.gprof d t η := by
      simp only [SliceAux.gprof]
      have hc : 0 < (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by positivity
      have : Real.exp (-η ^ 2 / (4 * t)) ≤ Real.exp (-r ^ 2 / (4 * t)) := by
        apply Real.exp_le_exp.mpr
        have : r ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hr.le hrη 2
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      nlinarith [mul_le_mul_of_nonneg_left this hc.le]
    have : Real.exp (-l * t) ≤ Real.exp (-l' * t) := by
      apply Real.exp_le_exp.mpr; nlinarith
    exact mul_le_mul_of_nonneg_right this hg
  · push Not at hrη
    have h1 := (yukawa_ode hd hl).2.1 η _ hη hrη
    have h2 := (yukawa_ode hd hl').2.1 η _ hη hrη
    have : max (yukawa d l (KernelGrad.tdist z 0) - yukawa d l η) 0 = 0 := max_eq_right (by linarith)
    rw [this]
    exact le_max_right _ _

theorem Fint_le_quad (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∫ z : Torus d, fTrunc d l η z ≤ η ^ 2 / (2 * d) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hT : 0 < η ^ 2 / (2 * (d : ℝ)) := by positivity
  have htend := SmearAux.tendsto_int_fTrunc hd hη hη2
  have hnn : ∀ l' : ℝ, 0 ≤ fTrunc d l' η := fun l' z => le_max_right _ _
  have hrep : ∀ l' : ℝ, ∫ z : Torus d, fTrunc d l' η z =
      (∫⁻ z : Torus d, ENNReal.ofReal (fTrunc d l' η z)).toReal := fun l' =>
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hnn l'))
      (EnergyAux.measurable_fTrunc l' η).aestronglyMeasurable
  refine ge_of_tendsto htend ?_
  have hev1 := htend.eventually (lt_mem_nhds hT)
  filter_upwards [hev1, self_mem_nhdsWithin, Ioc_mem_nhdsGT hl] with l' hpos hl'0 hl'l
  have hl'0' : (0 : ℝ) < l' := hl'0
  have hfin : (∫⁻ z : Torus d, ENNReal.ofReal (fTrunc d l' η z)) ≠ ⊤ := by
    intro htop
    rw [hrep l', htop] at hpos
    simp at hpos
  have hle : ∫⁻ z : Torus d, ENNReal.ofReal (fTrunc d l η z) ≤ ∫⁻ z : Torus d, ENNReal.ofReal (fTrunc d l' η z) := by
    refine lintegral_mono_ae ?_
    filter_upwards [fTrunc_anti_ae hd hl'0' hl'l.2 hη] with z hz
    exact ENNReal.ofReal_le_ofReal hz
  rw [hrep l, hrep l']
  exact ENNReal.toReal_mono hfin hle

theorem Fint_le_min (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∫ z : Torus d, fTrunc d l η z ≤ min (η ^ 2 / (2 * d)) (1 / l) :=
  le_min (Fint_le_quad hd hl hη hη2) (Fint_le_inv hd hl hη hη2)

/-- `∫_0^∞ l^{-β} min(T, 1/l) dl ≤ (1/β + 1/(1-β)) T^β` -/
theorem integral_min_inv {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun l : ℝ => l ^ (-β) * min T (1 / l)) (Ioi 0) ∧
    ∫ l in Ioi (0 : ℝ), l ^ (-β) * min T (1 / l) ≤ (1 / β + 1 / (1 - β)) * T ^ β := by
  set a : ℝ := 1 / T with ha
  have ha0 : 0 < a := by positivity
  have hi1 : IntegrableOn (fun l : ℝ => T * l ^ (-β)) (Ioc 0 a) := by
    have : IntegrableOn (fun l : ℝ => l ^ (-β)) (Ioc 0 a) := by
      have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := a) (r := -β) (by linarith))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha0.le).mp h
    exact this.const_mul T
  have hi2 : IntegrableOn (fun l : ℝ => l ^ (-β - 1)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ha0
  have hmeas : AEStronglyMeasurable (fun l : ℝ => l ^ (-β) * min T (1 / l)) (volume.restrict (Ioi (0 : ℝ))) := by
    refine Measurable.aestronglyMeasurable ?_
    exact (measurable_id.pow_const _).mul (measurable_const.min (measurable_const.div measurable_id))
  have hsplit : Ioi (0 : ℝ) = Ioc 0 a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha0.le).symm
  have hd1 : ∀ l ∈ Ioc (0 : ℝ) a, l ^ (-β) * min T (1 / l) ≤ T * l ^ (-β) := by
    intro l hl
    have := min_le_left T (1 / l)
    have hp : 0 ≤ l ^ (-β) := Real.rpow_nonneg hl.1.le _
    nlinarith
  have hd2 : ∀ l ∈ Ioi a, l ^ (-β) * min T (1 / l) ≤ l ^ (-β - 1) := by
    intro l hl
    have hl0 : 0 < l := lt_trans ha0 hl
    have := min_le_right T (1 / l)
    have hp : 0 ≤ l ^ (-β) := Real.rpow_nonneg hl0.le _
    have e : l ^ (-β - 1) = l ^ (-β) * (1 / l) := by
      rw [Real.rpow_sub hl0, Real.rpow_one]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left this hp
  have hint1 : IntegrableOn (fun l : ℝ => l ^ (-β) * min T (1 / l)) (Ioc 0 a) := by
    refine Integrable.mono' hi1 (hmeas.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun l hl => ?_)
    have hmn : 0 ≤ min T (1 / l) := le_min hT.le (by have := hl.1; positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hl.1.le _) hmn)]
    exact hd1 l hl
  have hint2 : IntegrableOn (fun l : ℝ => l ^ (-β) * min T (1 / l)) (Ioi a) := by
    refine Integrable.mono' hi2 (hmeas.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi ha0.le) le_rfl)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun l hl => ?_)
    have hl0 : 0 < l := lt_trans ha0 hl
    have hmn : 0 ≤ min T (1 / l) := le_min hT.le (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hl0.le _) hmn)]
    exact hd2 l hl
  have hint : IntegrableOn (fun l : ℝ => l ^ (-β) * min T (1 / l)) (Ioi 0) := by
    rw [hsplit]; exact hint1.union hint2
  refine ⟨hint, ?_⟩
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint1 hint2]
  have hkey1 : T * (1 / T) ^ (-β + 1) = T ^ β := by
    rw [one_div, Real.inv_rpow hT.le, ← Real.rpow_neg hT.le]
    have : T ^ β = T ^ (1 + (-(-β + 1))) := by congr 1; ring
    rw [this, Real.rpow_add hT, Real.rpow_one]
  have hkey2 : (1 / T) ^ (-β) = T ^ β := by
    rw [one_div, Real.inv_rpow hT.le, Real.rpow_neg hT.le, inv_inv]
  have hv1 : ∫ l in Ioc (0 : ℝ) a, T * l ^ (-β) = T ^ β / (1 - β) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le ha0.le, integral_rpow (Or.inl (by linarith))]
    rw [Real.zero_rpow (by linarith : (-β + 1) ≠ 0), sub_zero, ha]
    have : (-β + 1) = 1 - β := by ring
    rw [this] at hkey1 ⊢
    rw [← hkey1]; field_simp
  have hv2 : ∫ l in Ioi a, l ^ (-β - 1) = T ^ β / β := by
    rw [integral_Ioi_rpow_of_lt (by linarith) ha0, show -β - 1 + 1 = -β by ring, ha, hkey2]
    field_simp
  calc (∫ l in Ioc (0 : ℝ) a, l ^ (-β) * min T (1 / l)) + ∫ l in Ioi a, l ^ (-β) * min T (1 / l)
      ≤ (∫ l in Ioc (0 : ℝ) a, T * l ^ (-β)) + ∫ l in Ioi a, l ^ (-β - 1) := by
        refine add_le_add (setIntegral_mono_on hint1 hi1 measurableSet_Ioc hd1)
          (setIntegral_mono_on hint2 hi2 measurableSet_Ioi hd2)
    _ = (1 / β + 1 / (1 - β)) * T ^ β := by
        rw [hv1, hv2]; have h1 : 0 < 1 - β := by linarith
        field_simp; ring

theorem Fint_stieltjes (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ η : ℝ, 0 < η → η < 1 / 2 →
      IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * ∫ z : Torus d, fTrunc d l η z) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * ∫ z : Torus d, fTrunc d l η z ≤ CF * η ^ ((d : ℝ) - s) := by
  have hβ0 : 0 < bexp d s := by unfold bexp; linarith
  have hβ1 : bexp d s < 1 := by unfold bexp; linarith
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨1 / bexp d s + 1 / (1 - bexp d s), by
    have : 0 < 1 - bexp d s := by linarith
    positivity, fun η hη hη2 => ?_⟩
  set T : ℝ := η ^ 2 / (2 * d) with hT
  have hT0 : 0 < T := by positivity
  obtain ⟨hI, hJ⟩ := integral_min_inv hβ0 hβ1 hT0
  have hmeas : AEStronglyMeasurable (fun l : ℝ => l ^ (-bexp d s) * ∫ z : Torus d, fTrunc d l η z)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have h1 : Measurable fun l : ℝ => ∫ z : Torus d, fTrunc d l η z :=
      ((measurable_fTrunc_uncurry d η).stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Torus d)))).measurable
    exact ((measurable_id.pow_const _).mul h1).aestronglyMeasurable
  have hdom : ∀ l ∈ Ioi (0 : ℝ), l ^ (-bexp d s) * ∫ z : Torus d, fTrunc d l η z ≤
      l ^ (-bexp d s) * min T (1 / l) := by
    intro l hl
    have hl' : (0 : ℝ) < l := hl
    exact mul_le_mul_of_nonneg_left (Fint_le_min hd hl' hη hη2) (Real.rpow_nonneg hl'.le _)
  have hint : IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * ∫ z : Torus d, fTrunc d l η z) (Ioi 0) := by
    refine Integrable.mono' hI hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun l hl => ?_)
    have hl' : (0 : ℝ) < l := hl
    have h0 : 0 ≤ ∫ z : Torus d, fTrunc d l η z := integral_nonneg fun z => le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hl'.le _) h0)]
    exact hdom l hl
  refine ⟨hint, ?_⟩
  refine (setIntegral_mono_on hint hI measurableSet_Ioi hdom).trans (hJ.trans ?_)
  have hc : 0 ≤ 1 / bexp d s + 1 / (1 - bexp d s) := by
    have : 0 < 1 - bexp d s := by linarith
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hc
  have h2d : (1 : ℝ) ≤ 2 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  calc T ^ bexp d s ≤ (η ^ 2) ^ bexp d s := by
        refine Real.rpow_le_rpow hT0.le ?_ hβ0.le
        rw [hT]
        exact div_le_self (by positivity) h2d
    _ = η ^ ((d : ℝ) - s) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
        congr 1
        unfold bexp
        push_cast; ring

end HRS.Commutator.Stj
