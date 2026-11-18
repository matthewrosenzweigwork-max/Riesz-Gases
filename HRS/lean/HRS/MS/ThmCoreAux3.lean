import HRS.MS.ThmCoreAux2

/-!
# THM-1: relative entropy lemmas and the free-energy identity

Namespace `HRS.MS.Thm`; helper lemmas carry the prefix `t012_`.

* `relEnt_nonneg`, `relEnt_eq_zero_iff`, `relEnt_mix`: for probability densities `l`, `μ`, `ν` with `0 < ν x`
  everywhere (the positivity of the reference density cannot be dropped: at `ν x = 0` one has
  `l = ½ 1_[0,2]`, `ν = 1_[0,1]` with `relEnt l ν = 0` but `l ≠ ν`), and with the integrability of
  `l log (l / ν)` as an explicit hypothesis (otherwise the Bochner integral is the junk value `0`).
* `fe_identity`: for `μ ∈ Cset r M` (`1 ≤ M`), a probability density `l` with `l log (l / r)` and
  `|K l l|` integrable, and `0 < β`:
  `G l - G μ = β⁻¹ (relEnt l (Tmap μ) - relEnt μ (Tmap μ)) + ½ pairE K (l - μ) (l - μ)`,
  together with the integrability of `l log (l / Tmap μ)`, `μ log (μ / Tmap μ)` and of
  `K (l - μ) (l - μ)` on the product, which exclude every junk value of the Bochner integrals.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-! ### Pointwise facts on `x log (x / y)` -/

theorem t012_pw_ge {l ν : ℝ} (hl : 0 ≤ l) (hν : 0 < ν) : l - ν ≤ l * Real.log (l / ν) := by
  rcases hl.eq_or_lt with h0 | hpos
  · subst h0; simp; exact hν.le
  · have h1 : Real.log (ν / l) ≤ ν / l - 1 := Real.log_le_sub_one_of_pos (div_pos hν hpos)
    have h2 : Real.log (l / ν) = - Real.log (ν / l) := by
      rw [← Real.log_inv, inv_div]
    rw [h2]
    have h3 : l * (ν / l - 1) = ν - l := by field_simp
    nlinarith

theorem t012_pw_gt {l ν : ℝ} (hl : 0 ≤ l) (hν : 0 < ν) (hne : l ≠ ν) :
    l - ν < l * Real.log (l / ν) := by
  rcases hl.eq_or_lt with h0 | hpos
  · subst h0; simp; exact hν
  · have hne' : ν / l ≠ 1 := by
      intro h; apply hne; field_simp at h; linarith
    have h1 : Real.log (ν / l) < ν / l - 1 := Real.log_lt_sub_one_of_pos (div_pos hν hpos) hne'
    have h2 : Real.log (l / ν) = - Real.log (ν / l) := by
      rw [← Real.log_inv, inv_div]
    rw [h2]
    have h3 : l * (ν / l - 1) = ν - l := by field_simp
    nlinarith

theorem t012_mul_log_div {m ν : ℝ} (hm : 0 ≤ m) (hν : 0 < ν) :
    m * Real.log (m / ν) = m * Real.log m - m * Real.log ν := by
  rcases hm.eq_or_lt with h0 | hpos
  · subst h0; simp
  · rw [Real.log_div hpos.ne' hν.ne']; ring

/-! ### Relative entropy of densities -/

theorem t012_integrable_of_prob {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) : Integrable ρ :=
  Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; norm_num)

theorem t012_relEnt_integrand_meas {l ν : Euc d → ℝ} (hl : Measurable l) (hν : Measurable ν) :
    Measurable fun x => l x * Real.log (l x / ν x) :=
  hl.mul (Real.measurable_log.comp (hl.div hν))

/-- `x ↦ l log (l / ν) - (l - ν)` is a nonnegative integrable function with integral `relEnt l ν`. -/
theorem t012_relEnt_sub_integral {l ν : Euc d → ℝ} (hl : HRS.Whole.IsProbDensity l)
    (hν : HRS.Whole.IsProbDensity ν)
    (hint : Integrable (fun x => l x * Real.log (l x / ν x))) :
    Integrable (fun x => l x * Real.log (l x / ν x) - (l x - ν x)) ∧
      ∫ x, (l x * Real.log (l x / ν x) - (l x - ν x)) = relEnt l ν := by
  have hli := t012_integrable_of_prob hl
  have hνi := t012_integrable_of_prob hν
  have hd : Integrable fun x => l x - ν x := hli.sub hνi
  refine ⟨hint.sub hd, ?_⟩
  rw [integral_sub hint hd, integral_sub hli hνi, hl.integral_one, hν.integral_one]
  simp [relEnt]

theorem relEnt_nonneg {l ν : Euc d → ℝ} (hl : HRS.Whole.IsProbDensity l)
    (hν : HRS.Whole.IsProbDensity ν) (hνpos : ∀ x, 0 < ν x)
    (hint : Integrable (fun x => l x * Real.log (l x / ν x))) : 0 ≤ relEnt l ν := by
  obtain ⟨hi, he⟩ := t012_relEnt_sub_integral hl hν hint
  rw [← he]
  exact integral_nonneg fun x => sub_nonneg.2 (t012_pw_ge (hl.nonneg x) (hνpos x))

theorem relEnt_eq_zero_iff {l ν : Euc d → ℝ} (hl : HRS.Whole.IsProbDensity l)
    (hν : HRS.Whole.IsProbDensity ν) (hνpos : ∀ x, 0 < ν x)
    (hint : Integrable (fun x => l x * Real.log (l x / ν x))) :
    relEnt l ν = 0 ↔ l =ᵐ[volume] ν := by
  constructor
  · intro h0
    obtain ⟨hi, he⟩ := t012_relEnt_sub_integral hl hν hint
    have hnn : (0 : Euc d → ℝ) ≤ fun x => l x * Real.log (l x / ν x) - (l x - ν x) :=
      fun x => sub_nonneg.2 (t012_pw_ge (hl.nonneg x) (hνpos x))
    have hz := (integral_eq_zero_iff_of_nonneg hnn hi).1 (by rw [he]; exact h0)
    filter_upwards [hz] with x hx
    by_contra hne
    have := t012_pw_gt (hl.nonneg x) (hνpos x) hne
    simp only [Pi.zero_apply] at hx
    linarith
  · intro h
    unfold relEnt
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h] with x hx
    rw [hx, div_self (hνpos x).ne']
    simp

/-- Mixing towards the reference density: the mixture has integrable entropy integrand and
`relEnt ((1-t) μ + t ν) ν ≤ (1-t) relEnt μ ν`. -/
theorem relEnt_mix {μ ν : Euc d → ℝ} (hμ : HRS.Whole.IsProbDensity μ)
    (hν : HRS.Whole.IsProbDensity ν) (hνpos : ∀ x, 0 < ν x)
    (hint : Integrable (fun x => μ x * Real.log (μ x / ν x))) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Integrable (fun x => ((1 - t) * μ x + t * ν x) * Real.log (((1 - t) * μ x + t * ν x) / ν x)) ∧
      relEnt (fun x => (1 - t) * μ x + t * ν x) ν ≤ (1 - t) * relEnt μ ν := by
  set m : Euc d → ℝ := fun x => (1 - t) * μ x + t * ν x with hm
  have hm0 : ∀ x, 0 ≤ m x := fun x =>
    add_nonneg (mul_nonneg (by linarith) (hμ.nonneg x)) (mul_nonneg ht0 (hν.nonneg x))
  have hmm : Measurable m := (measurable_const.mul hμ.measurable).add (measurable_const.mul hν.measurable)
  have hmi : Integrable m := ((t012_integrable_of_prob hμ).const_mul (1 - t)).add
    ((t012_integrable_of_prob hν).const_mul t)
  have hup : ∀ x, m x * Real.log (m x / ν x) ≤ (1 - t) * (μ x * Real.log (μ x / ν x)) := by
    intro x
    have h1t : 0 ≤ 1 - t := by linarith
    have hconv := Real.convexOn_mul_log.2 (Set.mem_Ici.2 (hμ.nonneg x))
      (Set.mem_Ici.2 (hν.nonneg x)) h1t ht0 (by ring)
    simp only [smul_eq_mul] at hconv
    have hconv' : m x * Real.log (m x) ≤
        (1 - t) * (μ x * Real.log (μ x)) + t * (ν x * Real.log (ν x)) := hconv
    have hmx : m x = (1 - t) * μ x + t * ν x := rfl
    have e : m x * Real.log (ν x) = (1 - t) * (μ x * Real.log (ν x)) + t * (ν x * Real.log (ν x)) := by
      rw [hmx]; ring
    rw [t012_mul_log_div (hm0 x) (hνpos x), t012_mul_log_div (hμ.nonneg x) (hνpos x), e]
    nlinarith [hconv']
  have hlow : ∀ x, m x - ν x ≤ m x * Real.log (m x / ν x) := fun x =>
    t012_pw_ge (hm0 x) (hνpos x)
  have hgm : Measurable fun x => m x * Real.log (m x / ν x) :=
    t012_relEnt_integrand_meas hmm hν.measurable
  have hgi : Integrable fun x => m x * Real.log (m x / ν x) := by
    refine Integrable.mono' ((hint.const_mul (1 - t)).norm.add
      (hmi.sub (t012_integrable_of_prob hν)).norm) hgm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    apply abs_le.2
    constructor
    · have h1 := neg_abs_le (m x - ν x)
      have h2 := abs_nonneg ((1 - t) * (μ x * Real.log (μ x / ν x)))
      simp only [Real.norm_eq_abs, Pi.sub_apply, Pi.add_apply]
      linarith [hlow x]
    · have h1 := le_abs_self ((1 - t) * (μ x * Real.log (μ x / ν x)))
      have h2 := abs_nonneg (m x - ν x)
      simp only [Real.norm_eq_abs, Pi.sub_apply, Pi.add_apply]
      linarith [hup x]
  refine ⟨hgi, ?_⟩
  unfold relEnt
  calc ∫ x, m x * Real.log (m x / ν x) ≤ ∫ x, (1 - t) * (μ x * Real.log (μ x / ν x)) :=
        integral_mono hgi (hint.const_mul (1 - t)) hup
    _ = (1 - t) * ∫ x, μ x * Real.log (μ x / ν x) := integral_const_mul _ _

/-! ### The free-energy identity -/

section Identity

variable {K : Euc d → Euc d → ℝ} {r : Euc d → ℝ} {B : ℝ}

theorem t012_log_T {ρ r' u Z β : ℝ} (hρ : 0 ≤ ρ) (hr : 0 < r') (hZ : 0 < Z) :
    ρ * Real.log (ρ / (r' * Real.exp (-β * u) / Z)) =
      ρ * Real.log (ρ / r') + β * (ρ * u) + Real.log Z * ρ := by
  rcases hρ.eq_or_lt with h0 | hpos
  · subst h0; simp
  · have hT : 0 < r' * Real.exp (-β * u) / Z := div_pos (mul_pos hr (Real.exp_pos _)) hZ
    rw [Real.log_div hpos.ne' hT.ne', Real.log_div hpos.ne' hr.ne',
      Real.log_div (mul_pos hr (Real.exp_pos _)).ne' hZ.ne',
      Real.log_mul hr.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring

theorem t012_pairE_eq (K : Euc d → Euc d → ℝ) (ρ μ : Euc d → ℝ) :
    pairE K ρ μ = ∫ x, ρ x * ∫ y, K x y * μ y := by
  unfold pairE
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  beta_reduce
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  ring

theorem t012_pairE_eq_prod {K : Euc d → Euc d → ℝ} {f h : Euc d → ℝ}
    (hint : Integrable (fun p : Euc d × Euc d => K p.1 p.2 * f p.1 * h p.2)
      ((volume : Measure (Euc d)).prod volume)) :
    pairE K f h = ∫ p : Euc d × Euc d, K p.1 p.2 * f p.1 * h p.2
      ∂((volume : Measure (Euc d)).prod volume) :=
  (integral_prod _ hint).symm

/-- Entropy of `ρ` relative to the Euler iterate: `relEnt ρ (Tμ) = relEnt ρ r + β ⟨K μ, ρ⟩ + log Z_μ`. -/
theorem t012_relEnt_T (hS : ThmSetting K r B) {β M : ℝ} (hβ : 0 < β) (hM : 1 ≤ M)
    {μ : Euc d → ℝ} (hμ : μ ∈ Cset r M) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hρent : Integrable fun x => ρ x * Real.log (ρ x / r x)) :
    Integrable (fun x => ρ x * Real.log (ρ x / Tmap K r β μ x)) ∧
      relEnt ρ (Tmap K r β μ) =
        relEnt ρ r + β * pairE K ρ μ + Real.log (t012_Z K r β μ) := by
  have hM0 : 0 ≤ M := by linarith
  have hZ := t012_Z_pos hS hβ.le hμ.1
  have hum := t012_u_meas hS hμ.1.measurable
  have hρi := t012_integrable_of_prob hρ
  have hub : ∀ x, 0 ≤ ∫ y, K x y * μ y ∧ ∫ y, K x y * μ y ≤ M * B := fun x => by
    obtain ⟨_, h2, h3⟩ := conv_bound_of_le hS.meas hS.nonneg hS.k1 hμ.1.measurable hμ.1.nonneg hM0
      hμ.2 x
    exact ⟨h2, h3⟩
  have hρu : Integrable fun x => ρ x * ∫ y, K x y * μ y := by
    refine Integrable.mono' (hρi.const_mul (M * B)) (hρ.measurable.mul hum).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.nonneg x) (hub x).1)]
    calc ρ x * ∫ y, K x y * μ y ≤ ρ x * (M * B) :=
          mul_le_mul_of_nonneg_left (hub x).2 (hρ.nonneg x)
      _ = M * B * ρ x := by ring
  have hpt : ∀ x, ρ x * Real.log (ρ x / Tmap K r β μ x) =
      ρ x * Real.log (ρ x / r x) + β * (ρ x * ∫ y, K x y * μ y) +
        Real.log (t012_Z K r β μ) * ρ x := fun x => by
    rw [t012_Tmap_eq]
    exact t012_log_T (hρ.nonneg x) (hS.r_pos x) hZ
  have hint : Integrable fun x => ρ x * Real.log (ρ x / Tmap K r β μ x) :=
    ((hρent.add (hρu.const_mul β)).add (hρi.const_mul _)).congr
      (ae_of_all _ fun x => (hpt x).symm)
  refine ⟨hint, ?_⟩
  unfold relEnt
  simp_rw [hpt]
  have i1 : Integrable fun x => ρ x * Real.log (ρ x / r x) + β * (ρ x * ∫ y, K x y * μ y) :=
    hρent.add (hρu.const_mul β)
  have i2 : Integrable fun x => Real.log (t012_Z K r β μ) * ρ x := hρi.const_mul _
  rw [integral_add i1 i2, integral_add hρent (hρu.const_mul β), integral_const_mul,
    integral_const_mul, hρ.integral_one, t012_pairE_eq]
  ring

theorem t012_prod_swap_symm {K : Euc d → Euc d → ℝ} (hsymm : ∀ x y, K x y = K y x)
    {f h : Euc d → ℝ}
    (hint : Integrable (fun p : Euc d × Euc d => K p.1 p.2 * f p.1 * h p.2)
      ((volume : Measure (Euc d)).prod volume)) :
    Integrable (fun p : Euc d × Euc d => K p.1 p.2 * h p.1 * f p.2)
      ((volume : Measure (Euc d)).prod volume) ∧
    ∫ p : Euc d × Euc d, K p.1 p.2 * h p.1 * f p.2 ∂((volume : Measure (Euc d)).prod volume) =
      ∫ p : Euc d × Euc d, K p.1 p.2 * f p.1 * h p.2 ∂((volume : Measure (Euc d)).prod volume) := by
  have hpt : ∀ p : Euc d × Euc d, K p.1 p.2 * h p.1 * f p.2 =
      (fun q : Euc d × Euc d => K q.1 q.2 * f q.1 * h q.2) p.swap := fun p => by
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [hsymm p.1 p.2]; ring
  refine ⟨(hint.swap).congr (ae_of_all _ fun p => (hpt p).symm), ?_⟩
  simp_rw [hpt]
  exact integral_prod_swap (fun q : Euc d × Euc d => K q.1 q.2 * f q.1 * h q.2)

/-- THM-1, the free-energy identity at an arbitrary `μ ∈ C_M` (with the integrability conjuncts):
`G l - G μ = β⁻¹ (H(l | Tμ) - H(μ | Tμ)) + ½ E_K(l - μ)`. -/
theorem fe_identity (hS : ThmSetting K r B) {β M : ℝ} (hβ : 0 < β) (hM : 1 ≤ M)
    {μ l : Euc d → ℝ} (hμ : μ ∈ Cset r M) (hl : HRS.Whole.IsProbDensity l)
    (hlent : Integrable fun x => l x * Real.log (l x / r x))
    (hlK : Integrable (fun p : Euc d × Euc d => K p.1 p.2 * l p.1 * l p.2)
      ((volume : Measure (Euc d)).prod volume)) :
    Integrable (fun x => l x * Real.log (l x / Tmap K r β μ x)) ∧
    Integrable (fun x => μ x * Real.log (μ x / Tmap K r β μ x)) ∧
    Integrable (fun p : Euc d × Euc d => K p.1 p.2 * (l - μ) p.1 * (l - μ) p.2)
      ((volume : Measure (Euc d)).prod volume) ∧
    Gfun K r β l - Gfun K r β μ =
      β⁻¹ * (relEnt l (Tmap K r β μ) - relEnt μ (Tmap K r β μ)) +
        (1 / 2) * pairE K (l - μ) (l - μ) := by
  have hM0 : 0 ≤ M := by linarith
  have hr_int := t012_r_integrable hS
  have hμent : Integrable fun x => μ x * Real.log (μ x / r x) :=
    t012_integrable_mul_log_div_of_le hr_int hS.r_pos (t012_r_meas hS) hμ.1.measurable
      hμ.1.nonneg hμ.2
  obtain ⟨hlT, hlrel⟩ := t012_relEnt_T hS hβ hM hμ hl hlent
  obtain ⟨hμT, hμrel⟩ := t012_relEnt_T hS hβ hM hμ hμ.1 hμent
  have hli := t012_integrable_of_prob hl
  have hμi := t012_integrable_of_prob hμ.1
  -- product integrability
  have hμμ : Integrable (fun p : Euc d × Euc d => K p.1 p.2 * μ p.1 * μ p.2)
      ((volume : Measure (Euc d)).prod volume) :=
    t012_prod_integrable hS.meas hS.nonneg (fun y => (hS.r_pos y).le) hS.k1 hμ.1.measurable hμi
      hμ.1.measurable hM0 (fun y => by rw [abs_of_nonneg (hμ.1.nonneg y)]; exact hμ.2 y)
  have hlμ : Integrable (fun p : Euc d × Euc d => K p.1 p.2 * l p.1 * μ p.2)
      ((volume : Measure (Euc d)).prod volume) :=
    t012_prod_integrable hS.meas hS.nonneg (fun y => (hS.r_pos y).le) hS.k1 hl.measurable hli
      hμ.1.measurable hM0 (fun y => by rw [abs_of_nonneg (hμ.1.nonneg y)]; exact hμ.2 y)
  obtain ⟨hμl, hswap⟩ := t012_prod_swap_symm hS.symm hlμ
  have hdiff : Integrable (fun p : Euc d × Euc d => K p.1 p.2 * (l - μ) p.1 * (l - μ) p.2)
      ((volume : Measure (Euc d)).prod volume) := by
    have := ((hlK.sub hlμ).sub hμl).add hμμ
    refine this.congr (ae_of_all _ fun p => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  refine ⟨hlT, hμT, hdiff, ?_⟩
  -- expand the pairing energy of the difference
  have hexp : pairE K (l - μ) (l - μ) = pairE K l l - 2 * pairE K l μ + pairE K μ μ := by
    rw [t012_pairE_eq_prod hdiff, t012_pairE_eq_prod hlK, t012_pairE_eq_prod hlμ,
      t012_pairE_eq_prod hμμ]
    have h1 : ∫ p : Euc d × Euc d, K p.1 p.2 * (l - μ) p.1 * (l - μ) p.2
          ∂((volume : Measure (Euc d)).prod volume) =
        ∫ p : Euc d × Euc d, (K p.1 p.2 * l p.1 * l p.2 - K p.1 p.2 * l p.1 * μ p.2
          - K p.1 p.2 * μ p.1 * l p.2 + K p.1 p.2 * μ p.1 * μ p.2)
          ∂((volume : Measure (Euc d)).prod volume) := by
      refine integral_congr_ae (ae_of_all _ fun p => ?_)
      simp only [Pi.sub_apply]; ring
    have j1 : Integrable (fun p : Euc d × Euc d =>
        K p.1 p.2 * l p.1 * l p.2 - K p.1 p.2 * l p.1 * μ p.2)
        ((volume : Measure (Euc d)).prod volume) := hlK.sub hlμ
    have j2 : Integrable (fun p : Euc d × Euc d =>
        K p.1 p.2 * l p.1 * l p.2 - K p.1 p.2 * l p.1 * μ p.2 - K p.1 p.2 * μ p.1 * l p.2)
        ((volume : Measure (Euc d)).prod volume) :=
      j1.sub hμl
    rw [h1, integral_add j2 hμμ, integral_sub j1 hμl, integral_sub hlK hlμ, hswap]
    ring
  unfold Gfun
  rw [hlrel, hμrel, hexp]
  have hβne : β ≠ 0 := hβ.ne'
  field_simp
  ring

end Identity

end HRS.MS.Thm

end
