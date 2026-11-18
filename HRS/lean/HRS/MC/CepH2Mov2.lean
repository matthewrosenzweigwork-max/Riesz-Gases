import HRS.MC.CepH2Mov1
import HRS.MC.CepH2Loc2

/-!
# CEPH2, G2 (b): entropy and Fisher lower semicontinuity and monotonicity for the frozen potentials
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

section
variable {U : Ch N → ℝ} {Un : ℕ → Ch N → ℝ} {θ : ℝ} {c C : ℝ}

/-- Entropy lower semicontinuity, moving potential and moving measure. -/
theorem h2_entropy_lsc_moving (hUc : Continuous U) (hUnc : ∀ n, Continuous (Un n)) (hθ : 0 < θ)
    (hc : 0 < c) (hlow : ∀ n z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ Un n z)
    (hUnU : ∀ (n : ℕ) (z : Ch N), ‖h2_perp z‖ < (n : ℝ) → Un n z = U z)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {ν : Measure (Ch N)} {νn : ℕ → Measure (Ch N)} [IsProbabilityMeasure ν] [∀ n, IsProbabilityMeasure (νn n)]
    (hν : ν (cep_cell N)ᶜ = 0)
    (hconv : ∀ ψ : Ch N → ℝ, Continuous ψ → (∀ z, ψ (z + cep_diag N) = ψ z) → (∃ C, ∀ z, |ψ z| ≤ C) →
      Tendsto (fun n => ∫ z, ψ z ∂(νn n)) atTop (𝓝 (∫ z, ψ z ∂ν))) :
    cep_cylEntropy θ U ν ≤ liminf (fun n => cep_cylEntropy θ (Un n) (νn n)) atTop := by
  have hconfn : ∀ n, ∃ c' C' : ℝ, 0 < c' ∧ ∀ z, c' * Metric.infDist z (cep_Alcove N) ^ 2 - C' ≤ Un n z :=
    fun n => ⟨c, C, hc, hlow n⟩
  haveI := h2_cylRef_prob hUc hconf hθ
  haveI : ∀ n, IsProbabilityMeasure (cep_cylRef θ (Un n)) := fun n => h2_cylRef_prob (hUnc n) (hconfn n) hθ
  have hZ := h2_weight_lintegral_tendsto (θ := θ) hUc hUnc hθ hc hlow hUnU (f := fun _ => 1) measurable_const
    (M := 1) ENNReal.one_ne_top (fun _ => le_rfl)
  have hZ' : Tendsto (fun n => cep_cylPartition θ (Un n)) atTop (𝓝 (cep_cylPartition θ U)) := by
    simpa [cep_cylPartition] using hZ
  have hZne : cep_cylPartition θ U ≠ ⊤ := (h2_partition_lt_top hconf hθ).ne
  have hZ0 : cep_cylPartition θ U ≠ 0 := (h2_partition_pos hUc θ).ne'
  have hZr : Tendsto (fun n => (cep_cylPartition θ (Un n)).toReal) atTop (𝓝 (cep_cylPartition θ U).toReal) :=
    (ENNReal.tendsto_toReal hZne).comp hZ'
  have hLr : Tendsto (fun n => Real.log (cep_cylPartition θ (Un n)).toReal) atTop
      (𝓝 (Real.log (cep_cylPartition θ U).toReal)) :=
    hZr.log (ENNReal.toReal_pos hZ0 hZne).ne'
  have hkl : klDiv ν (cep_cylRef θ U) ≤ liminf (fun n => klDiv (νn n) (cep_cylRef θ (Un n))) atTop :=
    h2_klDiv_liminf_moving hν (h2_cylRef_compl hUc θ) hconv (fun ψ hψ hb => by
      obtain ⟨C0, hC0⟩ := hb
      exact h2_ref_tendsto hUc hUnc hθ hc hlow hUnU hconf hψ.measurable hC0)
  have hsub := h2_liminf_sub_moving (fun n => klDiv (νn n) (cep_cylRef θ (Un n)))
    (fun n => Real.log (cep_cylPartition θ (Un n)).toReal) _ hLr
  unfold cep_cylEntropy relEntropy
  refine le_trans ?_ hsub
  have hmono : Monotone (fun x : ℝ≥0∞ => (x : EReal) - ((Real.log (cep_cylPartition θ U).toReal : ℝ) : EReal)) :=
    fun x y hxy => by
      show (x : EReal) - _ ≤ (y : EReal) - _
      rw [sub_eq_add_neg, sub_eq_add_neg]
      exact add_le_add_left (EReal.coe_ennreal_le_coe_ennreal_iff.2 hxy) _
  exact hmono hkl

theorem h2_fint_eq_of_near {V W : Ch N → ℝ} {ζ : Ch N → Ch N} {R n : ℝ} (hRn : R < n)
    (hfar : ∀ z, R < ‖h2_perp z‖ → ζ z = 0)
    (hVW : ∀ z, ‖h2_perp z‖ < n → gradient V z = gradient W z) (z : Ch N) :
    h2_fint θ V ζ z = h2_fint θ W ζ z := by
  by_cases hz : ‖h2_perp z‖ < n
  · unfold h2_fint
    rw [hVW z hz]
  · have : ζ z = 0 := hfar z (lt_of_lt_of_le hRn (not_lt.1 hz))
    unfold h2_fint
    rw [this]
    simp

/-- Fisher information lower semicontinuity, moving potential and moving measure. -/
theorem h2_fisher_lsc_moving (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z)
    (hUnU : ∀ (n : ℕ) (z : Ch N), ‖h2_perp z‖ < (n : ℝ) → Un n z = U z)
    {ν : Measure (Ch N)} {νn : ℕ → Measure (Ch N)} [IsProbabilityMeasure ν] [∀ n, IsProbabilityMeasure (νn n)]
    (hconv : ∀ ψ : Ch N → ℝ, Continuous ψ → (∀ z, ψ (z + cep_diag N) = ψ z) → (∃ C, ∀ z, |ψ z| ≤ C) →
      Tendsto (fun n => ∫ z, ψ z ∂(νn n)) atTop (𝓝 (∫ z, ψ z ∂ν))) :
    cep_cylFisher θ U ν ≤ liminf (fun n => cep_cylFisher θ (Un n) (νn n)) atTop := by
  unfold cep_cylFisher
  refine iSup_le fun ζ => iSup_le fun hζ' => ?_
  obtain ⟨hζ, hper, hR⟩ := hζ'
  obtain ⟨R', hfar⟩ := h2_zeta_far hR
  obtain ⟨C0, hC0⟩ := h2_fint_bdd hU hUper θ hζ hper hfar
  have hψ := h2_fint_continuous hU θ hζ
  have hψper := fun z => h2_fint_periodic hUper θ hper z
  have hlim := hconv _ hψ hψper ⟨C0, hC0⟩
  have hlim' : Tendsto (fun n => ENNReal.ofReal (∫ z, h2_fint θ U ζ z ∂(νn n))) atTop
      (𝓝 (ENNReal.ofReal (∫ z, h2_fint θ U ζ z ∂ν))) := ENNReal.tendsto_ofReal hlim
  change ENNReal.ofReal (∫ z, h2_fint θ U ζ z ∂ν) ≤ _
  rw [← hlim'.liminf_eq]
  refine liminf_le_liminf ?_
  obtain ⟨n0, hn0⟩ := exists_nat_gt R'
  filter_upwards [eventually_ge_atTop n0] with n hn
  have hRn : R' < (n : ℝ) := lt_of_lt_of_le hn0 (by exact_mod_cast hn)
  have hgrad : ∀ z, ‖h2_perp z‖ < (n : ℝ) → gradient U z = gradient (Un n) z := by
    intro z hz
    have hopen : IsOpen {z : Ch N | ‖h2_perp z‖ < (n : ℝ)} :=
      isOpen_lt (h2_continuous_perp.norm) continuous_const
    have hev' : Un n =ᶠ[𝓝 z] U :=
      Filter.mem_of_superset (hopen.mem_nhds hz) fun z hz => hUnU n z hz
    exact h2_gradient_eq_of_eq_near hev'.symm
  have heq : h2_fint θ (Un n) ζ = h2_fint θ U ζ := by
    funext z
    exact (h2_fint_eq_of_near hRn hfar hgrad z).symm
  rw [← heq]
  exact le_iSup₂_of_le ζ ⟨hζ, hper, hR⟩ le_rfl

/-- Monotonicity of the entropy in the potential, for measures of finite entropy. -/
theorem h2_entropy_mono (hU : ContDiff ℝ 1 U)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z) (hθ : 0 < θ)
    {V : Ch N → ℝ} (hVc : Continuous V) (hVle : ∀ z, V z ≤ U z)
    (hVconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ V z)
    {μ : Measure (Ch N)} [IsProbabilityMeasure μ] (hfin : cep_cylEntropy θ U μ < ⊤) :
    cep_cylEntropy θ V μ ≤ cep_cylEntropy θ U μ := by
  have hrel := h2_relEntropy_ne_top hfin
  unfold relEntropy at hrel
  obtain ⟨hcell, hm0⟩ := cepH2_moment_init_proof hU hconf hθ hfin
  have hmom := h2_integrable_moment_of_lintegral hm0
  obtain ⟨ρ, hρ, hρ0, hμeq, hρ1, hΦ⟩ := h2_density_of_finite hU.continuous hconf hθ hrel
  have hH := h2_cylEntropy_density hU.continuous hconf hθ hρ hρ0 hρ1 hΦ
  rw [hμeq] at hmom ⊢
  obtain ⟨hρU, hρlog⟩ := h2_density_Uint hU.continuous hconf hθ hρ hρ0 hρ1 hΦ hmom
  have hρi := h2_integrable_of_lintegral hρ hρ0 hρ1
  obtain ⟨c, C, hc, hVl⟩ := id hVconf
  have hVlow : ∀ z, -|C| ≤ V z := fun z => by
    have : 0 ≤ c * Metric.infDist z (cep_Alcove N) ^ 2 := by positivity
    linarith [hVl z, le_abs_self C]
  have hρV : Integrable (fun x => ρ x * V x) (volume.restrict (cep_cell N)) := by
    refine Integrable.mono' ((hρU.abs).add (hρi.const_mul |C|)) (hρ.mul hVc.measurable).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    have h1 : |V x| ≤ |U x| + |C| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (U x), hVlow x, abs_nonneg (U x), abs_nonneg C]
      · linarith [le_abs_self (U x), hVle x, hVlow x, abs_nonneg (U x), abs_nonneg C]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 x)]
    have : |ρ x * U x| = ρ x * |U x| := by rw [abs_mul, abs_of_nonneg (hρ0 x)]
    show ρ x * |V x| ≤ |ρ x * U x| + |C| * ρ x
    rw [this]
    nlinarith [hρ0 x]
  have hΦV : Integrable (fun x => ρ x * Real.log (ρ x) + ρ x * V x / θ) (volume.restrict (cep_cell N)) := by
    have := hρlog.add (hρV.div_const θ)
    exact this
  have hHV := h2_cylEntropy_density hVc hVconf hθ hρ hρ0 hρ1 hΦV
  rw [hHV, hH]
  refine EReal.coe_le_coe_iff.2 (integral_mono hΦV hΦ fun x => ?_)
  have : ρ x * V x / θ ≤ ρ x * U x / θ :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hVle x) (hρ0 x)) hθ.le
  linarith

end

end HRS.MC.CepH2
