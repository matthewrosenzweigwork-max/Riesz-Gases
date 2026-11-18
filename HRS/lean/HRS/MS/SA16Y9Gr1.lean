import HRS.MS.SA16Y9Dj2

/-!
# S.A.16 (SA16Y9) Gr1: Gronwall with a source for the `p`-th power energy (stability, P2)

`sa16y9_gronwall_src`: if `e ≥ 0` is continuous on `[0,T]`, differentiable on `(0,T)` with
`e' ≤ c e + p e^{1-1/p} σ`, `0 ≤ σ ≤ s`, `c ≥ 0`, then `e(τ)^{1/p} ≤ e^{cτ/p}(e(0)^{1/p} + s τ)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.AppendixA.Phase2SA16S

lemma sa16y9_conj_inv (p : ℝ) (hp : 2 ≤ p) : 1 / Real.conjExponent p = 1 - 1 / p := by
  have hH := Real.HolderConjugate.conjExponent (show 1 < p by linarith)
  have := hH.inv_add_inv_eq_one
  rw [one_div, one_div]
  linarith

theorem sa16y9_gronwall_eps {T c s p : ℝ} (hp : 2 ≤ p) (hc : 0 ≤ c) (hs : 0 ≤ s) (e σ : ℝ → ℝ)
    (hcont : ContinuousOn e (Icc 0 T)) (he0 : ∀ τ ∈ Icc (0 : ℝ) T, 0 ≤ e τ)
    (hσ0 : ∀ τ ∈ Ioo (0 : ℝ) T, 0 ≤ σ τ) (hσ : ∀ τ ∈ Ioo (0 : ℝ) T, σ τ ≤ s)
    (hder : ∀ τ ∈ Ioo (0 : ℝ) T, ∃ e', HasDerivAt e e' τ ∧ e' ≤ c * e τ + p * (e τ ^ (1 - 1 / p) * σ τ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ τ ∈ Icc (0 : ℝ) T, (e τ + ε) ^ (1 / p) ≤ Real.exp (c / p * τ) * ((e 0 + ε) ^ (1 / p) + s * τ) := by
  have hp0 : 0 < p := by linarith
  set a : ℝ := c / p with ha
  have ha0 : 0 ≤ a := div_nonneg hc hp0.le
  set f : ℝ → ℝ := fun τ => (e τ + ε) ^ (1 / p) with hf
  set g : ℝ → ℝ := fun τ => Real.exp (-a * τ) * f τ - s * τ with hg
  have hpos : ∀ τ ∈ Icc (0 : ℝ) T, 0 < e τ + ε := fun τ hτ => by linarith [he0 τ hτ]
  have hfc : ContinuousOn f (Icc 0 T) := by
    refine ContinuousOn.rpow_const (hcont.add continuousOn_const) (fun τ hτ => Or.inl (hpos τ hτ).ne')
  have hgc : ContinuousOn g (Icc 0 T) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hfc).sub
      (continuous_const.mul continuous_id).continuousOn
  have hgd : ∀ τ ∈ Ioo (0 : ℝ) T, ∃ g', HasDerivAt g g' τ ∧ g' ≤ 0 := by
    intro τ hτ
    have hτc : τ ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hτ
    obtain ⟨e', he', hle⟩ := hder τ hτ
    have hpe := hpos τ hτc
    have hfd : HasDerivAt f (e' * (1 / p) * (e τ + ε) ^ (1 / p - 1)) τ :=
      (he'.add_const ε).rpow_const (Or.inl hpe.ne')
    have hgd : HasDerivAt g (Real.exp (-a * τ) * (e' * (1 / p) * (e τ + ε) ^ (1 / p - 1)) +
        (-a * Real.exp (-a * τ)) * f τ - s) τ := by
      have h1 : HasDerivAt (fun τ => Real.exp (-a * τ)) (Real.exp (-a * τ) * (-a * 1)) τ :=
        ((hasDerivAt_id' τ).const_mul (-a)).exp
      exact ((h1.mul hfd).sub ((hasDerivAt_id' τ).const_mul s)).congr_deriv (by ring)
    refine ⟨_, hgd, ?_⟩
    -- the bound on f'
    have hq : (e τ + ε) ^ (1 / p - 1) * (e τ + ε) = (e τ + ε) ^ (1 / p) := by
      rw [← Real.rpow_add_one hpe.ne']; congr 1; ring
    have hne : 0 ≤ e τ := he0 τ hτc
    have hA : (e τ + ε) ^ (1 / p - 1) * e τ ≤ f τ :=
      calc (e τ + ε) ^ (1 / p - 1) * e τ ≤ (e τ + ε) ^ (1 / p - 1) * (e τ + ε) :=
            mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hpe.le _)
        _ = f τ := hq
    have hB : (e τ + ε) ^ (1 / p - 1) * e τ ^ (1 - 1 / p) ≤ 1 := by
      have h1 : e τ ^ (1 - 1 / p) ≤ (e τ + ε) ^ (1 - 1 / p) :=
        Real.rpow_le_rpow hne (by linarith) (by rw [sub_nonneg]; exact (div_le_one hp0).2 (by linarith))
      calc (e τ + ε) ^ (1 / p - 1) * e τ ^ (1 - 1 / p) ≤ (e τ + ε) ^ (1 / p - 1) * (e τ + ε) ^ (1 - 1 / p) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hpe.le _)
        _ = 1 := by rw [← Real.rpow_add hpe]; simp
    have hσ1 := hσ0 τ hτ
    have hσ2 := hσ τ hτ
    have hexp : Real.exp (-a * τ) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hτ.1]
    have hd1 : e' * (1 / p) * (e τ + ε) ^ (1 / p - 1) ≤ a * f τ + σ τ := by
      have hwe : 0 ≤ (e τ + ε) ^ (1 / p - 1) := Real.rpow_nonneg hpe.le _
      calc e' * (1 / p) * (e τ + ε) ^ (1 / p - 1)
          = (1 / p) * (e' * (e τ + ε) ^ (1 / p - 1)) := by ring
        _ ≤ (1 / p) * ((c * e τ + p * (e τ ^ (1 - 1 / p) * σ τ)) * (e τ + ε) ^ (1 / p - 1)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle hwe) (by positivity)
        _ = a * ((e τ + ε) ^ (1 / p - 1) * e τ) + ((e τ + ε) ^ (1 / p - 1) * e τ ^ (1 - 1 / p)) * σ τ := by
            rw [ha]; field_simp
        _ ≤ a * f τ + 1 * σ τ := by
            gcongr
        _ = a * f τ + σ τ := by ring
    have hmul : Real.exp (-a * τ) * (e' * (1 / p) * (e τ + ε) ^ (1 / p - 1)) ≤
        Real.exp (-a * τ) * (a * f τ + σ τ) :=
      mul_le_mul_of_nonneg_left hd1 (Real.exp_pos _).le
    have : Real.exp (-a * τ) * (σ τ) ≤ s := by
      calc Real.exp (-a * τ) * σ τ ≤ 1 * s := mul_le_mul hexp hσ2 hσ1 zero_le_one
        _ = s := one_mul s
    nlinarith [Real.exp_pos (-a * τ)]
  have hanti : AntitoneOn g (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hgc ?_ ?_
    · intro τ hτ
      rw [interior_Icc] at hτ
      obtain ⟨g', hg', -⟩ := hgd τ hτ
      exact hg'.differentiableAt.differentiableWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      obtain ⟨g', hg', hle⟩ := hgd τ hτ
      rw [hg'.deriv]; exact hle
  intro τ hτ
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hτ.1.trans hτ.2⟩
  have := hanti h0 hτ hτ.1
  simp only [hg, mul_zero, Real.exp_zero, one_mul, sub_zero] at this
  have h2 : Real.exp (-a * τ) * f τ ≤ f 0 + s * τ := by linarith
  have h3 : f τ ≤ Real.exp (a * τ) * (f 0 + s * τ) := by
    calc f τ = Real.exp (a * τ) * (Real.exp (-a * τ) * f τ) := by
          rw [← mul_assoc, ← Real.exp_add]; simp
      _ ≤ Real.exp (a * τ) * (f 0 + s * τ) := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  exact h3

theorem sa16y9_gronwall_src {T c s p : ℝ} (hp : 2 ≤ p) (hc : 0 ≤ c) (hs : 0 ≤ s) (e σ : ℝ → ℝ)
    (hcont : ContinuousOn e (Icc 0 T)) (he0 : ∀ τ ∈ Icc (0 : ℝ) T, 0 ≤ e τ)
    (hσ0 : ∀ τ ∈ Ioo (0 : ℝ) T, 0 ≤ σ τ) (hσ : ∀ τ ∈ Ioo (0 : ℝ) T, σ τ ≤ s)
    (hder : ∀ τ ∈ Ioo (0 : ℝ) T, ∃ e', HasDerivAt e e' τ ∧ e' ≤ c * e τ + p * (e τ ^ (1 - 1 / p) * σ τ)) :
    ∀ τ ∈ Icc (0 : ℝ) T, e τ ^ (1 / p) ≤ Real.exp (c / p * τ) * (e 0 ^ (1 / p) + s * τ) := by
  intro τ hτ
  have hp0 : 0 < p := by linarith
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hτ.1.trans hτ.2⟩
  have hlim1 : Tendsto (fun ε : ℝ => (e τ + ε) ^ (1 / p)) (𝓝[>] 0) (𝓝 (e τ ^ (1 / p))) := by
    have : ContinuousAt (fun ε : ℝ => (e τ + ε) ^ (1 / p)) 0 := by
      refine ContinuousAt.rpow_const (continuousAt_const.add continuousAt_id) (Or.inr (by positivity))
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun ε : ℝ => Real.exp (c / p * τ) * ((e 0 + ε) ^ (1 / p) + s * τ)) (𝓝[>] 0)
      (𝓝 (Real.exp (c / p * τ) * (e 0 ^ (1 / p) + s * τ))) := by
    have : ContinuousAt (fun ε : ℝ => Real.exp (c / p * τ) * ((e 0 + ε) ^ (1 / p) + s * τ)) 0 := by
      refine continuousAt_const.mul (ContinuousAt.add ?_ continuousAt_const)
      exact ContinuousAt.rpow_const (continuousAt_const.add continuousAt_id) (Or.inr (by positivity))
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact sa16y9_gronwall_eps hp hc hs e σ hcont he0 hσ0 hσ hder hε τ hτ

end HRS.Whole.AppendixA.Phase2SA16S
