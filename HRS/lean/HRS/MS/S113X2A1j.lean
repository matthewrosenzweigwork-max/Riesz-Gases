import HRS.MS.S113X2A1i

/-!
# S11.3 X2 part A1j: slice subsolution inequality for the killed law at every pair of times
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

/-- **Every-time subsolution inequality.**  For `0 ≤ s ≤ t`, a smooth `φ ≥ 0` vanishing outside a compact collision-free set:
`ν_t(φ) ≤ ν_s(φ) + ∫_s^t ν_r(𝓛φ) dr`, with `ν_r` the killed law (`s113a_killedLaw`) and `𝓛φ = s113a_genx φ`. -/
theorem s113a_killed_slice_subsolution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s q β : ℝ} (hβ : 0 < β)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X)
    (D : Set (EucConfig d N)) (hD : IsOpen D)
    (chi : EucConfig d N → ℝ) (hchi : Measurable chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1)
    (phi : EucConfig d N → ℝ) (hphi : ContDiff ℝ ∞ phi) (hphi0 : ∀ x, 0 ≤ phi x)
    {K : Set (EucConfig d N)} (hKc : IsCompact K) (hKfree : ∀ x ∈ K, x ∉ eucCollisionSet d N)
    (hsupp : ∀ x, x ∉ K → phi x = 0) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Integrable (fun r : ℝ => ∫ x, s113a_genx d s q β N phi x ∂(s113a_killedLaw P D X₀ X chi r.toNNReal))
        (volume.restrict (Set.Ioo a b)) ∧
    ∫ x, phi x ∂(s113a_killedLaw P D X₀ X chi b.toNNReal) ≤
      ∫ x, phi x ∂(s113a_killedLaw P D X₀ X chi a.toNNReal) +
        ∫ r in Set.Ioo a b, ∫ x, s113a_genx d s q β N phi x ∂(s113a_killedLaw P D X₀ X chi r.toNNReal) := by
  classical
  obtain ⟨ℱ, W', hF, τ, hτ, hτg⟩ := s113a_setup hX D hD
  have hb0 : 0 ≤ b := ha.trans hab
  obtain ⟨Za, hZai, hZaeq, -, hZaae⟩ := s113a_Z_timeindep hβ ha hX hF D chi hchi hchi0 hchi1 hτ hτg phi
    hphi hKc hKfree hsupp
  obtain ⟨Zb, hZbi, hZbeq, hFint, hZbae⟩ := s113a_Z_timeindep hβ hb0 hX hF D chi hchi hchi0 hchi1 hτ hτg phi
    hphi hKc hKfree hsupp
  obtain ⟨C0, hC00, hC0b⟩ := s113a_bound_on_strip (N := N) hKc (F := fun p : ℝ × EucConfig d N => phi p.2)
    (hphi.continuous.comp continuous_snd) (fun r x hx => hsupp x hx) 0
  have hphib : ∀ x, |phi x| ≤ C0 := fun x => by
    have := hC0b 0 ⟨le_rfl, le_rfl⟩ x
    simpa using this
  have hsolb := hX.sol b
  -- integrals against the killed law
  have hfu : ∀ u : ℝ, 0 ≤ u → ∫ x, phi x ∂(s113a_killedLaw P D X₀ X chi u.toNNReal) =
      ∫ ζ, (if ((u : ℝ) : WithTop ℝ) < τ ζ then chi (X 0 ζ) * phi (X u.toNNReal ζ) else 0) ∂P := by
    intro u hu
    have hsol := hX.sol 0
    have h := s113a_killedLaw_integral P X₀ X (hsol.adapted 0) hsol.init D chi hchi hchi0 u.toNNReal
      (hsol.adapted _) τ
      ((s113a_measurableSet_lt_stopping hτ).preimage (measurable_prodMk_left (x := ((u.toNNReal : ℝ≥0) : ℝ))))
      (hτg.mono fun ζ h => h.1 u.toNNReal) phi hphi.continuous.measurable
    rw [h]
    simp only [Real.coe_toNNReal _ hu]
  have hmeas : ∀ u : ℝ, Measurable fun ζ =>
      (if ((u : ℝ) : WithTop ℝ) < τ ζ then chi (X 0 ζ) * phi (X u.toNNReal ζ) else 0) := by
    intro u
    have hXu : Measurable (X u.toNNReal) := (hX.sol 0).adapted _
    refine Measurable.ite ?_ ((hchi.comp ((hX.sol 0).adapted 0)).mul (hphi.continuous.measurable.comp hXu))
      measurable_const
    exact (s113a_measurableSet_lt_stopping hτ).preimage (measurable_prodMk_left (x := u))
  have hfint : ∀ u : ℝ, Integrable (fun ζ =>
      (if ((u : ℝ) : WithTop ℝ) < τ ζ then chi (X 0 ζ) * phi (X u.toNNReal ζ) else 0)) P := by
    intro u
    refine Integrable.of_bound (C := C0) (hmeas u).aestronglyMeasurable (ae_of_all _ fun ζ => ?_)
    split_ifs
    · rw [norm_mul, Real.norm_of_nonneg (hchi0 _)]
      calc chi (X 0 ζ) * ‖phi (X u.toNNReal ζ)‖ ≤ 1 * C0 :=
            mul_le_mul (hchi1 _) (by simpa using hphib _) (norm_nonneg _) zero_le_one
        _ = C0 := one_mul C0
    · simpa using hC00
  -- the pointwise comparison
  have hcmp : ∀ᵐ ζ ∂P,
      (if ((b : ℝ) : WithTop ℝ) < τ ζ then chi (X 0 ζ) * phi (X b.toNNReal ζ) else 0) -
        (if ((a : ℝ) : WithTop ℝ) < τ ζ then chi (X 0 ζ) * phi (X a.toNNReal ζ) else 0) ≤
      Zb ζ - Za ζ := by
    filter_upwards [hZaae, hZbae] with ζ h1 h2
    by_cases hbt : ((b : ℝ) : WithTop ℝ) < τ ζ
    · have hat : ((a : ℝ) : WithTop ℝ) < τ ζ := lt_of_le_of_lt (by exact_mod_cast hab) hbt
      rw [if_pos hbt, if_pos hat, h1.1 hat, h2.1 hbt]
    · rw [if_neg hbt]
      rw [not_lt] at hbt
      cases hc : τ ζ with
      | top => rw [hc] at hbt; exact absurd hbt (by simp)
      | coe c =>
        rw [hc] at hbt
        have hcb : c ≤ b := by exact_mod_cast hbt
        rw [h2.2 c hc hcb]
        by_cases hac : ((a : ℝ) : WithTop ℝ) < (c : WithTop ℝ)
        · rw [if_pos (by simpa [hc] using hac)]
          rw [h1.1 (by simpa [hc] using hac)]
          have : 0 ≤ chi (X 0 ζ) * phi (X c.toNNReal ζ) := mul_nonneg (hchi0 _) (hphi0 _)
          linarith
        · rw [if_neg (by simpa [hc] using hac)]
          have hca : c ≤ a := by
            rw [not_lt] at hac; exact_mod_cast hac
          rw [h1.2 c hc hca]; simp
  have hL : Integrable (fun ζ =>
      (if ((b : ℝ) : WithTop ℝ) < τ ζ then chi (X 0 ζ) * phi (X b.toNNReal ζ) else 0) -
        (if ((a : ℝ) : WithTop ℝ) < τ ζ then chi (X 0 ζ) * phi (X a.toNNReal ζ) else 0)) P :=
    (hfint b).sub (hfint a)
  have hR : Integrable (fun ζ => Zb ζ - Za ζ) P := hZbi.sub hZai
  have hmono := integral_mono_ae hL hR hcmp
  rw [integral_sub (hfint b) (hfint a), integral_sub hZbi hZai, hZbeq, hZaeq] at hmono
  have hsplit := s113a_integral_Ioo_split ha hab hFint
  refine ⟨hFint.mono_measure (Measure.restrict_mono (Set.Ioo_subset_Ioo ha le_rfl) le_rfl), ?_⟩
  rw [hfu b hb0, hfu a ha]
  linarith [hmono, hsplit]

end HRS.MS.S113X2

end
