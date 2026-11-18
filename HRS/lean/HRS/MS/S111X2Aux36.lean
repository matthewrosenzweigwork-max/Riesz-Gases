import HRS.MS.S111X2Aux35

/-!
# S11.1 X2, packet H01 (part 4): time increments of the orbit in the centered `L²(μ)` norm

`s111x2_orbit_incr`: for the classical solutions `f` (datum `φ`) and `h` (datum `Gφ`) on `[0,H]` and `0 ≤ τ₁ ≤ τ₂ ≤ H`,
`‖P_μ (f(H-τ₂) - f(H-τ₁))‖² ≤ (τ₂-τ₁)² η⁻² e^{2κ} e^{-2κτ₁} (‖P_μ φ‖² + ‖P_μ Gφ‖²)`
(mean value inequality for the `L²`-differentiable orbit with `∂_t F = G_t`, E07, and the decay of `G_t`, E08).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

theorem s111x2_orbit_incr (hd : 2 ≤ d) (s a β lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hβ : 0 < β) (hlam : 0 < lam) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ →
      IsR2Poincare (HRS.Whole.withDensityReal ρ) lam →
      ∀ H : ℝ, 0 < H → ∀ φ : Euc d → ℝ, MemCb 2 φ → ∀ f h : ℝ → Euc d → ℝ,
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H φ f →
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) H
          (generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 φ) h →
        ∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ H →
          s111x2_centeredSquare (HRS.Whole.withDensityReal ρ) (fun x => f (H - τ₂) x - f (H - τ₁) x) ≤
            (τ₂ - τ₁) ^ 2 * (η⁻¹ * η⁻¹ * Real.exp (2 * (lam / β)) * Real.exp (-2 * (lam / β) * τ₁) *
              (s111x2_centeredSquare (HRS.Whole.withDensityReal ρ) φ +
                s111x2_centeredSquare (HRS.Whole.withDensityReal ρ)
                  (generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 φ))) := by
  obtain ⟨η, hη0, hη1, hEn⟩ := s111x2_orbit_energy hd s a β lam hs0 hs ha hβ hlam
  refine ⟨η, hη0, hη1, fun ρ hρ hP H hH φ hφ f h hf hh τ₁ τ₂ h1 h12 h2H => ?_⟩
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := isProbabilityMeasure_nu T.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  obtain ⟨-, hder, -, -, -⟩ := s111x2_generator_orbit hd hs0 hs ha hβ hH hρ hφ hf hh
  obtain ⟨Bf0, Bf1, Bf2, hBf0, hBf1, hBf2, hfB⟩ := HRS.MS.S111X1.classical_bounds hf
  obtain ⟨Bh0, Bh1, Bh2, hBh0, hBh1, hBh2, hhB⟩ := HRS.MS.S111X1.classical_bounds hh
  have hrefl : ∀ r ∈ Icc (0 : ℝ) H, H - r ∈ Icc (0 : ℝ) H := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hmemf : ∀ r ∈ Icc (0 : ℝ) H, MemLp (f r) 2 μ := fun r hr =>
    MemLp.of_bound (hf.c2 r hr).continuous.aestronglyMeasurable Bf0
      (Filter.Eventually.of_forall fun x => (hfB r hr x).1) |>.mono_exponent le_top
  have hmemh : ∀ r ∈ Icc (0 : ℝ) H, MemLp (h r) 2 μ := fun r hr =>
    MemLp.of_bound (hh.c2 r hr).continuous.aestronglyMeasurable Bh0
      (Filter.Eventually.of_forall fun x => (hhB r hr x).1) |>.mono_exponent le_top
  set K : ℝ := η⁻¹ * η⁻¹ * Real.exp (2 * (lam / β)) * Real.exp (-2 * (lam / β) * τ₁) *
    (s111x2_centeredSquare μ φ + s111x2_centeredSquare μ (generatorW C 0 φ)) with hK
  have hK0 : 0 ≤ K := by
    have := s111x2_cs_nonneg μ φ
    have := s111x2_cs_nonneg μ (generatorW C 0 φ)
    positivity
  -- the centered `L²` class of the orbit
  set Φ : ℝ → Lp ℝ 2 μ := fun t => Pc μ (s111x2_toLp μ (f (H - t))) with hΦ
  have hcontw : ∀ x, ContinuousOn (fun q => f (H - q) x) (Icc 0 H) := by
    intro x
    have h0 := hf.cont_c2 0 (by norm_num)
    have h1' : Continuous fun r : Icc (0 : ℝ) H => iteratedFDeriv ℝ 0 (f r) x :=
      h0.comp (continuous_id.prodMk continuous_const)
    have h2' : Continuous fun r : Icc (0 : ℝ) H => f r x := by
      have := (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp h1'
      refine this.congr fun r => ?_
      simp [iteratedFDeriv_zero_eq_comp]
    have h3 : ContinuousOn (fun r => f r x) (Icc 0 H) := continuousOn_iff_continuous_restrict.2 h2'
    exact h3.comp (by fun_prop : ContinuousOn (fun q : ℝ => H - q) (Icc 0 H)) (fun r hr => hrefl r hr)
  have hΦc : ContinuousOn Φ (Icc 0 H) := by
    intro t ht
    have := s111x2_lp_continuousWithinAt (μ := μ) (w := fun q x => f (H - q) x) (G := fun _ => Bf0) ht
      (fun r' hr' => hmemf _ (hrefl r' hr')) hcontw
      (fun r' hr' x => by simpa using (hfB _ (hrefl r' hr') x).1) (memLp_const _)
    exact ((Pc μ).continuous.continuousAt.comp_continuousWithinAt this)
  have hΦd : ∀ t ∈ Ioo (0 : ℝ) H, HasDerivAt Φ (Pc μ (s111x2_toLp μ (h (H - t)))) t := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) H := ⟨ht.1.le, ht.2.le⟩
    have hlp := s111x2_lp_hasDerivAt (μ := μ) (w := fun q x => f (H - q) x) (w' := fun q x => h (H - q) x)
      (a := 0) (b := H) (A := Bh0) ht (fun r' hr' => hmemf _ (hrefl r' ⟨hr'.1.le, hr'.2.le⟩))
      (hmemh _ (hrefl t htI)) (fun x r' hr' => hder r' hr' x)
      (fun r' hr' x => by
        have := (hhB _ (hrefl r' ⟨hr'.1.le, hr'.2.le⟩) x).1
        rw [Real.norm_eq_abs] at this
        nlinarith [norm_nonneg x])
      (s111x2_lin_memLp T Bh0)
    exact (Pc μ).hasFDerivAt.comp_hasDerivAt t hlp
  -- derivative bound on `(τ₁,τ₂)`
  have hbd : ∀ t ∈ Ioo τ₁ τ₂, ‖Pc μ (s111x2_toLp μ (h (H - t)))‖ ≤ Real.sqrt K := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) H := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hmI := hmemh _ (hrefl t htI)
    have hcl : Pc μ (s111x2_toLp μ (h (H - t))) = s111x2_cl hmI := (s111x2_cl_eq_Pc hmI).symm
    rw [hcl]
    have hn := s111x2_cl_norm_sq hmI
    have hen := hEn ρ hρ hP H hH φ hφ f h hf hh t htI
    have hexp : Real.exp (-2 * (lam / β) * t) ≤ Real.exp (-2 * (lam / β) * τ₁) := by
      apply Real.exp_le_exp.2
      have : 0 ≤ lam / β := by positivity
      nlinarith [ht.1]
    have hle : s111x2_centeredSquare μ (h (H - t)) ≤ K := by
      refine hen.trans ?_
      have hq : 0 ≤ η⁻¹ * η⁻¹ * Real.exp (2 * (lam / β)) *
          (s111x2_centeredSquare μ φ + s111x2_centeredSquare μ (generatorW C 0 φ)) := by
        have := s111x2_cs_nonneg μ φ
        have := s111x2_cs_nonneg μ (generatorW C 0 φ)
        positivity
      calc η⁻¹ * η⁻¹ * Real.exp (2 * (lam / β)) * Real.exp (-2 * (lam / β) * t) *
            (s111x2_centeredSquare μ φ + s111x2_centeredSquare μ (generatorW C 0 φ))
          = (η⁻¹ * η⁻¹ * Real.exp (2 * (lam / β)) *
            (s111x2_centeredSquare μ φ + s111x2_centeredSquare μ (generatorW C 0 φ))) *
              Real.exp (-2 * (lam / β) * t) := by ring
        _ ≤ (η⁻¹ * η⁻¹ * Real.exp (2 * (lam / β)) *
            (s111x2_centeredSquare μ φ + s111x2_centeredSquare μ (generatorW C 0 φ))) *
              Real.exp (-2 * (lam / β) * τ₁) := mul_le_mul_of_nonneg_left hexp hq
        _ = K := by rw [hK]; ring
    rw [← Real.sqrt_sq (norm_nonneg (s111x2_cl hmI)), hn]
    exact Real.sqrt_le_sqrt hle
  -- Lipschitz on `(τ₁,τ₂)`, then on the closed interval
  have hsub : Ioo τ₁ τ₂ ⊆ Ioo 0 H := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hL : LipschitzOnWith (Real.sqrt K).toNNReal Φ (Ioo τ₁ τ₂) := by
    refine (convex_Ioo τ₁ τ₂).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (hΦd x (hsub hx)).hasDerivWithinAt) (fun x hx => ?_)
    rw [Real.le_toNNReal_iff_coe_le (Real.sqrt_nonneg _)]
    simpa using hbd x hx
  have hcontI : ContinuousOn Φ (Icc τ₁ τ₂) :=
    hΦc.mono (Icc_subset_Icc h1 h2H)
  rcases h12.eq_or_lt with heq | hlt
  · subst heq
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    simp [s111x2_centeredSquare, HRS.Whole.projMean, HRS.Whole.pair]
  have hcl : closure (Ioo τ₁ τ₂) = Icc τ₁ τ₂ := closure_Ioo hlt.ne
  have hL' : LipschitzOnWith (Real.sqrt K).toNNReal Φ (Icc τ₁ τ₂) := by
    rw [← hcl]
    exact LipschitzOnWith.closure (by rwa [hcl]) hL
  have hdist := hL'.dist_le_mul τ₂ ⟨h12, le_rfl⟩ τ₁ ⟨le_rfl, h12⟩
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.sqrt_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (by linarith)] at hdist
  -- the difference as a centered class
  have hm1 := hmemf _ (hrefl τ₁ ⟨h1, by linarith⟩)
  have hm2 := hmemf _ (hrefl τ₂ ⟨by linarith, h2H⟩)
  have e : (fun x => f (H - τ₂) x - f (H - τ₁) x) = f (H - τ₂) + (-1 : ℝ) • f (H - τ₁) := by
    funext x; simp [sub_eq_add_neg]
  rw [e]
  have hdiff : MemLp (f (H - τ₂) + (-1 : ℝ) • f (H - τ₁)) 2 μ := hm2.add (hm1.const_smul (-1))
  have hsubcl : s111x2_cl hdiff = Φ τ₂ - Φ τ₁ := by
    rw [s111x2_cl_lin hm2 hm1 (-1), s111x2_cl_eq_Pc hm2, s111x2_cl_eq_Pc hm1]
    simp [hΦ, sub_eq_add_neg]
  rw [← s111x2_cl_norm_sq hdiff, hsubcl]
  have hsq : ‖Φ τ₂ - Φ τ₁‖ ^ 2 ≤ (Real.sqrt K * (τ₂ - τ₁)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hdist 2
  calc ‖Φ τ₂ - Φ τ₁‖ ^ 2 ≤ (Real.sqrt K * (τ₂ - τ₁)) ^ 2 := hsq
    _ = (τ₂ - τ₁) ^ 2 * K := by
        rw [mul_pow, Real.sq_sqrt hK0]; ring

end HRS.MS.S111X2
