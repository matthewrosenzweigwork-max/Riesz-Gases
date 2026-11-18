import HRS.ME.UnifP1A

/-!
# Uniform pressure bounds under a sup bound on the density (packet P1)

`perturbed_pressure_sup`: the hypothesis `∀ k, cbNorm k ρ ≤ Λ k` of `HRS.perturbed_pressure` is replaced
by the sup bound `∀ x, ρ x ≤ Λ` (the original proofs use `Λ 0` only, through `le_cbNorm_zero`).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.ME.Unif

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
/-- The two-sided pressure bound `|log K^{g-θh}| ≤ C N δ_N` of Proposition 5.5, uniformly over the
family of backgrounds and kernels; the first display `N:eq:pressure-main`. -/
theorem pressure_two_sided (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ : ℝ) (B : ℝ) :
    ∃ θ₀ C : ℝ, 0 < θ₀ ∧ 0 ≤ C ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsSmooth ρ → (∀ x, c₀ ≤ ρ x) →
        (∀ x, ρ x ≤ Λ) →
      ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
        (∀ x y, |h x y| ≤ B * (periodicRiesz d s (x - y) + cstar)) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp, ∀ θ : ℝ, |θ| ≤ θ₀ →
          ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤
              ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => periodicRiesz d s (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ∧
          ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => periodicRiesz d s (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ≤
            ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  obtain ⟨g, hg⟩ : ∃ g : Torus d → ℝ, g = periodicRiesz d s := ⟨_, rfl⟩
  rw [← hg] at hw ⊢
  -- the shifted constant `cs ≥ c_*` with `w ≥ 1` everywhere
  obtain ⟨g0, hg0⟩ : ∃ g0 : ℝ, g0 = g 0 := ⟨_, rfl⟩
  obtain ⟨cs, hcsdef⟩ : ∃ cs : ℝ, cs = max cstar (1 - g0) := ⟨_, rfl⟩
  have hcs : ∀ z : Torus d, 1 ≤ g z + cs := by
    intro z
    by_cases hz : z = 0
    · subst hz
      have : 1 - g0 ≤ cs := by rw [hcsdef]; exact le_max_right _ _
      linarith
    · have := hw z hz; have : cstar ≤ cs := by rw [hcsdef]; exact le_max_left _ _
      linarith
  have hcstar : cstar ≤ cs := by rw [hcsdef]; exact le_max_left _ _
  obtain ⟨B', hB'def⟩ : ∃ B' : ℝ, B' = max B 0 := ⟨_, rfl⟩
  have hB' : 0 ≤ B' := by rw [hB'def]; exact le_max_right _ _
  have hgm : Measurable g := by rw [hg]; exact CoercAux.measurable_periodicRiesz_one hd hs0 hsd
  have hgi : Integrable g := by rw [hg]; exact CoercAux.integrable_periodicRiesz_one hd hs0 hsd
  have hwi : Integrable (fun z => g z + cs) := hgi.add (integrable_const cs)
  obtain ⟨Mw, hMw⟩ : ∃ Mw : ℝ, Mw = ∫ z, (g z + cs) := ⟨_, rfl⟩
  have hMw0 : 0 ≤ Mw := by
    rw [hMw]; exact integral_nonneg fun z => by show 0 ≤ g z + cs; linarith [hcs z]
  rw [hg] at hcs
  obtain ⟨E₀, hE₀, hspl⟩ := uniformSplit hd hs0 hsd cs hcs
  rw [← hg] at hcs hspl
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = E₀ + B' + 1 := ⟨_, rfl⟩
  obtain ⟨a₀, Cw, ha₀, hweak⟩ := weak_reference_pressure hd s hs0 hsd cs
    (fun z _ => by have := hcs z; rw [hg] at this; exact this) βm βp hβm c₀ hc₀ Λ A
  rw [← hg] at hweak
  obtain ⟨Λ0, hΛ0def⟩ : ∃ Λ0 : ℝ, Λ0 = max Λ 0 := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ0 := by rw [hΛ0def]; exact le_max_right _ _
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min 1 (a₀ / (4 * (Λ0 + 1))) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := by rw [hεdef]; exact min_le_left _ _
  have hεa : Λ0 * ε ≤ a₀ / 4 := by
    have h1 : ε ≤ a₀ / (4 * (Λ0 + 1)) := by rw [hεdef]; exact min_le_right _ _
    calc Λ0 * ε ≤ Λ0 * (a₀ / (4 * (Λ0 + 1))) := mul_le_mul_of_nonneg_left h1 hΛ0
      _ ≤ (Λ0 + 1) * (a₀ / (4 * (Λ0 + 1))) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = a₀ / 4 := by field_simp
  obtain ⟨Λf, af, q, c, haf, hqm, hq0, hqev, hqint, hqε, hc0, hsplit, hqenv⟩ := hspl ε hε hε1
  obtain ⟨Sa, hSa⟩ : ∃ Sa : ℝ, Sa = ∑ k ∈ Λf, af k := ⟨_, rfl⟩
  have hSa0 : 0 ≤ Sa := by rw [hSa]; exact Finset.sum_nonneg haf
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = B' * (Sa + |g0| + |cs|) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = B' * Mw + D := ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  obtain ⟨θ₀, hθ₀def⟩ : ∃ θ₀ : ℝ, θ₀ = min 1 (min (1 / (2 * B' + 1))
      (min (1 / (D + 1)) (a₀ / (4 * (Λ0 + 1) * (Kc + 1))))) := ⟨_, rfl⟩
  have hθ₀pos : 0 < θ₀ := by
    rw [hθ₀def]; exact lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hθ1 : θ₀ ≤ 1 := by rw [hθ₀def]; exact min_le_left _ _
  have hθB : θ₀ * B' ≤ 1 / 2 := by
    have : θ₀ ≤ 1 / (2 * B' + 1) := by
      rw [hθ₀def]; exact (min_le_right _ _).trans (min_le_left _ _)
    calc θ₀ * B' ≤ (1 / (2 * B' + 1)) * B' := mul_le_mul_of_nonneg_right this hB'
      _ ≤ 1 / 2 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have hθD : θ₀ * D ≤ 1 := by
    have : θ₀ ≤ 1 / (D + 1) := by
      rw [hθ₀def]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    calc θ₀ * D ≤ (1 / (D + 1)) * D := mul_le_mul_of_nonneg_right this hD0
      _ ≤ 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
          linarith
  have hθK : Λ0 * (θ₀ * Kc) ≤ a₀ / 4 := by
    have : θ₀ ≤ a₀ / (4 * (Λ0 + 1) * (Kc + 1)) := by
      rw [hθ₀def]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    calc Λ0 * (θ₀ * Kc) ≤ Λ0 * ((a₀ / (4 * (Λ0 + 1) * (Kc + 1))) * Kc) := by
          apply mul_le_mul_of_nonneg_left _ hΛ0
          exact mul_le_mul_of_nonneg_right this hKc0
      _ ≤ (Λ0 + 1) * ((a₀ / (4 * (Λ0 + 1) * (Kc + 1))) * (Kc + 1)) := by
          have h1 : 0 ≤ a₀ / (4 * (Λ0 + 1) * (Kc + 1)) := by positivity
          apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) h1
      _ = a₀ / 4 := by field_simp
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = Λ0 * ∫ z, (|g z| + B' * (g z + cs)) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg hΛ0 (integral_nonneg fun z => by
      show 0 ≤ |g z| + B' * (g z + cs)
      have := hcs z
      have : 0 ≤ B' * (g z + cs) := mul_nonneg hB' (by linarith)
      positivity)
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (|βp| * Sa / 2 + |Cw|) (|βp| * M / 2) := ⟨_, rfl⟩
  have hC1 : |βp| * Sa / 2 + |Cw| ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hC2 : |βp| * M / 2 ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hC0 : 0 ≤ C := le_trans (by positivity) hC1
  refine ⟨θ₀, C, hθ₀pos, hC0, ?_⟩
  intro ρ hρ hsm hlow hcb h hhm hsym hdom N hN β hβ θ hθ
  have hN1 : 1 ≤ N := by omega
  have hβ0 : 0 ≤ β := (hβm.trans_le hβ.1).le
  haveI hμprob : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hρΛ : ∀ x, ρ x ≤ Λ0 := fun x =>
    (hcb x).trans (hΛ0def ▸ le_max_left _ _)
  have hρm : Measurable ρ := hρ.measurable
  have hδ : 1 ≤ (N : ℝ) * deltaN d s N := one_le_mul_deltaN hs0 N hN1
  have hT : 0 ≤ (N : ℝ) * deltaN d s N := by linarith
  have hθ' : |θ| ≤ 1 := hθ.trans hθ1
  have hmeas2 : ∀ {f : Torus d → ℝ}, Measurable f → Measurable (Function.uncurry fun x y : Torus d => f (x - y)) :=
    fun hf => hf.comp (measurable_fst.sub measurable_snd)
  -- the envelope of `h` and its row bound
  have hhdom : ∀ x y, |h x y| ≤ B' * (g (x - y) + cs) := by
    rw [hB'def]; exact dom_max hd hcstar hw hdom
  have hwint : Integrable (fun z => B' * (g z + cs)) := hwi.const_mul B'
  have hhR : RowOK (withDensityReal ρ) h := (rowOK_of_dom hΛ0 hρΛ hwint hhm hhdom).1
  have hgR : RowOK (withDensityReal ρ) (fun x y => g (x - y)) :=
    (rowOK_of_dom hΛ0 hρΛ hgi.abs (hmeas2 hgm) (fun x y => le_rfl)).1
  have hqR : RowOK (withDensityReal ρ) (fun x y => q (x - y)) :=
    (rowOK_of_dom hΛ0 hρΛ hqint (hmeas2 hqm) (fun x y => by rw [abs_of_nonneg (hq0 _)])).1
  have hcosle : ∀ z : Torus d, |∑ k ∈ Λf, af k * Torus.cosMode k z| ≤ Sa := by
    intro z
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hSa]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [abs_mul, abs_of_nonneg (haf k hk)]
    exact mul_le_of_le_one_right (haf k hk) (abs_cosMode_le k z)
  have hcosm : Measurable (fun z : Torus d => ∑ k ∈ Λf, af k * Torus.cosMode k z) :=
    Finset.measurable_sum _ fun k _ => measurable_const.mul (Torus.continuous_cosMode k).measurable
  have hgLR : RowOK (withDensityReal ρ) (fun x y => ∑ k ∈ Λf, af k * Torus.cosMode k (x - y)) :=
    (rowOK_of_dom hΛ0 hρΛ (integrable_const Sa) (hmeas2 hcosm) (fun x y => hcosle _)).1
  have hsplit' : ∀ x : Torus d, x ≠ 0 → g x = ∑ k ∈ Λf, af k * Torus.cosMode k x + q x - c := hsplit
  have henv : ∀ x y, |h x y| ≤ B' * q (x - y) + D := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      have h1 := hhdom x x
      rw [sub_self] at h1
      have h2 : g 0 + cs ≤ |g0| + |cs| := by
        rw [← hg0]; exact add_le_add (le_abs_self _) (le_abs_self _)
      have h3 : B' * (g 0 + cs) ≤ B' * (|g0| + |cs|) := mul_le_mul_of_nonneg_left h2 hB'
      have h4 : 0 ≤ B' * q 0 := mul_nonneg hB' (hq0 _)
      have h5 : B' * (|g0| + |cs|) ≤ D := by
        rw [hD]; exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg g0, abs_nonneg cs]) hB'
      rw [sub_self]; linarith
    · have h1 := hhdom x y
      have h2 := hsplit' (x - y) (sub_ne_zero.2 hxy)
      have h3 := le_abs_self (∑ k ∈ Λf, af k * Torus.cosMode k (x - y))
      have h4 := hcosle (x - y)
      have h5 : g (x - y) + cs ≤ q (x - y) + (Sa + |cs|) := by
        have := le_abs_self cs
        have := (le_abs_self _ : (∑ k ∈ Λf, af k * Torus.cosMode k (x - y)) ≤ _)
        linarith
      have h6 : B' * (g (x - y) + cs) ≤ B' * (q (x - y) + (Sa + |cs|)) :=
        mul_le_mul_of_nonneg_left h5 hB'
      have h7 : B' * (Sa + |cs|) ≤ D := by
        rw [hD]; exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg g0]) hB'
      nlinarith
  -- the weak kernel `q_θ = q - θ h + |θ| D`
  have hθB' : |θ| * B' ≤ 1 / 2 := (mul_le_mul_of_nonneg_right hθ hB').trans hθB
  have hθD' : |θ| * D ≤ 1 := (mul_le_mul_of_nonneg_right hθ hD0).trans hθD
  obtain ⟨qθ, hqθdef⟩ : ∃ qθ : Torus d → Torus d → ℝ, qθ = fun x y => q (x - y) - θ * h x y + |θ| * D :=
    ⟨_, rfl⟩
  have hqθ0 : ∀ x y, 0 ≤ qθ x y := by
    intro x y; rw [hqθdef]; exact qTheta_nonneg hq0 henv hθB' x y
  have hqθsym : ∀ x y, qθ x y = qθ y x := by
    intro x y
    rw [hqθdef]
    simp only
    rw [hsym x y, ← hqev (x - y), neg_sub]
  have hqθm : Measurable (Function.uncurry qθ) := by
    rw [hqθdef]
    exact (((hmeas2 hqm).sub (measurable_const.mul hhm)).add measurable_const)
  have hqθA : ∀ x y, qθ x y ≤ A * (g (x - y) + cs) := by
    intro x y; rw [hqθdef, hA]
    exact qTheta_le hB' hD0 hE₀ hcs hqenv hhdom hθ' hθD' x y
  obtain ⟨Wθ, hWθdef⟩ : ∃ Wθ : Torus d → ℝ,
      Wθ = fun z => q z + |θ| * (B' * (g z + cs)) + |θ| * D := ⟨_, rfl⟩
  have h1w : Integrable (fun z => |θ| * (B' * (g z + cs))) := hwint.const_mul _
  have h2w : Integrable (fun z => q z + |θ| * (B' * (g z + cs))) := hqint.add h1w
  have hWθint : Integrable Wθ := by
    have h3 : Integrable (fun z => q z + |θ| * (B' * (g z + cs)) + |θ| * D) :=
      h2w.add (integrable_const (|θ| * D))
    rw [hWθdef]; exact h3
  have hdomθ : ∀ x y, |qθ x y| ≤ Wθ (x - y) := by
    intro x y
    rw [abs_of_nonneg (hqθ0 x y), hqθdef, hWθdef]
    simp only
    have h1 := hhdom x y
    have h2 : -(θ * h x y) ≤ |θ| * (B' * (g (x - y) + cs)) := by
      calc -(θ * h x y) ≤ |θ * h x y| := neg_le_abs _
        _ = |θ| * |h x y| := abs_mul _ _
        _ ≤ |θ| * (B' * (g (x - y) + cs)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    linarith
  obtain ⟨hqθR, hrowbd⟩ := rowOK_of_dom hΛ0 hρΛ hWθint hqθm hdomθ
  have hintW : ∫ z, Wθ z = (∫ z, q z) + |θ| * Kc := by
    have e1 : ∫ z, (q z + |θ| * (B' * (g z + cs)) + |θ| * D) =
        (∫ z, (q z + |θ| * (B' * (g z + cs)))) + ∫ _z : Torus d, |θ| * D :=
      integral_add h2w (integrable_const _)
    have e2 : ∫ z, (q z + |θ| * (B' * (g z + cs))) =
        (∫ z, q z) + ∫ z, |θ| * (B' * (g z + cs)) := integral_add hqint h1w
    have e3 : ∫ z, |θ| * (B' * (g z + cs)) = |θ| * (B' * Mw) := by
      rw [integral_const_mul, integral_const_mul, hMw]
    have e4 : ∫ _z : Torus d, |θ| * D = |θ| * D := by simp
    rw [hWθdef, hKc]
    show ∫ z, (q z + |θ| * (B' * (g z + cs)) + |θ| * D) = _
    rw [e1, e2, e3, e4]; ring
  have hrowR : ∀ x, ∫ y, qθ x y ∂(withDensityReal ρ) ≤ a₀ / 2 := by
    intro x
    have h1 : ∫ y, qθ x y ∂(withDensityReal ρ) ≤ ∫ y, |qθ x y| ∂(withDensityReal ρ) :=
      integral_mono (hqθR.int x) (hqθR.int x).abs (fun y => le_abs_self _)
    have h2 := hrowbd x
    rw [hintW] at h2
    have h3 : Λ0 * ((∫ z, q z) + |θ| * Kc) ≤ a₀ / 4 + a₀ / 4 := by
      have h4 : Λ0 * (∫ z, q z) ≤ Λ0 * ε := mul_le_mul_of_nonneg_left hqε hΛ0
      have h5 : Λ0 * (|θ| * Kc) ≤ Λ0 * (θ₀ * Kc) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hθ hKc0) hΛ0
      nlinarith
    linarith
  have hrowL : ∀ x, ∫⁻ y, ENNReal.ofReal (qθ x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (a₀ / 2) := by
    intro x
    rw [← ofReal_integral_eq_lintegral_ofReal (hqθR.int x) (Filter.Eventually.of_forall fun y => hqθ0 x y)]
    exact ENNReal.ofReal_le_ofReal (hrowR x)
  have hW := hweak ρ hρ hsm hlow hcb qθ hqθm hqθsym hqθ0 hqθA (a₀ / 2) (by positivity)
    (by linarith) hrowL N hN β hβ
  have hμ0 : ∀ x, withDensityReal ρ {x} = 0 := withDensityReal_singleton hd ρ
  have hβp : β ≤ |βp| := hβ.2.trans (le_abs_self _)
  refine ⟨?_, ?_⟩
  · -- lower bound (Jensen)
    have hkdom : ∀ x y, |g (x - y) - θ * h x y| ≤ (fun z => |g z| + B' * (g z + cs)) (x - y) := by
      intro x y
      simp only
      have h1 := hhdom x y
      calc |g (x - y) - θ * h x y| ≤ |g (x - y)| + |θ * h x y| := abs_sub _ _
        _ ≤ |g (x - y)| + B' * (g (x - y) + cs) := by
            refine add_le_add le_rfl ?_
            rw [abs_mul]
            calc |θ| * |h x y| ≤ 1 * |h x y| := mul_le_mul_of_nonneg_right hθ' (abs_nonneg _)
              _ ≤ _ := by rw [one_mul]; exact h1
    have hWint : Integrable (fun z => |g z| + B' * (g z + cs)) := hgi.abs.add hwint
    have hkm : Measurable (Function.uncurry fun x y : Torus d => g (x - y) - θ * h x y) := by
      show Measurable (fun p : Torus d × Torus d => g (p.1 - p.2) - θ * h p.1 p.2)
      exact (hgm.comp (measurable_fst.sub measurable_snd)).sub
        ((measurable_const (a := θ)).mul hhm)
    obtain ⟨hkR, hkbd⟩ := rowOK_of_dom hΛ0 hρΛ hWint hkm hkdom
    have hlow' := pressure_lower_core (N := N) hkR (M := M) (fun x => by rw [hMdef]; exact hkbd x) hN1 hβ0
    refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) hlow'
    have h1 : β * M / 2 ≤ |βp| * M / 2 := by
      have := mul_le_mul_of_nonneg_right hβp hM0
      linarith
    have h2 : |βp| * M / 2 * 1 ≤ |βp| * M / 2 * ((N : ℝ) * deltaN d s N) :=
      mul_le_mul_of_nonneg_left hδ (by positivity)
    have h3 : C * 1 ≤ C * ((N : ℝ) * deltaN d s N) := mul_le_mul_of_nonneg_left hδ hC0
    have h4 : C * N * deltaN d s N = C * ((N : ℝ) * deltaN d s N) := by ring
    rw [h4]
    nlinarith
  · -- upper bound: discard the positive-definite part and use Lemma 5.7
    have hup := pressure_upper_core (N := N) hμ0 Λf af haf g q c hc0 hsplit' hgLR hqR hhR θ D hD0 hN1 hβ0
    rw [← hSa] at hup
    refine hup.trans ?_
    rw [← hqθdef]
    refine (mul_le_mul' le_rfl hW.2).trans ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 : β * Sa / 2 ≤ |βp| * Sa / 2 := by
      have := mul_le_mul_of_nonneg_right hβp hSa0
      linarith
    have h2 : (|βp| * Sa / 2 + |Cw|) * 1 ≤ (|βp| * Sa / 2 + |Cw|) * ((N : ℝ) * deltaN d s N) :=
      mul_le_mul_of_nonneg_left hδ (by positivity)
    have h3 : C * 1 ≤ C * ((N : ℝ) * deltaN d s N) := mul_le_mul_of_nonneg_left hδ hC0
    have h4 : C * N * deltaN d s N = C * ((N : ℝ) * deltaN d s N) := by ring
    have h5 : Cw * N * deltaN d s N ≤ |Cw| * ((N : ℝ) * deltaN d s N) := by
      have : Cw * N * deltaN d s N = Cw * ((N : ℝ) * deltaN d s N) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hT
    have h6 : β * Sa / 2 ≤ |βp| * Sa / 2 * ((N : ℝ) * deltaN d s N) := by
      have : |βp| * Sa / 2 * 1 ≤ |βp| * Sa / 2 * ((N : ℝ) * deltaN d s N) :=
        mul_le_mul_of_nonneg_left hδ (by positivity)
      linarith
    rw [h4]
    nlinarith


/-- Proposition 5.5 `N:prop:pressure`, all three displays, uniformly over a bounded smooth positive
family of backgrounds and over a compact positive temperature interval. -/
theorem perturbed_pressure_sup (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ : ℝ) (B : ℝ) :
    ∃ θ₀ θ₁ C : ℝ, 0 < θ₀ ∧ 0 < θ₁ ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsSmooth ρ → (∀ x, c₀ ≤ ρ x) →
        (∀ x, ρ x ≤ Λ) →
      ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
        (∀ x y, |h x y| ≤ B * (periodicRiesz d s (x - y) + cstar)) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp,
        (∀ θ : ℝ, |θ| ≤ θ₀ →
          ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤
              ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => periodicRiesz d s (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ∧
          ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => periodicRiesz d s (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ≤
            ENNReal.ofReal (Real.exp (C * N * deltaN d s N))) ∧
        (∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (θ₁ * N *
              |modulatedEnergy h X (withDensityReal ρ)|))
            ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (Real.exp (C * N * deltaN d s N))) ∧
        ∀ ν : Measure (Config d N), IsProbabilityMeasure ν →
          relEntropy ν (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) < ∞ →
          ∫⁻ X, ENNReal.ofReal (N * |modulatedEnergy h X (withDensityReal ρ)|) ∂ν ≤
            ENNReal.ofReal C *
              (relEntropy ν (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) +
                ENNReal.ofReal (N * deltaN d s N)) := by
  obtain ⟨θ₀, C₁, hθ₀, hC₁, hP⟩ := pressure_two_sided hd s hs0 hsd cstar hw βm βp hβm c₀ hc₀ Λ B
  have hθ₁ : 0 < βm * θ₀ := mul_pos hβm hθ₀
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max C₁ (max (2 * C₁ + 1) ((βm * θ₀)⁻¹ * (2 * C₁ + 1))) := ⟨_, rfl⟩
  have hCa : C₁ ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hCb : 2 * C₁ + 1 ≤ C := by rw [hCdef]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hCc : (βm * θ₀)⁻¹ * (2 * C₁ + 1) ≤ C := by
    rw [hCdef]; exact (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨θ₀, βm * θ₀, C, hθ₀, hθ₁, ?_⟩
  intro ρ hρ hsm hlow hcb h hhm hsym hdom N hN β hβ
  have hN1 : 1 ≤ N := by omega
  haveI hμprob : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hρΛ : ∀ x, ρ x ≤ max Λ 0 := fun x =>
    (hcb x).trans (le_max_left _ _)
  obtain ⟨hgR, hhR⟩ := rowOK_g_h hd s hs0 hsd cstar hw B (le_max_right _ _) hρΛ hhm hdom
  have hδ : 1 ≤ (N : ℝ) * deltaN d s N := one_le_mul_deltaN hs0 N hN1
  have hT : 0 ≤ (N : ℝ) * deltaN d s N := by linarith
  have hP' := hP ρ hρ hsm hlow hcb h hhm hsym hdom N hN β hβ
  obtain ⟨hE, hD⟩ := moments_of_pressure (N := N) (μ := withDensityReal ρ) (g := periodicRiesz d s)
    (h := h) hgR hhR (δ := deltaN d s N) (C := C₁) (θ₀ := θ₀) (βm := βm) (β := β) hδ hC₁ hθ₀ hβm hβ.1 hP'
  have hmono : ∀ C' : ℝ, C' ≤ C → Real.exp (C' * N * deltaN d s N) ≤ Real.exp (C * N * deltaN d s N) := by
    intro C' hC'
    refine Real.exp_le_exp.2 ?_
    have : C' * N * deltaN d s N = C' * ((N : ℝ) * deltaN d s N) := by ring
    have h2 : C * N * deltaN d s N = C * ((N : ℝ) * deltaN d s N) := by ring
    rw [this, h2]; exact mul_le_mul_of_nonneg_right hC' hT
  refine ⟨fun θ hθ => ?_, ?_, ?_⟩
  · obtain ⟨hl, hu⟩ := hP' θ hθ
    refine ⟨le_trans (ENNReal.ofReal_le_ofReal ?_) hl, hu.trans (ENNReal.ofReal_le_ofReal (hmono C₁ hCa))⟩
    refine Real.exp_le_exp.2 ?_
    have h1 : C₁ * N * deltaN d s N = C₁ * ((N : ℝ) * deltaN d s N) := by ring
    have h2 : C * N * deltaN d s N = C * ((N : ℝ) * deltaN d s N) := by ring
    rw [h1, h2]
    have := mul_le_mul_of_nonneg_right hCa hT
    linarith
  · exact hE.trans (ENNReal.ofReal_le_ofReal (hmono _ hCb))
  · intro ν hν hKL
    refine (hD ν hν hKL).trans ?_
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hCc) le_rfl

end HRS.ME.Unif

end
