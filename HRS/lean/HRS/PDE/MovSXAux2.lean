import HRS.PDE.MovSXAux1

/-!
# MOVSX Aux2: `pressure_two_sided` restated parametrically in `(g_L, q, c₀)`

The proof of `pressure_two_sided` (`HRS/Energy/PressureProof.lean:506`) splits `g = g_L + q - c` (`g_L = ∑ a_k cos_k`),
and uses only the abstract properties of the kernel `G = g_L + q - c` (off the diagonal), of `q` (even, `0 ≤ q ≤ q₀`
with `q₀` the fixed uniform split of `g`, so the envelope `q ≤ E₀ w` and the row bound `a < a₀` are inherited) and
of the perturbation `h` (`|h| ≤ B' w`, `|h| ≤ B' q + D`).  This file restates it for such an arbitrary kernel `G`
(the cores `pressure_upper_core`, `pressure_lower_core` and `N:lem:weak-pressure` are applied verbatim), with a sup
bound `ρ ≤ Λ0` in place of the smoothness of `ρ`.  The order of constants is
`(E₀, B', κ) → ε₀ → (split data with ∫q₀ ≤ ε₀, D) → (θ₀, C) → (G, q, ρ, h, N, β, θ)`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem movsx_pressure_param0 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cs : ℝ) (hcs : ∀ z : Torus d, 1 ≤ periodicRiesz d s z + cs)
    (βm βp : ℝ) (hβm : 0 < βm) (Λ0 : ℝ) (hΛ0 : 0 ≤ Λ0) (E₀ B' κ : ℝ) (hE₀ : 0 ≤ E₀) (hB' : 0 ≤ B')
    (hκ : 0 ≤ κ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ (Λf : Finset (Lattice d)) (af : Lattice d → ℝ) (q₀ : Torus d → ℝ) (cc D : ℝ),
        (∀ k ∈ Λf, 0 ≤ af k) → Measurable q₀ → (∀ x, 0 ≤ q₀ x) → Integrable q₀ → ∫ x, q₀ x ≤ ε₀ →
        0 ≤ cc → 0 ≤ D → (∀ x, q₀ x ≤ E₀ * (periodicRiesz d s x + cs)) →
      ∃ θ₀ C : ℝ, 0 < θ₀ ∧ 0 ≤ C ∧
        ∀ (G q : Torus d → ℝ), Measurable G → Measurable q → (∀ x, 0 ≤ q x) → (∀ x, q x ≤ q₀ x) →
          (∀ x, q (-x) = q x) → (∀ z, |G z| ≤ κ * (periodicRiesz d s z + cs)) →
          (∀ x : Torus d, x ≠ 0 → G x = ∑ k ∈ Λf, af k * Torus.cosMode k x + q x - cc) →
        ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ0) →
        ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
          (∀ x y, |h x y| ≤ B' * (periodicRiesz d s (x - y) + cs)) →
          (∀ x y, |h x y| ≤ B' * q (x - y) + D) →
        ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp, ∀ θ : ℝ, |θ| ≤ θ₀ →
          ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤
              ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => G (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ∧
          ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => G (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ≤
            ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  obtain ⟨g, hg⟩ : ∃ g : Torus d → ℝ, g = periodicRiesz d s := ⟨_, rfl⟩
  rw [← hg] at hcs ⊢
  have hgm : Measurable g := by rw [hg]; exact CoercAux.measurable_periodicRiesz_one hd hs0 hsd
  have hgi : Integrable g := by rw [hg]; exact CoercAux.integrable_periodicRiesz_one hd hs0 hsd
  have hwi : Integrable (fun z => g z + cs) := hgi.add (integrable_const cs)
  obtain ⟨Mw, hMw⟩ : ∃ Mw : ℝ, Mw = ∫ z, (g z + cs) := ⟨_, rfl⟩
  have hMw0 : 0 ≤ Mw := by
    rw [hMw]; exact integral_nonneg fun z => by show 0 ≤ g z + cs; linarith [hcs z]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = E₀ + B' + 1 := ⟨_, rfl⟩
  obtain ⟨a₀, Cw, ha₀, hweak⟩ := movsx_weak_reference_pressure hd s hs0 hsd cs
    (fun z _ => by have := hcs z; rw [hg] at this; exact this) βm βp hβm Λ0 A
  rw [← hg] at hweak
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min 1 (a₀ / (4 * (Λ0 + 1))) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := by rw [hεdef]; exact min_le_left _ _
  have hεa : Λ0 * ε ≤ a₀ / 4 := by
    have h1 : ε ≤ a₀ / (4 * (Λ0 + 1)) := by rw [hεdef]; exact min_le_right _ _
    calc Λ0 * ε ≤ Λ0 * (a₀ / (4 * (Λ0 + 1))) := mul_le_mul_of_nonneg_left h1 hΛ0
      _ ≤ (Λ0 + 1) * (a₀ / (4 * (Λ0 + 1))) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = a₀ / 4 := by field_simp
  refine ⟨ε, hε, hε1, ?_⟩
  intro Λf af q₀ cc D haf hq₀m hq₀0 hq₀int hq₀ε hcc hD0 hq₀env
  obtain ⟨Sa, hSa⟩ : ∃ Sa : ℝ, Sa = ∑ k ∈ Λf, af k := ⟨_, rfl⟩
  have hSa0 : 0 ≤ Sa := by rw [hSa]; exact Finset.sum_nonneg haf
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
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = Λ0 * ∫ z, ((κ + B') * (g z + cs)) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg hΛ0 (integral_nonneg fun z => by
      show 0 ≤ (κ + B') * (g z + cs)
      have := hcs z
      exact mul_nonneg (by linarith) (by linarith))
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (|βp| * Sa / 2 + |Cw|) (|βp| * M / 2) := ⟨_, rfl⟩
  have hC1 : |βp| * Sa / 2 + |Cw| ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hC2 : |βp| * M / 2 ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hC0 : 0 ≤ C := le_trans (by positivity) hC1
  refine ⟨θ₀, C, hθ₀pos, hC0, ?_⟩
  intro G q hGm hqm hq0 hqle hqev hGdom hsplit ρ hρ hρΛ h hhm hsym hhdom henv N hN β hβ θ hθ
  have hN1 : 1 ≤ N := by omega
  have hβ0 : 0 ≤ β := (hβm.trans_le hβ.1).le
  haveI hμprob : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hδ : 1 ≤ (N : ℝ) * deltaN d s N := one_le_mul_deltaN hs0 N hN1
  have hT : 0 ≤ (N : ℝ) * deltaN d s N := by linarith
  have hθ' : |θ| ≤ 1 := hθ.trans hθ1
  have hmeas2 : ∀ {f : Torus d → ℝ}, Measurable f → Measurable (Function.uncurry fun x y : Torus d => f (x - y)) :=
    fun hf => hf.comp (measurable_fst.sub measurable_snd)
  have hqint : Integrable q := by
    refine Integrable.mono' hq₀int hqm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hq0 z)]; exact hqle z
  have hqε : ∫ z, q z ≤ ε := (integral_mono hqint hq₀int hqle).trans hq₀ε
  have hqenv : ∀ z, q z ≤ E₀ * (g z + cs) := fun z => (hqle z).trans (hq₀env z)
  have hwint : Integrable (fun z => B' * (g z + cs)) := hwi.const_mul B'
  have hhR : RowOK (withDensityReal ρ) h := (rowOK_of_dom hΛ0 hρΛ hwint hhm hhdom).1
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
  have hW := hweak ρ hρ hρΛ qθ hqθm hqθsym hqθ0 hqθA (a₀ / 2) (by positivity)
    (by linarith) hrowL N hN β hβ
  have hμ0 : ∀ x, withDensityReal ρ {x} = 0 := withDensityReal_singleton hd ρ
  have hβp : β ≤ |βp| := hβ.2.trans (le_abs_self _)
  refine ⟨?_, ?_⟩
  · -- lower bound (Jensen)
    have hkdom : ∀ x y, |G (x - y) - θ * h x y| ≤ (fun z => (κ + B') * (g z + cs)) (x - y) := by
      intro x y
      simp only
      have h1 := hhdom x y
      have h2 := hGdom (x - y)
      calc |G (x - y) - θ * h x y| ≤ |G (x - y)| + |θ * h x y| := abs_sub _ _
        _ ≤ κ * (g (x - y) + cs) + B' * (g (x - y) + cs) := by
            refine add_le_add h2 ?_
            rw [abs_mul]
            calc |θ| * |h x y| ≤ 1 * |h x y| := mul_le_mul_of_nonneg_right hθ' (abs_nonneg _)
              _ ≤ _ := by rw [one_mul]; exact h1
        _ = (κ + B') * (g (x - y) + cs) := by ring
    have hWint : Integrable (fun z => (κ + B') * (g z + cs)) := hwi.const_mul _
    have hkm : Measurable (Function.uncurry fun x y : Torus d => G (x - y) - θ * h x y) := by
      show Measurable (fun p : Torus d × Torus d => G (p.1 - p.2) - θ * h p.1 p.2)
      exact (hGm.comp (measurable_fst.sub measurable_snd)).sub
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
    have hup := pressure_upper_core (N := N) hμ0 Λf af haf G q cc hcc hsplit hgLR hqR hhR θ D hD0 hN1 hβ0
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

set_option maxHeartbeats 800000 in
/-- `movsx_pressure_param0` with the domination `|G| ≤ κ w` required only off the diagonal `z ≠ 0`
(the kernel is then replaced by `0` on the diagonal, which changes neither the energies a.e. nor the partition
functions). -/
theorem movsx_pressure_param (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cs : ℝ) (hcs : ∀ z : Torus d, 1 ≤ periodicRiesz d s z + cs)
    (βm βp : ℝ) (hβm : 0 < βm) (Λ0 : ℝ) (hΛ0 : 0 ≤ Λ0) (E₀ B' κ : ℝ) (hE₀ : 0 ≤ E₀) (hB' : 0 ≤ B')
    (hκ : 0 ≤ κ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ (Λf : Finset (Lattice d)) (af : Lattice d → ℝ) (q₀ : Torus d → ℝ) (cc D : ℝ),
        (∀ k ∈ Λf, 0 ≤ af k) → Measurable q₀ → (∀ x, 0 ≤ q₀ x) → Integrable q₀ → ∫ x, q₀ x ≤ ε₀ →
        0 ≤ cc → 0 ≤ D → (∀ x, q₀ x ≤ E₀ * (periodicRiesz d s x + cs)) →
      ∃ θ₀ C : ℝ, 0 < θ₀ ∧ 0 ≤ C ∧
        ∀ (G q : Torus d → ℝ), Measurable G → Measurable q → (∀ x, 0 ≤ q x) → (∀ x, q x ≤ q₀ x) →
          (∀ x, q (-x) = q x) → (∀ z, z ≠ 0 → |G z| ≤ κ * (periodicRiesz d s z + cs)) →
          (∀ x : Torus d, x ≠ 0 → G x = ∑ k ∈ Λf, af k * Torus.cosMode k x + q x - cc) →
        ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ0) →
        ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
          (∀ x y, |h x y| ≤ B' * (periodicRiesz d s (x - y) + cs)) →
          (∀ x y, |h x y| ≤ B' * q (x - y) + D) →
        ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp, ∀ θ : ℝ, |θ| ≤ θ₀ →
          ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤
              ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => G (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ∧
          ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => G (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ≤
            ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  obtain ⟨ε₀, hε₀, hε₁, H⟩ := movsx_pressure_param0 hd s hs0 hsd cs hcs βm βp hβm Λ0 hΛ0 E₀ B' κ hE₀ hB' hκ
  refine ⟨ε₀, hε₀, hε₁, fun Λf af q₀ cc D haf hq₀m hq₀0 hq₀int hq₀ε hcc hD hq₀env => ?_⟩
  obtain ⟨θ₀, C, hθ, hC, H2⟩ := H Λf af q₀ cc D haf hq₀m hq₀0 hq₀int hq₀ε hcc hD hq₀env
  refine ⟨θ₀, C, hθ, hC, fun G q hGm hqm hq0 hqle hqev hGdom hsplit ρ hρ hρΛ h hhm hsym hhdom henv N hN β hβ θ hθ' => ?_⟩
  obtain ⟨G', hG'⟩ : ∃ G' : Torus d → ℝ, G' = fun z => if z = 0 then 0 else G z := ⟨_, rfl⟩
  have hG'm : Measurable G' := by
    rw [hG']; exact Measurable.ite (measurableSet_singleton (0 : Torus d)) measurable_const hGm
  have hG'dom : ∀ z, |G' z| ≤ κ * (periodicRiesz d s z + cs) := by
    intro z
    by_cases hz : z = 0
    · have h1 := hcs z
      have : G' z = 0 := by rw [hG']; simp [hz]
      rw [this, abs_zero]; exact mul_nonneg hκ (by linarith)
    · have : G' z = G z := by rw [hG']; simp [hz]
      rw [this]; exact hGdom z hz
  have hsplit' : ∀ x : Torus d, x ≠ 0 → G' x = ∑ k ∈ Λf, af k * Torus.cosMode k x + q x - cc := by
    intro x hx
    have : G' x = G x := by rw [hG']; simp [hx]
    rw [this]; exact hsplit x hx
  have key := H2 G' q hG'm hqm hq0 hqle hqev hG'dom hsplit' ρ hρ hρΛ h hhm hsym hhdom henv N hN β hβ θ hθ'
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hμ0 : ∀ x, withDensityReal ρ {x} = 0 := withDensityReal_singleton hd ρ
  have hEq : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => G (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) =
      ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => G' (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_injective_pi (N := N) hμ0] with X hX
    rw [modulatedEnergy_congr_offdiag hμ0 (k₂ := fun x y => G' (x - y) - θ * h x y)
      (fun x y hxy => by
        have : x - y ≠ 0 := sub_ne_zero.2 hxy
        simp only [hG', this, if_false]) X hX]
  rw [hEq]
  exact key

end HRS

end
