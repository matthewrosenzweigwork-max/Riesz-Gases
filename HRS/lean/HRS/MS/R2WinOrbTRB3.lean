import HRS.MS.R2WinOrbTRB2
import HRS.MS.WadAux31

/-!
# S10.3 packet [B], part 3: Duhamel form of the nonlinear adjoint solution, and commutation of differences with the Mehler flow

Prefix `s103b_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103b_mild`: for a classical adjoint solution `f` (terminal datum `φ`) of the coefficient of the nonlinear trajectory `ρ`,
  `f_r = P_{t-r} φ + ∫_r^t P_{τ-r} q_τ dτ`, `q_τ = s103bQ d s (ρ_τ) (f_τ)`, `P` the Mehler semigroup of `β⁻¹Δ - a x·∇`
  (`s83_mild_form` with the splitting `s103b_gen_split`); and the integrands `τ ↦ P_{τ-r}q_τ(x)` are interval integrable.
* `s103b_dpF_cb`, `s103b_P_dpF`: the iterated differences `Δ_{m_1}⋯Δ_{m_k}` of the Mehler average satisfy
  `Δ_m (P_τ g) = P_τ (Δ_{c m} g)`, `c = e^{-aτ}` (translations are intertwined with the flow).
* `s103b_dpF_add`, `s103b_dpF_integral`: the differences are additive and commute with the interval integral in the Duhamel term.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad

variable {d : ℕ}

/-! ### Duhamel form -/

theorem s103b_mild (s a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (ρ : ℝ → Euc d → ℝ) {t : ℝ} (ht : 0 ≤ t)
    {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t φ f) :
    (∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x : Euc d, f r x = s83_P a β⁻¹ (t - r) φ x +
      ∫ τ in r..t, s83_P a β⁻¹ (τ - r) (s103bQ d s (ρ τ) (f τ)) x) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x : Euc d,
      IntervalIntegrable (fun τ => s83_P a β⁻¹ (τ - r) (s103bQ d s (ρ τ) (f τ)) x) volume r t) := by
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  obtain ⟨B0, hB0⟩ := hf.bdd 0 (by norm_num)
  obtain ⟨B1, hB1⟩ := hf.bdd 1 (by norm_num)
  obtain ⟨B2, hB2⟩ := hf.bdd 2 (by norm_num)
  have hb0 : ∀ r ∈ Set.Icc 0 t, ∀ y, |f r y| ≤ B0 := fun r hr y => by
    have := hB0 r hr y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hb1 : ∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (f r) y‖ ≤ B1 := fun r hr y => by
    have := hB1 r hr y
    rwa [norm_iteratedFDeriv_one] at this
  have hb2 : ∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (fderiv ℝ (f r)) y‖ ≤ B2 := fun r hr y => by
    have := hB2 r hr y
    rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this
  set Bm : ℝ := max B0 (max B1 B2) with hBm
  have hbnn : 0 ≤ Bm := by
    have := (abs_nonneg (f 0 0)).trans (hb0 0 h0I 0)
    exact le_max_of_le_left this
  have hB0' : ∀ r ∈ Set.Icc 0 t, ∀ y, |f r y| ≤ Bm := fun r hr y =>
    (hb0 r hr y).trans (le_max_left _ _)
  have hB1' : ∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (f r) y‖ ≤ Bm := fun r hr y =>
    (hb1 r hr y).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hB2' : ∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (fderiv ℝ (f r)) y‖ ≤ Bm := fun r hr y =>
    (hb2 r hr y).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hwc : ContinuousOn (fun q : ℝ × Euc d => f q.1 q.2) (Set.Icc 0 t ×ˢ Set.univ) :=
    s84_contOn_of_subtype (s84_cont_D0 (F := fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1)
      (x := fun p => p.2) (hf.cont_c2 0 (by norm_num)))
  have hD1 : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (f q.1) q.2) (Set.Icc 0 t ×ˢ Set.univ) :=
    s84_contOn_of_subtype (s84_cont_D1 (F := fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1)
      (x := fun p => p.2) (hf.cont_c2 1 (by norm_num)))
  have hD2 : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (fderiv ℝ (f q.1)) q.2)
      (Set.Icc 0 t ×ˢ Set.univ) :=
    s84_contOn_of_subtype (s84_cont_D2 (F := fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1)
      (x := fun p => p.2) (hf.cont_c2 2 (by norm_num)))
  have hGc : ContinuousOn (fun q : ℝ × Euc d =>
      generatorW ((quadraticGradientDyn d s a β).coeff ρ) q.1 (f q.1) q.2) (Set.Icc 0 t ×ˢ Set.univ) :=
    s84_contOn_of_subtype hf.cont_time_deriv
  obtain ⟨BG, hBG⟩ := hf.bdd_time_deriv
  have hmild := fun (r : ℝ) (hr : r ∈ Set.Icc 0 t) (x : Euc d) => s83_mild_form (a := a) (ν := β⁻¹) (t := t)
    (w := f) (G := fun r y => generatorW ((quadraticGradientDyn d s a β).coeff ρ) r (f r) y) ha hν hf.c2
    hB0' hB1' hB2' hwc hD1 hD2 hGc hf.time_deriv hBG hr x
  have hq : ∀ τ y, generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ (f τ) y -
      s83_L0 a β⁻¹ (f τ) y = s103bQ d s (ρ τ) (f τ) y := fun τ y => by
    rw [s103b_gen_split]; ring
  have hqfun : ∀ τ, (fun y => generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ (f τ) y -
      s83_L0 a β⁻¹ (f τ) y) = s103bQ d s (ρ τ) (f τ) := fun τ => funext (hq τ)
  refine ⟨fun r hr x => ?_, fun r hr x => ?_⟩
  · rw [hmild r hr x, hf.terminal]
    congr 1
    refine intervalIntegral.integral_congr fun τ _ => ?_
    show s83_P a β⁻¹ (τ - r) (fun y => generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ (f τ) y -
        s83_L0 a β⁻¹ (f τ) y) x = _
    rw [hqfun τ]
  · have hqc : ContinuousOn (fun p : ℝ × Euc d => s103bQ d s (ρ p.1) (f p.1) p.2) (Set.Icc 0 t ×ˢ Set.univ) := by
      have := hGc.sub (s83_L0_contOn a β⁻¹ hD1 hD2)
      refine this.congr fun q _ => ?_
      simp only [Pi.sub_apply]
      rw [hq]
    have hqb : ∀ τ ∈ Set.Icc 0 t, ∀ y, |s103bQ d s (ρ τ) (f τ) y| ≤
        (BG + (|β⁻¹| * d * Bm + |a| * Bm)) * (1 + ‖y‖) ^ 1 := by
      intro τ hτ y
      rw [← hq]
      have h1 := hBG τ hτ y
      have h2 := s83_L0_bound (hB1' τ hτ) (hB2' τ hτ) a β⁻¹ y
      rw [pow_one]
      refine (abs_sub _ _).trans ?_
      nlinarith [abs_nonneg (generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ (f τ) y)]
    have hcont := s83_cont_param (K := BG + (|β⁻¹| * d * Bm + |a| * Bm)) (p := 1) hr.1 hr.2 hqc hqb ha hν.le x
    exact hcont.intervalIntegrable_of_Icc hr.2

/-! ### Differences and Gaussian averages -/

theorem s103b_dpF_cb : ∀ (k : ℕ) (m : Fin k → Euc d) {g : Euc d → ℝ} {K : ℝ}, Continuous g →
    (∀ y, |g y| ≤ K) → Continuous (s8f_dpF k m g) ∧ ∀ y, |s8f_dpF k m g y| ≤ 2 ^ k * K := by
  intro k
  induction k with
  | zero =>
    intro m g K hg hK
    exact ⟨hg, fun y => by simpa [s8f_dpF] using hK y⟩
  | succ k ih =>
    intro m g K hg hK
    obtain ⟨hc, hb⟩ := ih (Fin.init m) hg hK
    refine ⟨(hc.comp (continuous_id.add continuous_const)).sub hc, fun y => ?_⟩
    show |s8f_dpF k (Fin.init m) g (y + m (Fin.last k)) - s8f_dpF k (Fin.init m) g y| ≤ _
    refine (abs_sub _ _).trans ?_
    have := hb (y + m (Fin.last k))
    have := hb y
    rw [pow_succ]
    linarith

theorem s103b_dpF_add : ∀ (k : ℕ) (m : Fin k → Euc d) (g1 g2 : Euc d → ℝ) (y : Euc d),
    s8f_dpF k m (fun y => g1 y + g2 y) y = s8f_dpF k m g1 y + s8f_dpF k m g2 y := by
  intro k
  induction k with
  | zero => intro m g1 g2 y; rfl
  | succ k ih =>
    intro m g1 g2 y
    show s8f_dpF k (Fin.init m) (fun y => g1 y + g2 y) (y + m (Fin.last k)) -
        s8f_dpF k (Fin.init m) (fun y => g1 y + g2 y) y = (s8f_dpF k (Fin.init m) g1 (y + m (Fin.last k)) -
        s8f_dpF k (Fin.init m) g1 y) + (s8f_dpF k (Fin.init m) g2 (y + m (Fin.last k)) -
        s8f_dpF k (Fin.init m) g2 y)
    rw [ih, ih]
    ring

theorem s103b_G_shift (c σ : ℝ) (g : Euc d → ℝ) (x e : Euc d) :
    s83_G c σ g (x + e) = s83_G c σ (fun w => g (w + c • e)) x := by
  unfold s83_G
  congr 1
  funext z
  congr 1
  rw [smul_add]
  abel

theorem s103b_int_cb {g : Euc d → ℝ} {K : ℝ} (hg : Continuous g) (hK : ∀ y, |g y| ≤ K) (c σ : ℝ) (x : Euc d) :
    Integrable (fun z : Euc d => g (c • x + σ • z)) (stdGaussian (Euc d)) :=
  Integrable.of_bound (hg.comp (by fun_prop)).aestronglyMeasurable K
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hK _)

theorem s103b_G_sub {A B : Euc d → ℝ} {KA KB : ℝ} (hA : Continuous A) (hB : Continuous B)
    (hKA : ∀ y, |A y| ≤ KA) (hKB : ∀ y, |B y| ≤ KB) (c σ : ℝ) (x : Euc d) :
    s83_G c σ (fun w => A w - B w) x = s83_G c σ A x - s83_G c σ B x := by
  unfold s83_G
  exact integral_sub (s103b_int_cb hA hKA c σ x) (s103b_int_cb hB hKB c σ x)

/-- The Mehler flow intertwines translations: `Δ_m (P_τ g) = P_τ (Δ_{c m} g)` with `c = e^{-aτ}`. -/
theorem s103b_P_dpF (a ν τ : ℝ) {g : Euc d → ℝ} {K : ℝ} (hg : Continuous g) (hK : ∀ y, |g y| ≤ K) :
    ∀ (k : ℕ) (m : Fin k → Euc d) (x : Euc d), s8f_dpF k m (s83_P a ν τ g) x =
      s83_P a ν τ (s8f_dpF k (fun l => s83_mc a τ • m l) g) x := by
  intro k
  induction k with
  | zero => intro m x; rfl
  | succ k ih =>
    intro m x
    set c := s83_mc a τ with hc
    set σ := s83_ms a ν τ with hσ
    obtain ⟨hGc, hGK⟩ := s103b_dpF_cb k (fun l => c • Fin.init m l) hg hK
    show s8f_dpF k (Fin.init m) (s83_P a ν τ g) (x + m (Fin.last k)) -
        s8f_dpF k (Fin.init m) (s83_P a ν τ g) x = s83_P a ν τ (fun y =>
        s8f_dpF k (Fin.init (fun l => c • m l)) g (y + c • m (Fin.last k)) -
        s8f_dpF k (Fin.init (fun l => c • m l)) g y) x
    rw [ih (Fin.init m) (x + m (Fin.last k)), ih (Fin.init m) x]
    have e1 : (fun l => s83_mc a τ • Fin.init m l) = Fin.init (fun l => c • m l) := rfl
    rw [e1] at hGc hGK ⊢
    unfold s83_P
    rw [← hc, ← hσ, s103b_G_shift]
    rw [← s103b_G_sub (A := fun w => s8f_dpF k (Fin.init fun l => c • m l) g (w + c • m (Fin.last k)))
      (B := s8f_dpF k (Fin.init fun l => c • m l) g) (KA := 2 ^ k * K) (KB := 2 ^ k * K)
      (hGc.comp (continuous_id.add continuous_const)) hGc (fun w => hGK _) hGK]

/-- Interchange of the differences with the interval integral. -/
theorem s103b_dpF_integral {r t : ℝ} {F : ℝ → Euc d → ℝ}
    (hF : ∀ y, IntervalIntegrable (fun τ => F τ y) volume r t) :
    ∀ (k : ℕ) (m : Fin k → Euc d), (∀ x, IntervalIntegrable (fun τ => s8f_dpF k m (F τ) x) volume r t) ∧
      ∀ x, s8f_dpF k m (fun y => ∫ τ in r..t, F τ y) x = ∫ τ in r..t, s8f_dpF k m (F τ) x := by
  intro k
  induction k with
  | zero => intro m; exact ⟨hF, fun x => rfl⟩
  | succ k ih =>
    intro m
    obtain ⟨hi, he⟩ := ih (Fin.init m)
    refine ⟨fun x => (hi (x + m (Fin.last k))).sub (hi x), fun x => ?_⟩
    show s8f_dpF k (Fin.init m) (fun y => ∫ τ in r..t, F τ y) (x + m (Fin.last k)) -
        s8f_dpF k (Fin.init m) (fun y => ∫ τ in r..t, F τ y) x =
        ∫ τ in r..t, (s8f_dpF k (Fin.init m) (F τ) (x + m (Fin.last k)) - s8f_dpF k (Fin.init m) (F τ) x)
    rw [he, he, intervalIntegral.integral_sub (hi _) (hi _)]

end HRS.MS.R2WinOrbNL

end
