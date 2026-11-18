import HRS.MS.R2WinOrbTRD4

/-!
# S10.3 packet [C], part 5: the weighted terminal-layer estimate

Prefix `s103c_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103c_mild_e`: for a classical adjoint solution `f` with terminal datum `ψ ∈ C²_b`, the difference `e_r = f_r - ψ` satisfies the Duhamel formula with the
  source `q_τ + L_0ψ` and zero terminal value: `e_r = ∫_r^t P_{τ-r}(q_τ + L_0 ψ) dτ` (`s83_mild_form` for `w = f - ψ`).
* `s103c_layer_wt` (**Lemma W**): the jets of order `1..N` of `f_r - ψ` are `O(t-r)(1+‖x‖)⁻¹`, with a constant independent of the trajectory, `t`, `r`, `ψ`, `f`.
  This is the estimate that makes the drift `-a x·∇(f_r - ψ)` of the generator small in `Bd N` on the terminal layer.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul HRS.MS.Who HRS.MS.BreakdownS67 HRS.MS.MovLin

variable {d : ℕ}

theorem s103c_fderiv_sub1 {g1 g2 : Euc d → ℝ} (hg1 : ContDiff ℝ 2 g1) (hg2 : ContDiff ℝ 2 g2) (y : Euc d) :
    fderiv ℝ (fun y => g1 y - g2 y) y = fderiv ℝ g1 y - fderiv ℝ g2 y :=
  fderiv_sub ((hg1.differentiable (by norm_num)) y) ((hg2.differentiable (by norm_num)) y)

theorem s103c_fderiv_sub2 {g1 g2 : Euc d → ℝ} (hg1 : ContDiff ℝ 2 g1) (hg2 : ContDiff ℝ 2 g2) (y : Euc d) :
    fderiv ℝ (fderiv ℝ (fun y => g1 y - g2 y)) y = fderiv ℝ (fderiv ℝ g1) y - fderiv ℝ (fderiv ℝ g2) y := by
  have e : fderiv ℝ (fun y => g1 y - g2 y) = fun y => fderiv ℝ g1 y - fderiv ℝ g2 y :=
    funext (s103c_fderiv_sub1 hg1 hg2)
  have h1 : ContDiff ℝ 1 (fderiv ℝ g1) := hg1.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 1 (fderiv ℝ g2) := hg2.fderiv_right (by norm_num)
  rw [e]
  exact fderiv_sub ((h1.differentiable one_ne_zero) y) ((h2.differentiable one_ne_zero) y)

theorem s103c_mild_e (s a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (ρ : ℝ → Euc d → ℝ) {t : ℝ} (ht : 0 ≤ t)
    {ψ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t ψ f)
    (hψ2 : ContDiff ℝ 2 ψ) {Bψ : ℝ} (hψb : ∀ j ≤ 2, ∀ y, ‖iteratedFDeriv ℝ j ψ y‖ ≤ Bψ) :
    (∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x : Euc d, f r x - ψ x = ∫ τ in r..t,
      s83_P a β⁻¹ (τ - r) (fun y => s103bQ d s (ρ τ) (f τ) y + s83_L0 a β⁻¹ ψ y) x) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x : Euc d, IntervalIntegrable (fun τ =>
      s83_P a β⁻¹ (τ - r) (fun y => s103bQ d s (ρ τ) (f τ) y + s83_L0 a β⁻¹ ψ y) x) volume r t) := by
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
  have hψ0 : ∀ y, |ψ y| ≤ Bψ := fun y => by
    have := hψb 0 (by norm_num) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hψ1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ Bψ := fun y => by
    have := hψb 1 (by norm_num) y
    rwa [norm_iteratedFDeriv_one] at this
  have hψ2' : ∀ y, ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ Bψ := fun y => by
    have := hψb 2 (by norm_num) y
    rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this
  have hBψ : 0 ≤ Bψ := (abs_nonneg _).trans (hψ0 0)
  set Bm : ℝ := max B0 (max B1 B2) with hBm
  have hbnn : 0 ≤ Bm := by
    have := (abs_nonneg (f 0 0)).trans (hb0 0 h0I 0)
    exact le_max_of_le_left this
  have hB0' : ∀ r ∈ Set.Icc 0 t, ∀ y, |f r y - ψ y| ≤ Bm + Bψ := fun r hr y =>
    (abs_sub _ _).trans (add_le_add ((hb0 r hr y).trans (le_max_left _ _)) (hψ0 y))
  have hB1' : ∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (fun y => f r y - ψ y) y‖ ≤ Bm + Bψ := fun r hr y => by
    rw [s103c_fderiv_sub1 (hf.c2 r hr) hψ2]
    exact (norm_sub_le _ _).trans (add_le_add ((hb1 r hr y).trans ((le_max_left _ _).trans (le_max_right _ _)))
      (hψ1 y))
  have hB2' : ∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (fderiv ℝ (fun y => f r y - ψ y)) y‖ ≤ Bm + Bψ := fun r hr y => by
    rw [s103c_fderiv_sub2 (hf.c2 r hr) hψ2]
    have h3 := norm_sub_le (fderiv ℝ (fderiv ℝ (f r)) y) (fderiv ℝ (fderiv ℝ ψ) y)
    have h4 : ‖fderiv ℝ (fderiv ℝ (f r)) y‖ ≤ Bm := (hb2 r hr y).trans ((le_max_right B1 B2).trans (le_max_right B0 (max B1 B2)))
    have h5 := hψ2' y
    linarith
  have hwc : ContinuousOn (fun q : ℝ × Euc d => f q.1 q.2 - ψ q.2) (Set.Icc 0 t ×ˢ Set.univ) := by
    have h1 : ContinuousOn (fun q : ℝ × Euc d => f q.1 q.2) (Set.Icc 0 t ×ˢ Set.univ) :=
      s84_contOn_of_subtype (s84_cont_D0 (F := fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1)
        (x := fun p => p.2) (hf.cont_c2 0 (by norm_num)))
    exact h1.sub (hψ2.continuous.comp continuous_snd).continuousOn
  have hD1f : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (f q.1) q.2) (Set.Icc 0 t ×ˢ Set.univ) :=
    s84_contOn_of_subtype (s84_cont_D1 (F := fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1)
      (x := fun p => p.2) (hf.cont_c2 1 (by norm_num)))
  have hD2f : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (fderiv ℝ (f q.1)) q.2) (Set.Icc 0 t ×ˢ Set.univ) :=
    s84_contOn_of_subtype (s84_cont_D2 (F := fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1)
      (x := fun p => p.2) (hf.cont_c2 2 (by norm_num)))
  have hψd1 : Continuous (fderiv ℝ ψ) := hψ2.continuous_fderiv (by norm_num)
  have hψd2 : Continuous (fderiv ℝ (fderiv ℝ ψ)) :=
    (hψ2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hD1 : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (fun y => f q.1 y - ψ y) q.2) (Set.Icc 0 t ×ˢ Set.univ) := by
    refine (hD1f.sub (hψd1.comp continuous_snd).continuousOn).congr fun q hq => ?_
    exact s103c_fderiv_sub1 (hf.c2 q.1 hq.1) hψ2 q.2
  have hD2 : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (fderiv ℝ (fun y => f q.1 y - ψ y)) q.2)
      (Set.Icc 0 t ×ˢ Set.univ) := by
    refine (hD2f.sub (hψd2.comp continuous_snd).continuousOn).congr fun q hq => ?_
    exact s103c_fderiv_sub2 (hf.c2 q.1 hq.1) hψ2 q.2
  have hGc : ContinuousOn (fun q : ℝ × Euc d =>
      generatorW ((quadraticGradientDyn d s a β).coeff ρ) q.1 (f q.1) q.2) (Set.Icc 0 t ×ˢ Set.univ) :=
    s84_contOn_of_subtype hf.cont_time_deriv
  obtain ⟨BG, hBG⟩ := hf.bdd_time_deriv
  have hder : ∀ x : Euc d, ∀ r ∈ Set.Ioo 0 t, HasDerivAt (fun r' => f r' x - ψ x)
      (-(generatorW ((quadraticGradientDyn d s a β).coeff ρ) r (f r) x)) r := fun x r hr =>
    (hf.time_deriv x r hr).sub_const (ψ x)
  have hmild := fun (r : ℝ) (hr : r ∈ Set.Icc 0 t) (x : Euc d) => s83_mild_form (a := a) (ν := β⁻¹) (t := t)
    (w := fun r y => f r y - ψ y) (G := fun r y => generatorW ((quadraticGradientDyn d s a β).coeff ρ) r (f r) y)
    ha hν (fun r hr => (hf.c2 r hr).sub hψ2) hB0' hB1' hB2' hwc hD1 hD2 hGc hder hBG hr x
  have hq : ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ y, generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ (f τ) y -
      s83_L0 a β⁻¹ (fun y => f τ y - ψ y) y = s103bQ d s (ρ τ) (f τ) y + s83_L0 a β⁻¹ ψ y := by
    intro τ hτ y
    rw [s103b_gen_split, s103c_L0_sub a β (hf.c2 τ hτ) hψ2]
    ring
  have hzero : (fun y => f t y - ψ y) = fun _ => 0 := by
    funext y; simp [hf.terminal]
  refine ⟨fun r hr x => ?_, fun r hr x => ?_⟩
  · rw [hmild r hr x, hzero]
    have h0 : s83_P a β⁻¹ (t - r) (fun _ : Euc d => (0 : ℝ)) x = 0 := by
      simp [s83_P, s83_G]
    rw [h0, zero_add]
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    have hτ' : τ ∈ Set.Icc r t := by rwa [Set.uIcc_of_le hr.2] at hτ
    have hτ0 : τ ∈ Set.Icc (0 : ℝ) t := ⟨hr.1.trans hτ'.1, hτ'.2⟩
    show s83_P a β⁻¹ (τ - r) (fun y => generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ (f τ) y -
        s83_L0 a β⁻¹ (fun y => f τ y - ψ y) y) x = _
    have : (fun y => generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ (f τ) y -
        s83_L0 a β⁻¹ (fun y => f τ y - ψ y) y) = fun y => s103bQ d s (ρ τ) (f τ) y + s83_L0 a β⁻¹ ψ y :=
      funext (hq τ hτ0)
    rw [this]
  · have hL0c : ContinuousOn (fun p : ℝ × Euc d => s83_L0 a β⁻¹ ψ p.2) (Set.Icc 0 t ×ˢ Set.univ) :=
      s83_L0_contOn (w := fun _ : ℝ => ψ) (S := Set.Icc 0 t ×ˢ Set.univ) a β⁻¹
        (hψd1.comp continuous_snd).continuousOn (hψd2.comp continuous_snd).continuousOn
    have hQeq : ∀ τ y, s103bQ d s (ρ τ) (f τ) y =
        generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ (f τ) y - s83_L0 a β⁻¹ (f τ) y := by
      intro τ y; rw [s103b_gen_split]; ring
    have hqc : ContinuousOn (fun p : ℝ × Euc d => s103bQ d s (ρ p.1) (f p.1) p.2 + s83_L0 a β⁻¹ ψ p.2)
        (Set.Icc 0 t ×ˢ Set.univ) := by
      have h1 := hGc.sub (s83_L0_contOn (w := f) a β⁻¹ hD1f hD2f)
      have h2 : ContinuousOn (fun p : ℝ × Euc d => s103bQ d s (ρ p.1) (f p.1) p.2) (Set.Icc 0 t ×ˢ Set.univ) :=
        h1.congr fun q _ => by simp only [Pi.sub_apply]; rw [hQeq]
      exact h2.add hL0c
    have hqb : ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ y, |s103bQ d s (ρ τ) (f τ) y + s83_L0 a β⁻¹ ψ y| ≤
        (BG + (|β⁻¹| * d * Bm + |a| * Bm) + (|β⁻¹| * d * Bψ + |a| * Bψ)) * (1 + ‖y‖) ^ 1 := by
      intro τ hτ y
      have h1 := hBG τ hτ y
      have h2 := s83_L0_bound (B1 := Bm) (B2 := Bm)
        (fun y' => (hb1 τ hτ y').trans ((le_max_left B1 B2).trans (le_max_right B0 (max B1 B2))))
        (fun y' => (hb2 τ hτ y').trans ((le_max_right B1 B2).trans (le_max_right B0 (max B1 B2)))) a β⁻¹ y
      have h3 := s83_L0_bound hψ1 hψ2' a β⁻¹ y
      rw [pow_one, hQeq]
      have h4 : |generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ (f τ) y - s83_L0 a β⁻¹ (f τ) y| ≤
          BG * (1 + ‖y‖) + (|β⁻¹| * d * Bm + |a| * Bm) * (1 + ‖y‖) := (abs_sub _ _).trans (add_le_add h1 h2)
      have h5 := abs_add_le (generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ (f τ) y -
        s83_L0 a β⁻¹ (f τ) y) (s83_L0 a β⁻¹ ψ y)
      nlinarith [h4, h3, h5]
    have hcont := s83_cont_param (K := BG + (|β⁻¹| * d * Bm + |a| * Bm) + (|β⁻¹| * d * Bψ + |a| * Bψ)) (p := 1)
      hr.1 hr.2 hqc hqb ha hν.le x
    exact hcont.intervalIntegrable_of_Icc hr.2

theorem s103c_layer_wt {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ) (ha : 0 < a)
    (hβ : 0 < β) (N : ℕ) {L : ℝ} (hL : (d : ℝ) + N + s + 3 < L) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ρ : ℝ → Euc d → ℝ) (Ah : ℝ), 0 ≤ Ah →
      (∀ τ ∈ Set.Icc (0 : ℝ) T, U2Dec (N + 1) L Ah (ρ τ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (ψ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (Aψ G : ℝ),
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t ψ f →
        DatD (N + 2) Aψ ψ →
        (∀ τ ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ ((N + 2 : ℕ) : WithTop ℕ∞) (f τ) ∧
          ∀ i, 1 ≤ i → i ≤ N + 2 → ∀ y, ‖iteratedFDeriv ℝ i (f τ) y‖ ≤ G) →
        ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ i, 1 ≤ i → i ≤ N → ∀ x : Euc d,
          ‖iteratedFDeriv ℝ i (fun y => f r y - ψ y) x‖ ≤ K * (Aψ + Ah * G) * (t - r) * (1 + ‖x‖)⁻¹ := by
  obtain ⟨Cq, hCq0, hCq⟩ := s103b_q_sy hd hs0 hsd N hL
  set m₁ : ℝ := mom d 1 (Real.sqrt (β⁻¹ / a)) with hm₁
  have hm₁0 : 0 ≤ m₁ := s83_mom_nonneg _ _ (Real.sqrt_nonneg _)
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  set C0 : ℝ := |β⁻¹| * d + d * (|a| * ((N : ℝ) + 1)) with hC0
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨(max 1 (d : ℝ)) ^ N * (5 / 4) ^ N * m₁ * (Cq + C0), by positivity, ?_⟩
  intro ρ Ah hAh hU t ht ψ f Aψ G hf hψ hfb r hr i hi1 hiN x
  have ht0 : 0 ≤ t := ht.1
  have hIcc : ∀ τ ∈ Set.Icc (0 : ℝ) t, τ ∈ Set.Icc (0 : ℝ) T := fun τ hτ => ⟨hτ.1, hτ.2.trans ht.2⟩
  have hAψ : 0 ≤ Aψ := hψ.nonneg
  have hG : 0 ≤ G := by
    have := (hfb r hr).2 1 le_rfl (by omega) 0
    exact (norm_nonneg _).trans this
  set Nsrc : ℝ := Cq * Ah * G + C0 * Aψ with hNsrc
  have hNs0 : 0 ≤ Nsrc := by positivity
  have hqSy : ∀ τ ∈ Set.Icc (0 : ℝ) t, Sy N (Cq * Ah * G) (s103bQ d s (ρ τ) (f τ)) := fun τ hτ =>
    hCq Ah (ρ τ) hAh (hU τ (hIcc τ hτ)) G (f τ) (hfb τ hτ).1 (hfb τ hτ).2
  have hL0 : Sy N (C0 * Aψ) (s83_L0 a β⁻¹ ψ) := s103c_L0_sy a β (hψ)
  set S : ℝ → Euc d → ℝ := fun τ y => s103bQ d s (ρ τ) (f τ) y + s83_L0 a β⁻¹ ψ y with hS
  have hSy : ∀ τ ∈ Set.Icc (0 : ℝ) t, Sy N Nsrc (S τ) := fun τ hτ => (hqSy τ hτ).add hL0
  have hψ2 : ContDiff ℝ 2 ψ := by
    have := hψ.1.of_le (show ((2 : ℕ) : WithTop ℕ∞) ≤ ((N + 2 : ℕ) : WithTop ℕ∞) by exact_mod_cast (by omega))
    exact_mod_cast this
  obtain ⟨hmild, hint⟩ := s103c_mild_e s a β ha hβ ρ ht0 hf hψ2 (Bψ := Aψ)
    (fun j hj y => hψ.2.1 j (by omega) y)
  have hScont : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (S τ) := fun τ hτ => (hSy τ hτ).1.continuous
  have hSbd : ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ y, |S τ y| ≤ Nsrc := by
    intro τ hτ y
    have := (hSy τ hτ).2 0 (Nat.zero_le _) y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    have hw : (1 + ‖y‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg y])
    calc |S τ y| ≤ Nsrc * (1 + ‖y‖)⁻¹ := this
      _ ≤ Nsrc * 1 := mul_le_mul_of_nonneg_left hw hNs0
      _ = Nsrc := mul_one _
  have he : (fun y => f r y - ψ y) = fun y => ∫ τ in r..t, s83_P a β⁻¹ (τ - r) (S τ) y := funext (hmild r hr)
  have hfrC : ContDiff ℝ (i : WithTop ℕ∞) (fun y => f r y - ψ y) :=
    ((hfb r hr).1.of_le (by exact_mod_cast (by omega : i ≤ N + 2))).sub
      (hψ.1.of_le (by exact_mod_cast (by omega : i ≤ N + 2)))
  have hw0 : 0 ≤ (1 + ‖x‖)⁻¹ := inv_nonneg.2 (by linarith [norm_nonneg x])
  have hBnn : 0 ≤ (5 / 4 : ℝ) ^ i * m₁ * Nsrc * (t - r) * (1 + ‖x‖)⁻¹ := by
    have : 0 ≤ t - r := sub_nonneg.2 hr.2
    positivity
  have hmain : ‖iteratedFDeriv ℝ i (fun y => f r y - ψ y) x‖ ≤
      (d : ℝ) ^ i * ((5 / 4 : ℝ) ^ i * m₁ * Nsrc * (t - r) * (1 + ‖x‖)⁻¹) := by
    refine s103c_iter_le_of_dpF hfrC hBnn x fun h hh hh0 idx => ?_
    obtain ⟨hn, hsum, hprod⟩ := s103c_steps_small hh hh0 idx
    set m : Fin i → Euc d := fun l => h • (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d) with hm
    have hkh : (i : ℝ) * h ≤ 1 / 8 := by
      have : ∑ l : Fin i, ‖m l‖ = (i : ℝ) * h := by
        simp only [hm, hn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      linarith
    have hint' := (s103b_dpF_integral (r := r) (t := t)
      (F := fun τ y => s83_P a β⁻¹ (τ - r) (S τ) y) (fun y => hint r hr y) i m).2 x
    rw [he, hint']
    have hsrc : ‖∫ τ in r..t, s8f_dpF i m (fun y => s83_P a β⁻¹ (τ - r) (S τ) y) x‖ ≤
        ((5 / 4 : ℝ) ^ i * m₁ * Nsrc * h ^ i * (1 + ‖x‖)⁻¹) * |t - r| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun τ hτ => ?_
      have hτ' : τ ∈ Set.Icc r t := by
        rw [Set.uIoc_of_le hr.2] at hτ
        exact ⟨hτ.1.le, hτ.2⟩
      have hτ0 : τ ∈ Set.Icc (0 : ℝ) t := ⟨hr.1.trans hτ'.1, hτ'.2⟩
      show ‖s8f_dpF i m (s83_P a β⁻¹ (τ - r) (S τ)) x‖ ≤ _
      rw [s103b_P_dpF a β⁻¹ (τ - r) (hScont τ hτ0) (hSbd τ hτ0) i m x, Real.norm_eq_abs]
      exact s103b_P_dp_wt ha hν (sub_nonneg.2 hτ'.1) hi1 hNs0
        ((hSy τ hτ0).1.of_le (by exact_mod_cast hiN))
        (fun i' hi' h1 y => (hSy τ hτ0).2 i' (hi'.trans hiN) y) hh hkh m (fun l => hn l) x
    rw [Real.norm_eq_abs] at hsrc
    refine hsrc.trans (le_of_eq ?_)
    rw [abs_of_nonneg (sub_nonneg.2 hr.2)]; ring
  refine hmain.trans ?_
  have hd1 : (1 : ℝ) ≤ max 1 (d : ℝ) := le_max_left _ _
  have hdi : (d : ℝ) ^ i ≤ (max 1 (d : ℝ)) ^ N :=
    (pow_le_pow_left₀ (Nat.cast_nonneg d) (le_max_right _ _) i).trans (pow_le_pow_right₀ hd1 hiN)
  have h54 : (5 / 4 : ℝ) ^ i ≤ (5 / 4) ^ N := pow_le_pow_right₀ (by norm_num) hiN
  have hAG : Nsrc ≤ (Cq + C0) * (Aψ + Ah * G) := by
    have h1 : 0 ≤ Ah * G := mul_nonneg hAh hG
    nlinarith [mul_nonneg hCq0 hAψ, mul_nonneg hC00 h1]
  have htr : 0 ≤ t - r := sub_nonneg.2 hr.2
  calc (d : ℝ) ^ i * ((5 / 4 : ℝ) ^ i * m₁ * Nsrc * (t - r) * (1 + ‖x‖)⁻¹)
      ≤ (max 1 (d : ℝ)) ^ N * ((5 / 4 : ℝ) ^ N * m₁ * ((Cq + C0) * (Aψ + Ah * G)) * (t - r) * (1 + ‖x‖)⁻¹) := by
        gcongr
    _ = _ := by ring

end HRS.MS.R2WinOrbNL

end
