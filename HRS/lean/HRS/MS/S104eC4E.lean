import HRS.MS.S104eC4D

/-!
# S104E route C, packet C4 part E: reverse time, identification with `generatorW`, and `IsClassicalAdjointW`

`c4_classical`: a family `w` with `C²` bounded slices, jointly continuous jets of order `≤ 2`, `w t = ψ`, satisfying the mild (Duhamel) equation
`w r = P_{t-r} ψ + ∫_r^t P_{v-r} (g v) dv`, where `g r = s103bQ d s (ρ r) (w r)` is bounded in `C²` and uniformly continuous in `r`, is a classical adjoint
solution along `(quadraticGradientDyn d s a β).coeff ρ`.  (`P = ouSg (ouQ d a) β⁻¹`.)  The inputs on `g` are supplied by packet C2 and the Hölder bounds of `w`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc HRS.MS.R2WinOrbNL

variable {d : ℕ}

theorem c4_gen_eq (s a β : ℝ) (ρ : ℝ → Euc d → ℝ) (r : ℝ) (h : Euc d → ℝ) (x : Euc d) :
    generatorW ((quadraticGradientDyn d s a β).coeff ρ) r h x =
      ul5A (ouQ d a) β⁻¹ h x + s103bQ d s (ρ r) h x := by
  rw [s103b_gen_split]
  congr 1
  unfold HRS.MS.Wad.s83_L0 ul5A
  rw [← HRS.MS.Wad.s83_lap_eq]
  have h1 : inner ℝ (-(Torus.matVec (ouQ d a) x)) (gradient h x) = -(a * fderiv ℝ h x x) := by
    have e : Torus.matVec (ouQ d a) x = a • x := by
      simp [Torus.matVec, ouQ]
    rw [e, inner_neg_left, inner_smul_left, HRS.MS.PoisKolm.kl_inner_gradient]
    simp
  rw [h1]; ring

theorem c4_mild_rev (Q : Matrix (Fin d) (Fin d) ℝ) (ν t : ℝ) (g : ℝ → Euc d → ℝ) (τ : ℝ) (x : Euc d) :
    Dd Q ν (fun σ => g (t - σ)) τ τ x = ∫ v in (t - τ)..t, ouSg Q ν (v - (t - τ)) (g v) x := by
  unfold Dd
  have := intervalIntegral.integral_comp_sub_left (a := 0) (b := τ)
    (fun v => ouSg Q ν (v - (t - τ)) (g v) x) t
  rw [sub_zero] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun σ _ => ?_
  simp only
  rw [show t - σ - (t - τ) = τ - σ by ring]

theorem c4_gen_cont2 (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) {t : ℝ} {w : ℝ → Euc d → ℝ}
    (h1 : ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ 1 (w p.1) p.2) (Icc 0 t ×ˢ univ))
    (h2 : ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ 2 (w p.1) p.2) (Icc 0 t ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × Euc d => ul5A Q ν (w p.1) p.2) (Icc 0 t ×ˢ univ) := by
  have hp := (continuous_snd.continuousOn (s := Icc 0 t ×ˢ univ)).prodMk (h1.prodMk h2)
  have hG := (ul5G_cont2 Q ν).comp_continuousOn hp
  refine hG.congr fun p _ => ?_
  exact ul5_A_eq Q ν _ _

theorem c4_classical (s a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (ρ : ℝ → Euc d → ℝ) {t : ℝ} (ht : 0 ≤ t)
    {ψ : Euc d → ℝ} {Bψ : ℝ} (hψ : Bd 2 Bψ ψ) {w g : ℝ → Euc d → ℝ} {Bw Kg : ℝ}
    (hw : ∀ r ∈ Icc (0 : ℝ) t, Bd 2 Bw (w r))
    (hwc : ∀ i ≤ 2, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (w p.1) p.2) (Icc 0 t ×ˢ univ))
    (hwt : w t = ψ)
    (hg : ∀ r ∈ Icc (0 : ℝ) t, g r = s103bQ d s (ρ r) (w r))
    (hg2 : ∀ r ∈ Icc (0 : ℝ) t, Bd 2 Kg (g r))
    (hgc : ∀ r₀ ∈ Icc (0 : ℝ) t, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Icc (0 : ℝ) t, |r - r₀| < δ →
      ∀ y, |g r y - g r₀ y| ≤ ε)
    (hm : ∀ r ∈ Icc (0 : ℝ) t, ∀ x, w r x = ouSg (ouQ d a) β⁻¹ (t - r) ψ x +
      ∫ v in r..t, ouSg (ouQ d a) β⁻¹ (v - r) (g v) x) :
    IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t ψ w := by
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  set Q := ouQ d a with hQ
  set C := (quadraticGradientDyn d s a β).coeff ρ with hC
  have hrev : ∀ r ∈ Icc (0 : ℝ) t, t - (t - r) = r := fun r _ => by ring
  -- the forward-time family
  have hGF : GFam t Kg (fun σ => g (t - σ)) :=
    ⟨fun σ hσ => by simpa using (hg2 (t - σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩).1,
      fun σ hσ => (hg2 (t - σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩).2,
      fun σ₀ h0 ε hε => by
        obtain ⟨δ, hδ, h⟩ := hgc (t - σ₀) ⟨by linarith [h0.2], by linarith [h0.1]⟩ ε hε
        exact ⟨δ, hδ, fun σ hσ hd y => h (t - σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
          (by rw [show t - σ - (t - σ₀) = -(σ - σ₀) by ring, abs_neg]; exact hd) y⟩⟩
  set W : ℝ → Euc d → ℝ := fun τ => w (t - τ) with hWdef
  have hWm : ∀ τ ∈ Icc (0 : ℝ) t, ∀ x, W τ x = ouSg Q β⁻¹ τ ψ x + Dd Q β⁻¹ (fun σ => g (t - σ)) τ τ x := by
    intro τ hτ x
    have hr : t - τ ∈ Icc (0 : ℝ) t := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    have := hm (t - τ) hr x
    rw [show t - (t - τ) = τ by ring] at this
    rw [hWdef]; simp only
    rw [this, c4_mild_rev Q β⁻¹ t g τ x]
  have hW2 : ∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ 2 (W τ) ∧ ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i (W τ) y‖ ≤ Bw := by
    intro τ hτ
    have hr : t - τ ∈ Icc (0 : ℝ) t := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    exact ⟨by simpa using (hw _ hr).1, (hw _ hr).2⟩
  have hWc : ∀ i ≤ 2, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (W p.1) p.2) (Icc 0 t ×ˢ univ) := by
    intro i hi
    have hf : ContinuousOn (fun p : ℝ × Euc d => (t - p.1, p.2)) (Icc 0 t ×ˢ univ) :=
      ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
    exact (hwc i hi).comp hf (fun p hp => ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩, mem_univ _⟩)
  have hψc : Continuous ψ := by simpa using hψ.1.continuous
  have hψb : ∀ y, |ψ y| ≤ Bψ := fun y => by
    have := hψ.2 0 (Nat.zero_le _) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hgrev : ∀ r ∈ Icc (0 : ℝ) t, ∀ x, generatorW C r (w r) x = ul5A Q β⁻¹ (w r) x + g r x := by
    intro r hr x
    rw [c4_gen_eq s a β ρ r (w r) x, hg r hr]
  -- joint continuity of `g`
  have hgjoint : ContinuousOn (fun p : ℝ × Euc d => g p.1 p.2) (Icc 0 t ×ˢ univ) := by
    intro p hp
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ1, hδ1, h1⟩ := hgc p.1 hp.1 (ε / 2) (by positivity)
    have hc0 : Continuous (g p.1) := (by simpa using (hg2 p.1 hp.1).1 : ContDiff ℝ 2 (g p.1)).continuous
    obtain ⟨δ2, hδ2, h2⟩ := Metric.continuous_iff.1 hc0 p.2 (ε / 2) (by positivity)
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun q hq hd => ?_⟩
    have hd1 : |q.1 - p.1| < δ1 := by
      have : dist q.1 p.1 ≤ dist q p := by
        rw [Prod.dist_eq]; exact le_max_left _ _
      rw [← Real.dist_eq]; exact lt_of_le_of_lt this (hd.trans_le (min_le_left _ _))
    have hd2 : dist q.2 p.2 < δ2 := by
      have : dist q.2 p.2 ≤ dist q p := by
        rw [Prod.dist_eq]; exact le_max_right _ _
      exact lt_of_le_of_lt this (hd.trans_le (min_le_right _ _))
    have a1 := h1 q.1 hq.1 hd1 q.2
    have a2 := h2 q.2 hd2
    rw [Real.dist_eq] at a2 ⊢
    calc |g q.1 q.2 - g p.1 p.2| = |(g q.1 q.2 - g p.1 q.2) + (g p.1 q.2 - g p.1 p.2)| := by ring_nf
      _ ≤ |g q.1 q.2 - g p.1 q.2| + |g p.1 q.2 - g p.1 p.2| := abs_add_le _ _
      _ < ε := by linarith
  refine ⟨fun r hr => by simpa using (hw r hr).1, fun j hj => ⟨Bw, fun r hr x => (hw r hr).2 j hj x⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have h := hwc j hj
    have hf : Continuous (fun p : Icc (0 : ℝ) t × Euc d => ((p.1 : ℝ), p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact h.comp_continuous hf (fun p => ⟨p.1.2, mem_univ _⟩)
  · rw [hwt]
  · intro x r hr
    have hr' : t - r ∈ Ioo 0 t := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have hd := c4_hasDerivAt Q hν hGF hψc hψb hWm hW2 hWc hr' x
    have hc := hd.scomp r ((hasDerivAt_id r).const_sub t)
    have e : ((fun τ' => W τ' x) ∘ (HSub.hSub t : ℝ → ℝ)) = fun r' => w r' x := by
      funext r'; simp [hWdef]
    rw [e] at hc
    have hrI : r ∈ Icc (0 : ℝ) t := ⟨hr.1.le, hr.2.le⟩
    have := hgrev r hrI x
    refine hc.congr_deriv ?_
    rw [this]
    simp only [hWdef, show t - (t - r) = r by ring, id]
    ring
  · have hA := c4_gen_cont2 Q β⁻¹ (hwc 1 (by norm_num)) (hwc 2 le_rfl)
    have hS := hA.add hgjoint
    have hf : Continuous (fun p : Icc (0 : ℝ) t × Euc d => ((p.1 : ℝ), p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    refine (hS.comp_continuous hf (fun p => ⟨p.1.2, mem_univ _⟩)).congr fun p => ?_
    simp only [Function.comp]
    exact (hgrev p.1 p.1.2 p.2).symm
  · obtain ⟨b, hb, hbm⟩ := ul5_matVec_le Q
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
    have hBw : 0 ≤ Bw := (norm_nonneg _).trans ((hw 0 h0).2 0 (Nat.zero_le _) 0)
    have hKg : 0 ≤ Kg := (norm_nonneg _).trans ((hg2 0 h0).2 0 (Nat.zero_le _) 0)
    refine ⟨|β⁻¹| * (d * Bw) + Bw * b + Kg, fun r hr x => ?_⟩
    rw [hgrev r hr x]
    have h1 := ul5_A_bound Q β⁻¹ (f := w r) (b1 := Bw) (b2 := Bw) x ((hw r hr).2 1 (by norm_num) x)
      ((hw r hr).2 2 le_rfl x)
    have h2 : |g r x| ≤ Kg := by
      have := (hg2 r hr).2 0 (Nat.zero_le _) x
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    have h3 : Bw * ‖Torus.matVec Q x‖ ≤ Bw * (b * ‖x‖) := mul_le_mul_of_nonneg_left (hbm x) hBw
    have hx := norm_nonneg x
    have hν0 : 0 ≤ |β⁻¹| * (d * Bw) := by positivity
    calc |ul5A Q β⁻¹ (w r) x + g r x| ≤ |ul5A Q β⁻¹ (w r) x| + |g r x| := abs_add_le _ _
      _ ≤ |β⁻¹| * (d * Bw) + Bw * (b * ‖x‖) + Kg := by linarith
      _ ≤ (|β⁻¹| * (d * Bw) + Bw * b + Kg) * (1 + ‖x‖) := by
        have : 0 ≤ Bw * b := mul_nonneg hBw hb
        nlinarith [mul_nonneg hx hν0, mul_nonneg hx this, mul_nonneg hx hKg]

end HRS.MS.S104e.C
