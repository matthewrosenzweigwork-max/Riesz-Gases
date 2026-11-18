import Mathlib

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open Filter Topology Set

namespace HRS.MS.S113X2B

/-- The convex power regularization `Φ_{p,ε}(z) = (z+ε)^p - ε^p - p ε^{p-1} z`. -/
def s113b_Phi (p e z : ℝ) : ℝ := (z + e) ^ p - e ^ p - p * e ^ (p - 1) * z
/-- `∂_z Φ_{p,ε}`. -/
def s113b_Phi1 (p e z : ℝ) : ℝ := p * ((z + e) ^ (p - 1) - e ^ (p - 1))
/-- `∂_z² Φ_{p,ε}`. -/
def s113b_Phi2 (p e z : ℝ) : ℝ := p * (p - 1) * (z + e) ^ (p - 2)
/-- `∂_p Φ_{p,ε}`. -/
def s113b_PhiP (p e z : ℝ) : ℝ :=
  (z + e) ^ p * Real.log (z + e) - e ^ p * Real.log e - e ^ (p - 1) * z - p * e ^ (p - 1) * Real.log e * z
/-- `z Φ' - Φ`. -/
def s113b_Theta (p e z : ℝ) : ℝ := z * s113b_Phi1 p e z - s113b_Phi p e z

/-! ### Values at zero -/

theorem s113b_Phi_zero (p e : ℝ) : s113b_Phi p e 0 = 0 := by simp [s113b_Phi]

theorem s113b_Phi1_zero (p e : ℝ) : s113b_Phi1 p e 0 = 0 := by simp [s113b_Phi1]

theorem s113b_Theta_zero (p e : ℝ) : s113b_Theta p e 0 = 0 := by simp [s113b_Theta, s113b_Phi_zero]

/-! ### Sign and monotonicity -/

theorem s113b_Phi1_nonneg {p e z : ℝ} (hp : 1 < p) (he : 0 < e) (hz : 0 ≤ z) :
    0 ≤ s113b_Phi1 p e z := by
  unfold s113b_Phi1
  have h : e ^ (p - 1) ≤ (z + e) ^ (p - 1) :=
    Real.rpow_le_rpow he.le (by linarith) (by linarith)
  exact mul_nonneg (by linarith) (by linarith)

theorem s113b_Phi2_nonneg {p e z : ℝ} (hp : 1 < p) (he : 0 < e) (hz : -e < z) :
    0 ≤ s113b_Phi2 p e z := by
  unfold s113b_Phi2
  have : 0 < z + e := by linarith
  exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (Real.rpow_nonneg this.le _)

theorem s113b_Phi1_monotoneOn {p e : ℝ} (hp : 1 < p) (he : 0 < e) :
    MonotoneOn (s113b_Phi1 p e) (Set.Ici 0) := by
  intro x hx y hy hxy
  unfold s113b_Phi1
  have hx' : (0:ℝ) ≤ x := hx
  have h : (x + e) ^ (p - 1) ≤ (y + e) ^ (p - 1) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-! ### Derivatives -/

theorem s113b_hasDerivAt_Phi {p e z : ℝ} (hp : 1 < p) (he : 0 < e) (hz : -e < z) :
    HasDerivAt (s113b_Phi p e) (s113b_Phi1 p e z) z := by
  have hz' : 0 < z + e := by linarith
  have h1 : HasDerivAt (fun y : ℝ => y + e) 1 z := (hasDerivAt_id z).add_const e
  have h2 : HasDerivAt (fun y : ℝ => (y + e) ^ p) (1 * p * (z + e) ^ (p - 1)) z :=
    h1.rpow_const (Or.inl hz'.ne')
  have h3 : HasDerivAt (fun y : ℝ => p * e ^ (p - 1) * y) (p * e ^ (p - 1)) z := by
    simpa using (hasDerivAt_id z).const_mul (p * e ^ (p - 1))
  have h4 := (h2.sub_const (e ^ p)).sub h3
  refine (h4.congr_deriv ?_)
  unfold s113b_Phi1
  ring

theorem s113b_hasDerivAt_Phi1 {p e z : ℝ} (hp : 1 < p) (he : 0 < e) (hz : -e < z) :
    HasDerivAt (s113b_Phi1 p e) (s113b_Phi2 p e z) z := by
  have hz' : 0 < z + e := by linarith
  have h1 : HasDerivAt (fun y : ℝ => y + e) 1 z := (hasDerivAt_id z).add_const e
  have h2 : HasDerivAt (fun y : ℝ => (y + e) ^ (p - 1)) (1 * (p - 1) * (z + e) ^ (p - 1 - 1)) z :=
    h1.rpow_const (Or.inl hz'.ne')
  have h4 := ((h2.sub_const (e ^ (p - 1))).const_mul p)
  refine (h4.congr_deriv ?_)
  unfold s113b_Phi2
  have : p - 1 - 1 = p - 2 := by ring
  rw [this]
  ring

theorem s113b_hasDerivAt_Phi_p {p e z : ℝ} (he : 0 < e) (hz : -e < z) :
    HasDerivAt (fun p' : ℝ => s113b_Phi p' e z) (s113b_PhiP p e z) p := by
  have hz' : 0 < z + e := by linarith
  have h1 : HasDerivAt (fun q : ℝ => (z + e) ^ q) ((z + e) ^ p * Real.log (z + e)) p :=
    (Real.hasStrictDerivAt_const_rpow hz' p).hasDerivAt
  have h2 : HasDerivAt (fun q : ℝ => e ^ q) (e ^ p * Real.log e) p :=
    (Real.hasStrictDerivAt_const_rpow he p).hasDerivAt
  have h3 : HasDerivAt (fun q : ℝ => e ^ (q - 1)) (e ^ (p - 1) * Real.log e) p :=
    ((Real.hasStrictDerivAt_const_rpow he (p - 1)).hasDerivAt).comp_sub_const p 1
  have h4 := (((hasDerivAt_id p).mul h3).mul_const z)
  have h5 := (h1.sub h2).sub h4
  refine (h5.congr_deriv ?_)
  unfold s113b_PhiP
  simp only [id]
  ring

/-! ### Nonnegativity of `Φ` -/

theorem s113b_Phi_nonneg {p e z : ℝ} (hp : 1 < p) (he : 0 < e) (hz : 0 ≤ z) :
    0 ≤ s113b_Phi p e z := by
  have hmono : MonotoneOn (s113b_Phi p e) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro x hx
      have hx' : (0:ℝ) ≤ x := hx
      exact (s113b_hasDerivAt_Phi hp he (by linarith)).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : (0:ℝ) < x := by simpa using hx
      exact (s113b_hasDerivAt_Phi hp he (by linarith)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : (0:ℝ) < x := by simpa using hx
      rw [(s113b_hasDerivAt_Phi hp he (by linarith)).deriv]
      exact s113b_Phi1_nonneg hp he hx'.le
  have := hmono (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 hz) hz
  rwa [s113b_Phi_zero] at this

/-! ### Joint continuity -/

theorem s113b_continuousOn_Phi (e : ℝ) (he : 0 < e) :
    ContinuousOn (fun x : ℝ × ℝ => s113b_Phi x.1 e x.2) (Set.Ioi 0 ×ˢ Set.Ici 0) := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have h1 : (0:ℝ) < x.1 := hx1
  have h2 : (0:ℝ) ≤ x.2 := hx2
  have hb : 0 < x.2 + e := by linarith
  apply ContinuousAt.continuousWithinAt
  unfold s113b_Phi
  have hc1 : ContinuousAt (fun y : ℝ × ℝ => (y.2 + e) ^ y.1) x :=
    ContinuousAt.rpow (by fun_prop) (by fun_prop) (Or.inl hb.ne')
  have hc2 : ContinuousAt (fun y : ℝ × ℝ => e ^ y.1) x :=
    ContinuousAt.rpow (by fun_prop) (by fun_prop) (Or.inl he.ne')
  have hc3 : ContinuousAt (fun y : ℝ × ℝ => e ^ (y.1 - 1)) x :=
    ContinuousAt.rpow (by fun_prop) (by fun_prop) (Or.inl he.ne')
  exact (hc1.sub hc2).sub ((continuousAt_fst.mul hc3).mul continuousAt_snd)

theorem s113b_continuousOn_Phi1 (e : ℝ) (he : 0 < e) :
    ContinuousOn (fun x : ℝ × ℝ => s113b_Phi1 x.1 e x.2) (Set.Ioi 0 ×ˢ Set.Ici 0) := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have h2 : (0:ℝ) ≤ x.2 := hx2
  have hb : 0 < x.2 + e := by linarith
  apply ContinuousAt.continuousWithinAt
  unfold s113b_Phi1
  have hc1 : ContinuousAt (fun y : ℝ × ℝ => (y.2 + e) ^ (y.1 - 1)) x :=
    ContinuousAt.rpow (by fun_prop) (by fun_prop) (Or.inl hb.ne')
  have hc3 : ContinuousAt (fun y : ℝ × ℝ => e ^ (y.1 - 1)) x :=
    ContinuousAt.rpow (by fun_prop) (by fun_prop) (Or.inl he.ne')
  exact continuousAt_fst.mul (hc1.sub hc3)

theorem s113b_continuousOn_Phi2 (e : ℝ) (he : 0 < e) :
    ContinuousOn (fun x : ℝ × ℝ => s113b_Phi2 x.1 e x.2) (Set.Ioi 0 ×ˢ Set.Ici 0) := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have h2 : (0:ℝ) ≤ x.2 := hx2
  have hb : 0 < x.2 + e := by linarith
  apply ContinuousAt.continuousWithinAt
  unfold s113b_Phi2
  have hc1 : ContinuousAt (fun y : ℝ × ℝ => (y.2 + e) ^ (y.1 - 2)) x :=
    ContinuousAt.rpow (by fun_prop) (by fun_prop) (Or.inl hb.ne')
  exact (continuousAt_fst.mul (continuousAt_fst.sub continuousAt_const)).mul hc1

theorem s113b_continuousOn_PhiP (e : ℝ) (he : 0 < e) :
    ContinuousOn (fun x : ℝ × ℝ => s113b_PhiP x.1 e x.2) (Set.Ioi 0 ×ˢ Set.Ici 0) := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have h2 : (0:ℝ) ≤ x.2 := hx2
  have hb : 0 < x.2 + e := by linarith
  apply ContinuousAt.continuousWithinAt
  unfold s113b_PhiP
  have hc1 : ContinuousAt (fun y : ℝ × ℝ => (y.2 + e) ^ y.1) x :=
    ContinuousAt.rpow (by fun_prop) (by fun_prop) (Or.inl hb.ne')
  have hc2 : ContinuousAt (fun y : ℝ × ℝ => e ^ y.1) x :=
    ContinuousAt.rpow (by fun_prop) (by fun_prop) (Or.inl he.ne')
  have hc3 : ContinuousAt (fun y : ℝ × ℝ => e ^ (y.1 - 1)) x :=
    ContinuousAt.rpow (by fun_prop) (by fun_prop) (Or.inl he.ne')
  have hl1 : ContinuousAt (fun y : ℝ × ℝ => Real.log (y.2 + e)) x :=
    ContinuousAt.log (by fun_prop) hb.ne'
  have hl2 : ContinuousAt (fun y : ℝ × ℝ => Real.log e) x := continuousAt_const
  exact (((hc1.mul hl1).sub (hc2.mul hl2)).sub (hc3.mul continuousAt_snd)).sub
    ((((continuousAt_fst.mul hc3).mul hl2).mul continuousAt_snd))

theorem s113b_continuousOn_Theta (e : ℝ) (he : 0 < e) :
    ContinuousOn (fun x : ℝ × ℝ => s113b_Theta x.1 e x.2) (Set.Ioi 0 ×ˢ Set.Ici 0) := by
  unfold s113b_Theta
  exact (continuousOn_snd.mul (s113b_continuousOn_Phi1 e he)).sub (s113b_continuousOn_Phi e he)

/-! ### Limits as `ε → 0+` -/

theorem s113b_tendsto_rpow_mul_log {a : ℝ} (ha : 0 < a) :
    Tendsto (fun e : ℝ => e ^ a * Real.log e) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have := tendsto_log_mul_rpow_nhdsGT_zero ha
  simpa [mul_comm] using this

theorem s113b_tendsto_Phi {p : ℝ} (hp : 1 < p) (z : ℝ) (hz : 0 ≤ z) :
    Tendsto (fun e : ℝ => s113b_Phi p e z) (nhdsWithin 0 (Set.Ioi 0)) (nhds (z ^ p)) := by
  have hc : ContinuousAt (fun e : ℝ => (z + e) ^ p - e ^ p - p * e ^ (p - 1) * z) 0 := by
    have h1 : ContinuousAt (fun e : ℝ => (z + e) ^ p) 0 :=
      ContinuousAt.rpow_const (by fun_prop) (Or.inr (by linarith))
    have h2 : ContinuousAt (fun e : ℝ => e ^ p) 0 :=
      Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))
    have h3 : ContinuousAt (fun e : ℝ => e ^ (p - 1)) 0 :=
      Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))
    exact (h1.sub h2).sub ((continuousAt_const.mul h3).mul continuousAt_const)
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  have hv : (z + 0) ^ p - (0:ℝ) ^ p - p * (0:ℝ) ^ (p - 1) * z = z ^ p := by
    rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]; simp
  rw [hv] at h
  exact h

theorem s113b_tendsto_Phi1 {p : ℝ} (hp : 1 < p) (z : ℝ) (hz : 0 ≤ z) :
    Tendsto (fun e : ℝ => s113b_Phi1 p e z) (nhdsWithin 0 (Set.Ioi 0)) (nhds (p * z ^ (p - 1))) := by
  have hc : ContinuousAt (fun e : ℝ => p * ((z + e) ^ (p - 1) - e ^ (p - 1))) 0 := by
    have h1 : ContinuousAt (fun e : ℝ => (z + e) ^ (p - 1)) 0 :=
      ContinuousAt.rpow_const (by fun_prop) (Or.inr (by linarith))
    have h3 : ContinuousAt (fun e : ℝ => e ^ (p - 1)) 0 :=
      Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))
    exact continuousAt_const.mul (h1.sub h3)
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  have hv : p * ((z + 0) ^ (p - 1) - (0:ℝ) ^ (p - 1)) = p * z ^ (p - 1) := by
    rw [Real.zero_rpow (by linarith)]; simp
  rw [hv] at h
  exact h

theorem s113b_tendsto_Theta {p : ℝ} (hp : 1 < p) (z : ℝ) (hz : 0 ≤ z) :
    Tendsto (fun e : ℝ => s113b_Theta p e z) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((p - 1) * z ^ p)) := by
  have h := (s113b_tendsto_Phi1 hp z hz).const_mul z |>.sub (s113b_tendsto_Phi hp z hz)
  have hv : z * (p * z ^ (p - 1)) - z ^ p = (p - 1) * z ^ p := by
    rcases hz.eq_or_lt with h0 | h0
    · subst h0
      have a : (0:ℝ) ^ p = 0 := Real.zero_rpow (by linarith)
      simp [a]
    · have : z ^ p = z ^ (p - 1) * z := by
        rw [Real.rpow_sub_one h0.ne']; field_simp
      rw [this]; ring
  rw [hv] at h
  exact h

theorem s113b_tendsto_PhiP {p : ℝ} (hp : 1 < p) (z : ℝ) (hz : 0 ≤ z) :
    Tendsto (fun e : ℝ => s113b_PhiP p e z) (nhdsWithin 0 (Set.Ioi 0)) (nhds (z ^ p * Real.log z)) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hT1 : Tendsto (fun e : ℝ => (z + e) ^ p * Real.log (z + e)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (z ^ p * Real.log z)) := by
    rcases hz.eq_or_lt with h0 | h0
    · subst h0
      rw [Real.zero_rpow hp0.ne', zero_mul]
      simpa using s113b_tendsto_rpow_mul_log hp0
    · have hc : ContinuousAt (fun e : ℝ => (z + e) ^ p * Real.log (z + e)) 0 := by
        have h1 : ContinuousAt (fun e : ℝ => (z + e) ^ p) 0 :=
          ContinuousAt.rpow_const (by fun_prop) (Or.inr hp0.le)
        have h2 : ContinuousAt (fun e : ℝ => Real.log (z + e)) 0 :=
          ContinuousAt.log (by fun_prop) (by simpa using h0.ne')
        exact h1.mul h2
      have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using h
  have hT2 := s113b_tendsto_rpow_mul_log hp0
  have hT3 : Tendsto (fun e : ℝ => e ^ (p - 1) * z) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h3 : ContinuousAt (fun e : ℝ => e ^ (p - 1) * z) 0 :=
      (Real.continuousAt_rpow_const _ _ (Or.inr hp1.le)).mul continuousAt_const
    have h := h3.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa [Real.zero_rpow hp1.ne'] using h
  have hT4 : Tendsto (fun e : ℝ => p * (e ^ (p - 1) * Real.log e) * z) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using ((s113b_tendsto_rpow_mul_log hp1).const_mul p).mul_const z
  have h := ((hT1.sub hT2).sub hT3).sub hT4
  simp only [sub_zero] at h
  refine h.congr (fun e => ?_)
  unfold s113b_PhiP
  ring

/-! ### Uniform bounds -/

theorem s113b_xlog_le_one {x p p1 : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hp1 : 0 < p1) (hp : p1 ≤ p) :
    |x ^ p * Real.log x| ≤ 1 / p1 := by
  have hlog : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
  have hxp : x ^ p ≤ x ^ p1 := Real.rpow_le_rpow_of_exponent_ge hx hx1 hp
  have hxp0 : 0 ≤ x ^ p := Real.rpow_nonneg hx.le _
  have hl : -Real.log x ≤ (x⁻¹) ^ p1 / p1 := by
    have := Real.log_le_rpow_div (x := x⁻¹) (inv_nonneg.2 hx.le) hp1
    rwa [Real.log_inv] at this
  rw [abs_mul, abs_of_nonneg hxp0, abs_of_nonpos hlog]
  calc x ^ p * -Real.log x ≤ x ^ p1 * ((x⁻¹) ^ p1 / p1) :=
        mul_le_mul hxp hl (by linarith [Real.log_nonpos hx.le hx1]) (Real.rpow_nonneg hx.le _)
    _ = 1 / p1 := by
        rw [Real.inv_rpow hx.le]
        have : x ^ p1 ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
        field_simp

theorem s113b_xlog_bound {x A p p1 p2 : ℝ} (hx : 0 < x) (hxA : x ≤ A) (hA : 1 ≤ A) (hp1 : 0 < p1)
    (hp : p1 ≤ p) (hp' : p ≤ p2) :
    |x ^ p * Real.log x| ≤ 1 / p1 + A ^ p2 * Real.log A := by
  have hA0 : 0 < A := by linarith
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hApos : 0 ≤ A ^ p2 * Real.log A := mul_nonneg (Real.rpow_nonneg hA0.le _) hlogA
  rcases le_or_gt x 1 with h1 | h1
  · have := s113b_xlog_le_one hx h1 hp1 hp
    linarith
  · have hlogx : 0 ≤ Real.log x := Real.log_nonneg h1.le
    have hxp : x ^ p ≤ A ^ p2 :=
      calc x ^ p ≤ A ^ p := Real.rpow_le_rpow hx.le hxA (by linarith)
        _ ≤ A ^ p2 := Real.rpow_le_rpow_of_exponent_le hA hp'
    have hlx : Real.log x ≤ Real.log A := Real.log_le_log hx hxA
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _), abs_of_nonneg hlogx]
    have : 0 < 1 / p1 := by positivity
    have := mul_le_mul hxp hlx hlogx (Real.rpow_nonneg hA0.le _)
    linarith

theorem s113b_uniform_bound (p1 p2 B : ℝ) (hp1 : 1 < p1) :
    ∃ C : ℝ, ∀ p ∈ Set.Icc p1 p2, ∀ e ∈ Set.Ioc (0:ℝ) 1, ∀ z ∈ Set.Icc (0:ℝ) B,
      |s113b_Phi p e z| ≤ C ∧ |s113b_Theta p e z| ≤ C ∧ |s113b_PhiP p e z| ≤ C ∧
        |s113b_Phi1 p e z| ≤ C := by
  set A : ℝ := |B| + 1 with hAdef
  have hA : 1 ≤ A := by have := abs_nonneg B; linarith
  have hA0 : 0 < A := by linarith
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hp10 : 0 < p1 := by linarith
  have hp11 : 0 < p1 - 1 := by linarith
  set P : ℝ := A ^ p2 + 1 + |p2| * A with hP
  set Q : ℝ := |p2| * A ^ (p2 - 1) with hQ
  set K1 : ℝ := 1 / p1 + A ^ p2 * Real.log A with hK1
  set K3 : ℝ := 1 / (p1 - 1) with hK3
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hK10 : 0 ≤ K1 := by
    have : 0 ≤ A ^ p2 * Real.log A := mul_nonneg (Real.rpow_nonneg hA0.le _) hlogA
    have : 0 < 1 / p1 := by positivity
    linarith
  have hK30 : 0 ≤ K3 := by positivity
  refine ⟨P + Q + (K1 + 1 / p1 + A + |p2| * A * K3) + (A * Q + P), ?_⟩
  intro p hp e he z hz
  obtain ⟨hpa, hpb⟩ := hp
  obtain ⟨he0, he1⟩ := he
  obtain ⟨hz0, hzB⟩ := hz
  have hp0 : 0 < p := by linarith
  have hpp2 : p ≤ |p2| := le_trans hpb (le_abs_self p2)
  have hzA : z ≤ A := by have := le_abs_self B; linarith
  have hzepos : 0 < z + e := by linarith
  have hzeA : z + e ≤ A := by have := le_abs_self B; linarith
  have h1 : (z + e) ^ p ≤ A ^ p2 :=
    calc (z + e) ^ p ≤ A ^ p := Real.rpow_le_rpow hzepos.le hzeA hp0.le
      _ ≤ A ^ p2 := Real.rpow_le_rpow_of_exponent_le hA hpb
  have h1' : 0 ≤ (z + e) ^ p := Real.rpow_nonneg hzepos.le _
  have h2 : e ^ p ≤ 1 := Real.rpow_le_one he0.le he1 hp0.le
  have h2' : 0 ≤ e ^ p := Real.rpow_nonneg he0.le _
  have h3 : e ^ (p - 1) ≤ 1 := Real.rpow_le_one he0.le he1 (by linarith)
  have h3' : 0 ≤ e ^ (p - 1) := Real.rpow_nonneg he0.le _
  have h4 : (z + e) ^ (p - 1) ≤ A ^ (p2 - 1) :=
    calc (z + e) ^ (p - 1) ≤ A ^ (p - 1) := Real.rpow_le_rpow hzepos.le hzeA (by linarith)
      _ ≤ A ^ (p2 - 1) := Real.rpow_le_rpow_of_exponent_le hA (by linarith)
  have h4' : 0 ≤ (z + e) ^ (p - 1) := Real.rpow_nonneg hzepos.le _
  have h5 : |(z + e) ^ p * Real.log (z + e)| ≤ K1 :=
    s113b_xlog_bound hzepos hzeA hA hp10 hpa hpb
  have h6 : |e ^ p * Real.log e| ≤ 1 / p1 := s113b_xlog_le_one he0 he1 hp10 hpa
  have h7 : |e ^ (p - 1) * Real.log e| ≤ K3 :=
    s113b_xlog_le_one he0 he1 hp11 (by linarith)
  -- bound on the linear term
  have hlin : p * e ^ (p - 1) * z ≤ |p2| * A := by
    have a1 : p * e ^ (p - 1) ≤ |p2| * 1 :=
      mul_le_mul hpp2 h3 h3' (abs_nonneg _)
    have a2 := mul_le_mul a1 hzA hz0 (by positivity)
    linarith
  have hlin0 : 0 ≤ p * e ^ (p - 1) * z := by positivity
  have hPhi : |s113b_Phi p e z| ≤ P := by
    unfold s113b_Phi
    rw [abs_le]; constructor <;> linarith
  have hPhi1_nn : 0 ≤ s113b_Phi1 p e z := s113b_Phi1_nonneg (by linarith) he0 hz0
  have hPhi1 : s113b_Phi1 p e z ≤ Q := by
    unfold s113b_Phi1
    have a1 : p * (z + e) ^ (p - 1) ≤ |p2| * A ^ (p2 - 1) :=
      mul_le_mul hpp2 h4 h4' (abs_nonneg _)
    have a2 : 0 ≤ p * e ^ (p - 1) := by positivity
    nlinarith
  have hPhi1' : |s113b_Phi1 p e z| ≤ Q := by
    rw [abs_of_nonneg hPhi1_nn]; exact hPhi1
  have hTheta : |s113b_Theta p e z| ≤ A * Q + P := by
    unfold s113b_Theta
    have a1 : z * s113b_Phi1 p e z ≤ A * Q := mul_le_mul hzA hPhi1 hPhi1_nn hA0.le
    have a2 : 0 ≤ z * s113b_Phi1 p e z := mul_nonneg hz0 hPhi1_nn
    have a3 := abs_le.1 hPhi
    rw [abs_le]; constructor <;> linarith
  have hPhiP : |s113b_PhiP p e z| ≤ K1 + 1 / p1 + A + |p2| * A * K3 := by
    have a1 : |(p * z) * (e ^ (p - 1) * Real.log e)| ≤ |p2| * A * K3 := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ p * z)]
      exact mul_le_mul (mul_le_mul hpp2 hzA hz0 (abs_nonneg _)) h7 (abs_nonneg _) (by positivity)
    have a2 : e ^ (p - 1) * z ≤ A := by
      have := mul_le_mul h3 hzA hz0 zero_le_one
      linarith
    have a2' : 0 ≤ e ^ (p - 1) * z := by positivity
    have eq : s113b_PhiP p e z = (z + e) ^ p * Real.log (z + e) - e ^ p * Real.log e
        - e ^ (p - 1) * z - (p * z) * (e ^ (p - 1) * Real.log e) := by
      unfold s113b_PhiP; ring
    rw [eq]
    have b1 := abs_le.1 h5
    have b2 := abs_le.1 h6
    have b3 := abs_le.1 a1
    rw [abs_le]; constructor <;> linarith
  have n1 : 0 ≤ A * Q := mul_nonneg hA0.le hQ0
  have n2 : 0 ≤ |p2| * A * K3 := mul_nonneg (mul_nonneg (abs_nonneg p2) hA0.le) hK30
  have n3 : 0 ≤ 1 / p1 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith

end HRS.MS.S113X2B
