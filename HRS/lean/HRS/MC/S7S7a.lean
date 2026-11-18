import HRS.MC.S7S7aAux5
import HRS.PDE.EnergyR2Fn

/-!
# Packet `s7_S7a_mode_data` (relocation of `HRS.MC.Sec7.s7_S7a_mode_data`)

Proof.  For each mode `k`, `sed_B1_regular_proof` gives a smooth `a_k` with the response equation everywhere and
`mu(a_k) = 0`.  Quantitative bounds: `||a_k||_{H^n} <= A_n T_k` by induction on `n` (positivity of `K` for `n = 0`,
smoothing by the Riesz kernel and multiplication by the smooth density for the step), where `T_k = F <k>^{n - r}`
bounds `phi_k = <k>^{-r} e_k` (`cbNorm_trigTerm_le`).  The transport fields are built by the Fourier-side Poisson solve
(`s7a_v_exists`) and the Sobolev embedding `H^{d+2} -> C^1` (`s7a_cb1_le`) turns the `H`-bounds into `cbNorm 1` bounds;
`r = 2d + 6` leaves the margin `<k>^{-d-4} <= <k>^{-d-3}`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.MC.Sec7.S7a

open HRS HRS.Sec7 HRS.MC.SEdge HRS.PDE HRS.PDE.MFApriori HRS.PDE.MFPair HRS.PDE.MFThermalReg
  HRS.PDE.ClassicalPart

open Classical

variable {d : ℕ}

theorem s7a_phi_eq_trig (r : ℝ) (k : NonzeroLattice d) :
    s7_phi r k = trigTerm (if Lattice.IsPosHalf k.1 then Real.sqrt 2 * Lattice.jp k.1 ^ (-r) else 0)
      (if Lattice.IsPosHalf k.1 then 0 else Real.sqrt 2 * Lattice.jp k.1 ^ (-r)) k.1 := by
  funext x
  unfold s7_phi Torus.realMode trigTerm
  by_cases h : Lattice.IsPosHalf k.1
  · simp only [h, if_true]; ring
  · simp only [h, if_false]; ring

theorem s7a_trig_smooth (a b : ℝ) (k : Lattice d) : Torus.IsSmooth (trigTerm a b k) := by
  unfold Torus.IsSmooth Torus.IsCk
  rw [lift_trigTerm]
  have h : ContDiff ℝ ⊤ (fun t : ℝ => a * Real.cos t + b * Real.sin t) :=
    (contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin)
  exact (h.comp (Torus.freqFunctional k).contDiff).of_le (by exact_mod_cast le_top)

theorem s7a_phi_smooth (r : ℝ) (k : NonzeroLattice d) : Torus.IsSmooth (s7_phi r k) := by
  rw [s7a_phi_eq_trig]; exact s7a_trig_smooth _ _ _

/-- Uniform bounds on `phi_k` (sup norm and `H^N` norm) with `T_k = F <k>^{N - r}`. -/
theorem s7a_phi_bounds (r : ℝ) (N : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ k : NonzeroLattice d, (∀ x, |s7_phi r k x| ≤ F * Lattice.jp k.1 ^ ((N : ℝ) - r)) ∧
      HRS.PDE.hsNorm (N : ℝ) (coeffOf (s7_phi r k)) ≤ F * Lattice.jp k.1 ^ ((N : ℝ) - r) := by
  refine ⟨(N + 1) * Real.sqrt 2 * (1 + Real.sqrt ((1 + d) ^ N)), by positivity, fun k => ?_⟩
  have hjp : 0 < Lattice.jp k.1 := Torus.jp_pos _
  set a : ℝ := (if Lattice.IsPosHalf k.1 then Real.sqrt 2 * Lattice.jp k.1 ^ (-r) else 0) with ha
  set b : ℝ := (if Lattice.IsPosHalf k.1 then 0 else Real.sqrt 2 * Lattice.jp k.1 ^ (-r)) with hb
  have hab : |a| + |b| = Real.sqrt 2 * Lattice.jp k.1 ^ (-r) := by
    have h0 : 0 ≤ Real.sqrt 2 * Lattice.jp k.1 ^ (-r) := by positivity
    by_cases h : Lattice.IsPosHalf k.1
    · simp [ha, hb, h, abs_of_nonneg h0]
    · simp [ha, hb, h, abs_of_nonneg h0]
  have hcb := cbNorm_trigTerm_le a b k.1 N
  rw [hab] at hcb
  have hpow : Lattice.jp k.1 ^ N * Lattice.jp k.1 ^ (-r) = Lattice.jp k.1 ^ ((N : ℝ) - r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hjp, sub_eq_add_neg]
  have hB : Torus.cbNorm N (s7_phi r k) ≤ ((N : ℝ) + 1) * Real.sqrt 2 * Lattice.jp k.1 ^ ((N : ℝ) - r) := by
    rw [s7a_phi_eq_trig]
    refine hcb.trans (le_of_eq ?_)
    rw [← hpow]; ring
  have hCk : Torus.IsCk (N : WithTop ℕ∞) (s7_phi r k) := HRS.Q66.q66_isCk_of_smooth (s7a_phi_smooth r k) N
  have hB0 : 0 ≤ ((N : ℝ) + 1) * Real.sqrt 2 * Lattice.jp k.1 ^ ((N : ℝ) - r) := by positivity
  constructor
  · intro x
    refine (HRS.PDE.R2Aux.abs_le_cbNorm hCk x).trans (hB.trans ?_)
    have : 0 ≤ Real.sqrt ((1 + (d : ℝ)) ^ N) := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hB0 this]
  · obtain ⟨-, hn⟩ := ClassicalPart.memHs_coeffOf_cbNorm N (s7_phi r k) hCk
    unfold HRS.PDE.hsNorm
    have hcb0 : 0 ≤ Torus.cbNorm N (s7_phi r k) := ClassicalPart.cbNorm_nonneg'' N _
    calc Real.sqrt (hsNormSq (N : ℝ) (coeffOf (s7_phi r k)))
        ≤ Real.sqrt ((1 + (d : ℝ)) ^ N * Torus.cbNorm N (s7_phi r k) ^ 2) := Real.sqrt_le_sqrt hn
      _ = Real.sqrt ((1 + (d : ℝ)) ^ N) * Torus.cbNorm N (s7_phi r k) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hcb0]
      _ ≤ Real.sqrt ((1 + (d : ℝ)) ^ N) *
            (((N : ℝ) + 1) * Real.sqrt 2 * Lattice.jp k.1 ^ ((N : ℝ) - r)) :=
          mul_le_mul_of_nonneg_left hB (Real.sqrt_nonneg _)
      _ ≤ _ := by nlinarith [mul_nonneg hB0 (Real.sqrt_nonneg ((1 + (d : ℝ)) ^ N))]

theorem s7_S7a_mode_data_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (r : ℝ)
    (hr : r = 2 * (d : ℝ) + 6) (γ : ℝ) (hγ : 0 ≤ γ) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ (a : NonzeroLattice d → Torus d → ℝ) (v : NonzeroLattice d → Fin d → Torus d → ℝ) (C : ℝ),
      s7_ModeData d s γ ρ r a v C := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  -- the response `a_k` from B1
  have hB1 : ∀ k : NonzeroLattice d, ∃ a : Torus d → ℝ, Torus.IsSmooth a ∧
      (∀ x, a x + γ * Kop (periodicRiesz d s) (withDensityReal ρ) a x =
        projMean (withDensityReal ρ) (s7_phi r k) x) ∧ ∫ x, a x ∂(withDensityReal ρ) = 0 := by
    intro k
    obtain ⟨a, v, ha, -, -, hresp, hmean, -⟩ :=
      HRS.MC.SEdge.B1.sed_B1_regular_proof hd hs0 hs hγ hρ (s7a_phi_smooth r k)
    exact ⟨a, ha, hresp, hmean⟩
  choose a ha hresp hmean using hB1
  -- constants
  obtain ⟨F, hF0, hF⟩ := s7a_phi_bounds (d := d) r (d + 2)
  obtain ⟨A2, hA20, hA2⟩ := s7a_hs_bound hd hs0 hs hγ hρ (d + 2)
  obtain ⟨A1, hA10, hA1⟩ := s7a_hs_bound hd hs0 hs hγ hρ (d + 1)
  obtain ⟨P, hP0, hP⟩ := s7a_v_exists hd hρ
  obtain ⟨CS, hCS0, hCS⟩ := s7a_cb1_le (d := d)
  -- the bounds on `a_k`
  have hbd : ∀ k : NonzeroLattice d,
      HRS.PDE.hsNorm (((d + 2 : ℕ)) : ℝ) (coeffOf (a k)) ≤
        A2 * (F * Lattice.jp k.1 ^ (((d + 2 : ℕ) : ℝ) - r)) ∧
      HRS.PDE.hsNorm (((d + 1 : ℕ)) : ℝ) (coeffOf (a k)) ≤
        A1 * (F * Lattice.jp k.1 ^ (((d + 2 : ℕ) : ℝ) - r)) := by
    intro k
    obtain ⟨hF1, hF2⟩ := hF k
    have hφm : MemHs (((d + 2 : ℕ)) : ℝ) (coeffOf (s7_phi r k)) :=
      memHs_of_isCk (d + 2) _ (HRS.Q66.q66_isCk_of_smooth (s7a_phi_smooth r k) _)
    have hF2' : HRS.PDE.hsNorm (((d + 1 : ℕ)) : ℝ) (coeffOf (s7_phi r k)) ≤
        F * Lattice.jp k.1 ^ (((d + 2 : ℕ) : ℝ) - r) :=
      (hsNorm_mono_idx (by push_cast; linarith) hφm).trans hF2
    exact ⟨hA2 (a k) _ _ (ha k) (s7a_phi_smooth r k) hF1 hF2 (hresp k) (hmean k),
      hA1 (a k) _ _ (ha k) (s7a_phi_smooth r k) hF1 hF2' (hresp k) (hmean k)⟩
  -- the transport fields
  have hV : ∀ k : NonzeroLattice d, ∃ v : Fin d → Torus d → ℝ, (∀ j, Torus.IsSmooth (v j)) ∧
      (∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * a k x)) ∧
      ∀ j, HRS.PDE.hsNorm (((d + 2 : ℕ)) : ℝ) (coeffOf (v j)) ≤
        P * (A1 * (F * Lattice.jp k.1 ^ (((d + 2 : ℕ) : ℝ) - r))) := by
    intro k
    obtain ⟨v, hv1, hv2, hv3⟩ := hP (a k) (ha k) (hmean k)
    exact ⟨v, hv1, hv2, fun j => (hv3 j).trans (mul_le_mul_of_nonneg_left (hbd k).2 hP0)⟩
  choose v hvs hvdiv hvb using hV
  -- exponent comparison
  have hexp : ∀ k : NonzeroLattice d, Lattice.jp k.1 ^ (((d + 2 : ℕ) : ℝ) - r) ≤
      Lattice.jp k.1 ^ (-((d : ℝ) + 3)) := by
    intro k
    refine Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one _) ?_
    rw [hr]; push_cast; linarith
  refine ⟨a, v, CS * (A2 * F + P * (A1 * F)), ?_⟩
  refine ⟨fun k => ha k, fun k j => hvs k j, hresp, hmean, fun k x => hvdiv k x, ?_, ?_⟩
  · intro k
    have h1 := hCS (a k) (ha k)
    have h2 := (hbd k).1
    have hj0 : 0 ≤ Lattice.jp k.1 ^ (((d + 2 : ℕ) : ℝ) - r) := by
      have := Torus.jp_pos k.1; positivity
    calc Torus.cbNorm 1 (a k) ≤ CS * HRS.PDE.hsNorm (((d + 2 : ℕ)) : ℝ) (coeffOf (a k)) := h1
      _ ≤ CS * (A2 * (F * Lattice.jp k.1 ^ (((d + 2 : ℕ) : ℝ) - r))) :=
          mul_le_mul_of_nonneg_left h2 hCS0
      _ ≤ CS * (A2 * F + P * (A1 * F)) * Lattice.jp k.1 ^ (-((d : ℝ) + 3)) := by
          have hP1 : 0 ≤ P * (A1 * F) := by positivity
          have : A2 * F * Lattice.jp k.1 ^ (((d + 2 : ℕ) : ℝ) - r) ≤
              (A2 * F + P * (A1 * F)) * Lattice.jp k.1 ^ (-((d : ℝ) + 3)) := by
            calc _ ≤ A2 * F * Lattice.jp k.1 ^ (-((d : ℝ) + 3)) :=
                  mul_le_mul_of_nonneg_left (hexp k) (by positivity)
              _ ≤ _ := by
                  have : 0 ≤ Lattice.jp k.1 ^ (-((d : ℝ) + 3)) := by
                    have := Torus.jp_pos k.1; positivity
                  nlinarith [mul_nonneg hP1 this]
          nlinarith [mul_le_mul_of_nonneg_left this hCS0]
  · intro k j
    have h1 := hCS (v k j) (hvs k j)
    have h2 := hvb k j
    have hj0 : 0 ≤ Lattice.jp k.1 ^ (-((d : ℝ) + 3)) := by
      have := Torus.jp_pos k.1; positivity
    calc Torus.cbNorm 1 (v k j) ≤ CS * HRS.PDE.hsNorm (((d + 2 : ℕ)) : ℝ) (coeffOf (v k j)) := h1
      _ ≤ CS * (P * (A1 * (F * Lattice.jp k.1 ^ (((d + 2 : ℕ) : ℝ) - r)))) :=
          mul_le_mul_of_nonneg_left h2 hCS0
      _ ≤ CS * (P * (A1 * (F * Lattice.jp k.1 ^ (-((d : ℝ) + 3))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hexp k) hF0) hA10) hP0) hCS0
      _ ≤ _ := by
          have hP1 : 0 ≤ A2 * F := by positivity
          nlinarith [mul_nonneg (mul_nonneg hCS0 hP1) hj0]

end HRS.MC.Sec7.S7a

end
