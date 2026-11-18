import HRS.MS.MovAdjTie

/-!
# S10.3 (stationary half), part 4: the zeroth-order orbit bound (`W:lem:r2-window-orbits`, TeX S L8120-8150)

Prefix `s103_`, namespace `HRS.MS.MovAdj`-adjacent (`HRS.MS.R2WinOrb`).  `s103_zeroth`: for the stationary coefficient and a classical
adjoint solution `f` with terminal datum `φ`, `|φ| ≤ Bφ`, `√ρ₀ Πφ ∈ Σ^M`:
`|f r x| ≤ Bφ + C_z ‖√ρ₀ Πφ‖_{Σ^M}` uniformly in `0 ≤ r ≤ t`.  The Markov semigroup `sg` contracts the supremum norm; the source `β J f_v` is
bounded by `β K_J C_sp e^{-c_s (t-v)} N`; the Duhamel formula of `s67_duhamel_abs` closes the argument.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.PoisKolm HRS.MS.PoisHigh HRS.MS.Mov63 HRS.MS.FlowB HRS.MS.PoisSg
  HRS.MS.PoisFlow HRS.MS.PoisMax HRS.MS.MovAdj

variable {d : ℕ}

theorem s103_sg_abs_le {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → Fin d → ℝ) (q : ℝ) (B : Euc d → Euc d) (t : ℝ) (h : Euc d → ℝ) (x : Euc d)
    {S : ℝ} (hS : ∀ y, |h y| ≤ S) : |sg P W q B t h x| ≤ S := by
  unfold sg
  have := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun w' => h (flowMap q B (fun s => W s w') t x)) (C := S)
    (Eventually.of_forall fun w' => by simpa [Real.norm_eq_abs] using hS _)
  simpa [Real.norm_eq_abs, probReal_univ] using this

theorem s103_exp_integral_le {b : ℝ} (hb : 0 < b) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ σ in (0 : ℝ)..τ, Real.exp (-b * σ) ≤ 1 / b := by
  have hderiv : ∀ σ ∈ Set.uIcc (0 : ℝ) τ, HasDerivAt (fun σ => -(Real.exp (-b * σ) / b))
      (Real.exp (-b * σ)) σ := by
    intro σ _
    have h1 : HasDerivAt (fun σ : ℝ => -b * σ) (-b) σ := by
      simpa using (hasDerivAt_id σ).const_mul (-b)
    have h2 := (h1.exp).div_const b
    have h3 := h2.neg
    convert h3 using 1
    field_simp
  have hint : IntervalIntegrable (fun σ => Real.exp (-b * σ)) MeasureTheory.volume 0 τ :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [mul_zero, Real.exp_zero]
  have : 0 ≤ Real.exp (-b * τ) / b := div_nonneg (Real.exp_pos _).le hb.le
  have e : -(Real.exp (-b * τ) / b) - -(1 / b) = 1 / b - Real.exp (-b * τ) / b := by ring
  rw [e]; linarith

theorem s103_zeroth {s q β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρ₀ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ₀) (M : ℕ) (hM : (d : ℝ) / 2 + 5 < M) :
    ∃ Cz : ℝ, 0 ≤ Cz ∧ ∀ (t : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (Bφ : ℝ), 0 ≤ t →
      IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ₀)) t φ f →
      MemOsc (M : ℝ) (s67psi ρ₀ φ) → (∀ x, |φ x| ≤ Bφ) →
      ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, |f r x| ≤ Bφ + Cz * oscNorm (M : ℝ) (s67psi ρ₀ φ) := by
  have H : Mov2dTh d s β q ρ₀ := ⟨hd, hs0, hsd, hβ, hq, hρ⟩
  obtain ⟨cs, hcs, hspec⟩ := s67_spectral hd hs0 hsd β q hβ hq ρ₀ hρ
  have hMA : movA d s ≤ (M : ℝ) := by
    have h0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    unfold movA
    refine max_le (by linarith) (by linarith)
  obtain ⟨Csp, hCsp0, hCsp⟩ := hspec (M : ℝ) hMA
  obtain ⟨KJ, hKJ0, hKJ⟩ := s67_J_bound H 0 M (by simpa using hM)
  obtain ⟨B, hBeq, hR, hcbB⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd hq hβ hρ
  have hq' : 0 < β * q := mul_pos hβ hq
  obtain ⟨-, hgrad, -⟩ := HRS.MS.Mov0.mv0_sqrt_gauss hq' hR
  obtain ⟨Mb, hBm⟩ := hcbB 2
  have hBc : Continuous B := hBm.1.continuous
  obtain ⟨Ω, mΩ, P, hP, ℱ, W, hW⟩ := exists_isBrownianFiltration_type (Fin d)
  refine ⟨KJ * Csp / cs, by positivity, ?_⟩
  intro t φ f Bφ ht hf hosc hφB r hr x
  set N := oscNorm (M : ℝ) (s67psi ρ₀ φ) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hCz : 0 ≤ KJ * Csp / cs * N := by positivity
  have hBφ : 0 ≤ Bφ := (abs_nonneg _).trans (hφB 0)
  rcases eq_or_lt_of_le hr.2 with hrt | hrt
  · subst hrt
    rw [hf.terminal]
    linarith [hφB x]
  have ht0 : 0 < t := hr.1.trans_lt hrt
  have hspecT := hCsp t φ f ht hf hosc
  have hJ : ∀ v ∈ Icc (0 : ℝ) t, ContDiff ℝ ((0 + 4 : ℕ) : WithTop ℕ∞) (f v) ∧
      ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) (s67J d s ρ₀ (f v)) ∧
      ∀ i ≤ 0 + 2, ∀ x, ‖iteratedFDeriv ℝ i (s67J d s ρ₀ (f v)) x‖ ≤
        KJ * (Csp * Real.exp (-cs * (t - v)) * N) := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := hKJ (f v) (hf.isC12TestRd.memCb hv) (hspecT v hv).1
    exact ⟨h1, h2, fun i hi x => (h3 i hi x).trans
      (mul_le_mul_of_nonneg_left (hspecT v hv).2 hKJ0)⟩
  have hSb : ∃ KS : ℝ, ∀ v ∈ Icc (0 : ℝ) t, ∀ y, |s67J d s ρ₀ (f v) y| ≤ KS := by
    refine ⟨KJ * (Csp * N), fun v hv y => ?_⟩
    have h1 := (hJ v hv).2.2 0 (Nat.zero_le _) y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hKJ0)
    have he : Real.exp (-cs * (t - v)) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have : 0 ≤ t - v := sub_nonneg.2 hv.2
      nlinarith
    calc Csp * Real.exp (-cs * (t - v)) * N ≤ Csp * 1 * N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hCsp0) hN0
      _ = Csp * N := by ring
  have hDuh := s67_duhData hd hs0 hsd hq hβ hρ hBc hgrad hf hSb
  have hT : 0 < t / β := div_pos ht0 hβ
  have hτ0 : 0 ≤ (t - r) / β := div_nonneg (sub_nonneg.2 hr.2) hβ.le
  set τ := (t - r) / β with hτdef
  have hτ : τ ∈ Icc (0 : ℝ) (t / β) :=
    ⟨hτ0, div_le_div_of_nonneg_right (by linarith [hr.1]) hβ.le⟩
  have hτr : t - β * τ = r := by rw [hτdef]; field_simp; ring
  have hduh : f r x = sg P W (β * q) B τ φ x +
      ∫ σ in (0 : ℝ)..τ, sg P W (β * q) B (τ - σ) (fun y => β * s67J d s ρ₀ (f (t - β * σ)) y) x := by
    have := s67_duhamel_abs hW (Mb := Mb) hq' (le_refl 2) hBm hDuh hT hτ x
    simp only [mul_zero, sub_zero, hf.terminal, hτr] at this
    exact this
  rw [hduh]
  have h1 : |sg P W (β * q) B τ φ x| ≤ Bφ := s103_sg_abs_le P W (β * q) B τ φ x hφB
  have hbd : ∀ σ ∈ Icc (0 : ℝ) τ, ∀ y, |β * s67J d s ρ₀ (f (t - β * σ)) y| ≤
      (β * KJ * Csp * N) * Real.exp (-(cs * β) * σ) := by
    intro σ hs y
    have hv : t - β * σ ∈ Icc (0 : ℝ) t := s67_hmem hβ ⟨hs.1, hs.2.trans hτ.2⟩
    have h3 := (hJ _ hv).2.2 0 (Nat.zero_le _) y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h3
    have e3 : -cs * (t - (t - β * σ)) = -(cs * β) * σ := by ring
    rw [e3] at h3
    rw [abs_mul, abs_of_pos hβ]
    calc β * |s67J d s ρ₀ (f (t - β * σ)) y|
        ≤ β * (KJ * (Csp * Real.exp (-(cs * β) * σ) * N)) := mul_le_mul_of_nonneg_left h3 hβ.le
      _ = (β * KJ * Csp * N) * Real.exp (-(cs * β) * σ) := by ring
  have h2 : |∫ σ in (0 : ℝ)..τ, sg P W (β * q) B (τ - σ)
      (fun y => β * s67J d s ρ₀ (f (t - β * σ)) y) x| ≤ KJ * Csp / cs * N := by
    rw [← Real.norm_eq_abs]
    have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) (a := 0) (b := τ) hτ0
      (f := fun σ => sg P W (β * q) B (τ - σ) (fun y => β * s67J d s ρ₀ (f (t - β * σ)) y) x)
      (g := fun σ => (β * KJ * Csp * N) * Real.exp (-(cs * β) * σ))
      (by
        refine Eventually.of_forall fun σ hσ => ?_
        rw [Real.norm_eq_abs]
        exact s103_sg_abs_le P W (β * q) B (τ - σ) _ x (hbd σ ⟨hσ.1.le, hσ.2⟩))
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have hA : 0 ≤ β * KJ * Csp * N := by positivity
    have := mul_le_mul_of_nonneg_left (s103_exp_integral_le (mul_pos hcs hβ) hτ0) hA
    refine this.trans (le_of_eq ?_)
    field_simp
  calc |sg P W (β * q) B τ φ x + ∫ σ in (0 : ℝ)..τ, sg P W (β * q) B (τ - σ)
        (fun y => β * s67J d s ρ₀ (f (t - β * σ)) y) x|
      ≤ |sg P W (β * q) B τ φ x| + |∫ σ in (0 : ℝ)..τ, sg P W (β * q) B (τ - σ)
        (fun y => β * s67J d s ρ₀ (f (t - β * σ)) y) x| := abs_add_le _ _
    _ ≤ Bφ + KJ * Csp / cs * N := add_le_add h1 h2
    _ = Bφ + KJ * Csp / cs * N := rfl

end HRS.MS.R2WinOrb

end
