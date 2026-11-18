import HRS.MS.S104eC1H

/-!
# S104E route C, packet C1 (part I): `c1_ou_strong` (strong continuity at `h = 0` and preservation of vanishing at infinity)
and linearity of `h ↦ ouSg (ouQ d a) ν h`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ContDiff

namespace HRS.MS.S104e.C
open HRS HRS.Whole HRS.MS.R2WinOrbNL HRS.MS.Ul HRS.MS.Wad
variable {d : ℕ}

theorem s104c1_vanB {a ν : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) {N : ℕ} {B : ℝ} {f : Euc d → ℝ} (hf : Bd N B f)
    (hv : VanB N f) {h : ℝ} (hh : 0 ≤ h) : VanB N (ouSg (ouQ d a) ν h f) := by
  intro i hi
  have hφc : Continuous (iteratedFDeriv ℝ i f) :=
    hf.1.continuous_iteratedFDeriv (by exact_mod_cast hi)
  have key := s104c1_van hφc (fun y => hf.2 i hi y) (hv i hi) (c := Real.exp (-a * h)) (s := s83_ms a ν h)
    (Real.exp_pos _).ne'
  refine squeeze_zero (fun x => norm_nonneg _) (fun x => ?_) key
  rw [s104c1_Drep ha hν hf hh hi x, norm_smul]
  have hc1 : ‖Real.exp (-a * h) ^ i‖ ≤ 1 := by
    rw [norm_pow, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact pow_le_one₀ (Real.exp_pos _).le (by rw [Real.exp_le_one_iff]; nlinarith)
  calc _ ≤ 1 * ‖∫ z, iteratedFDeriv ℝ i f (Real.exp (-a * h) • x + s83_ms a ν h • z)
        ∂(stdGaussian (Euc d))‖ := mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)
    _ = _ := one_mul _

theorem s104c1_strong_i {a ν : ℝ} (ha : 0 < a) (hν : 0 < ν) {N : ℕ} {B : ℝ} {f : Euc d → ℝ}
    (hf : Bd N B f) (hv : VanB N f) {i : ℕ} (hi : i ≤ N) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 ≤ h → h < δ → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (ouSg (ouQ d a) ν h f) x - iteratedFDeriv ℝ i f x‖ ≤ ε := by
  have hφc : Continuous (iteratedFDeriv ℝ i f) :=
    hf.1.continuous_iteratedFDeriv (by exact_mod_cast hi)
  have hB : 0 ≤ B := hf.nonneg
  obtain ⟨δc, hδc0, hclose⟩ := s104c1_close hφc (fun y => hf.2 i hi y) (hv i hi) (half_pos hε)
  refine ⟨min (min (δc / a) (δc ^ 2 / (2 * ν))) (ε / (2 * (N + 1) * (a + 1) * (B + 1))), by positivity, ?_⟩
  intro h hh hhδ x
  have h1 : h < δc / a := hhδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : h < δc ^ 2 / (2 * ν) := hhδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : h < ε / (2 * (N + 1) * (a + 1) * (B + 1)) := hhδ.trans_le (min_le_right _ _)
  set c : ℝ := Real.exp (-a * h) with hc
  set s : ℝ := s83_ms a ν h with hs
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c ≤ 1 := by rw [hc, Real.exp_le_one_iff]; nlinarith
  have hc1' : 1 - c ≤ a * h := by
    have := Real.add_one_le_exp (-a * h); rw [← hc] at this; linarith
  have hcδ : |c - 1| < δc := by
    rw [abs_of_nonpos (by linarith)]
    have : a * h < δc := by rwa [lt_div_iff₀ ha, mul_comm] at h1
    linarith
  have hs0 : 0 ≤ s := s83_ms_nonneg _ _ _
  have hs2 : s ^ 2 ≤ 2 * ν * h := by
    rw [hs, s83_ms_sq ha hν.le hh]
    have := Real.add_one_le_exp (-2 * a * h)
    have e : ν * (1 - Real.exp (-2 * a * h)) / a ≤ ν * (2 * a * h) / a := by
      refine div_le_div_of_nonneg_right ?_ ha.le
      exact mul_le_mul_of_nonneg_left (by linarith) hν.le
    refine e.trans (le_of_eq ?_)
    field_simp
  have hsδ : s < δc := by
    have : 2 * ν * h < δc ^ 2 := by rwa [lt_div_iff₀ (by positivity), mul_comm] at h2
    by_contra hcon
    push Not at hcon
    nlinarith
  have hI := hclose c s hcδ hs0 hsδ x
  rw [s104c1_Drep ha hν.le hf hh hi x]
  set I := ∫ z, iteratedFDeriv ℝ i f (c • x + s • z) ∂(stdGaussian (Euc d)) with hI'
  set φx := iteratedFDeriv ℝ i f x with hφx
  have hpow1 : c ^ i ≤ 1 := pow_le_one₀ hc0.le hc1
  have hpow2 : 1 - c ^ i ≤ i * (1 - c) := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ c - 1 by linarith) i
    rw [show 1 + (c - 1) = c by ring] at h
    linarith
  have hi1 : (i : ℝ) ≤ N := by exact_mod_cast hi
  have e : c ^ i • I - φx = c ^ i • (I - φx) + (c ^ i - 1) • φx := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hc0 i),
    abs_of_nonpos (by linarith)]
  have hφB : ‖φx‖ ≤ B := hf.2 i hi x
  have t1 : c ^ i * ‖I - φx‖ ≤ ε / 2 :=
    calc c ^ i * ‖I - φx‖ ≤ 1 * (ε / 2) := mul_le_mul hpow1 hI (norm_nonneg _) zero_le_one
      _ = ε / 2 := one_mul _
  have t2 : -(c ^ i - 1) * ‖φx‖ ≤ ε / 2 := by
    have h4 : -(c ^ i - 1) * ‖φx‖ ≤ (i * (a * h)) * B := by
      have : -(c ^ i - 1) ≤ i * (a * h) :=
        calc -(c ^ i - 1) = 1 - c ^ i := by ring
          _ ≤ i * (1 - c) := hpow2
          _ ≤ i * (a * h) := mul_le_mul_of_nonneg_left hc1' (Nat.cast_nonneg _)
      exact mul_le_mul this hφB (norm_nonneg _) (by positivity)
    refine h4.trans ?_
    have h5 : h * (2 * (N + 1) * (a + 1) * (B + 1)) < ε := by
      rwa [lt_div_iff₀ (by positivity)] at h3
    have e2 : (i : ℝ) * a * B ≤ ((N : ℝ) + 1) * (a + 1) * (B + 1) := by
      have e1 : (i : ℝ) ≤ N + 1 := by linarith
      have e2 : a ≤ a + 1 := by linarith
      have e3 : B ≤ B + 1 := by linarith
      exact mul_le_mul (mul_le_mul e1 e2 ha.le (by positivity)) e3 hB (by positivity)
    have e4 : h * (2 * ((N : ℝ) + 1) * (a + 1) * (B + 1)) = 2 * (h * (((N : ℝ) + 1) * (a + 1) * (B + 1))) := by
      ring
    calc (i : ℝ) * (a * h) * B = h * ((i : ℝ) * a * B) := by ring
      _ ≤ h * (((N : ℝ) + 1) * (a + 1) * (B + 1)) := mul_le_mul_of_nonneg_left e2 hh
      _ ≤ ε / 2 := by linarith
  linarith

theorem c1_ou_strong (a ν : ℝ) (ha : 0 < a) (hν : 0 < ν) (N : ℕ) {B : ℝ} {f : Euc d → ℝ}
    (hf : Bd N B f) (hv : VanB N f) :
    (∀ h : ℝ, 0 ≤ h → VanB N (ouSg (ouQ d a) ν h f)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 ≤ h → h < δ → ∀ i ≤ N, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (ouSg (ouQ d a) ν h f) x - iteratedFDeriv ℝ i f x‖ ≤ ε := by
  refine ⟨fun h hh => s104c1_vanB ha hν.le hf hv hh, fun ε hε => ?_⟩
  have hex : ∀ i : ℕ, ∃ δ : ℝ, 0 < δ ∧ (i ≤ N → ∀ h : ℝ, 0 ≤ h → h < δ → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (ouSg (ouQ d a) ν h f) x - iteratedFDeriv ℝ i f x‖ ≤ ε) := by
    intro i
    by_cases hi : i ≤ N
    · obtain ⟨δ, hδ, hh⟩ := s104c1_strong_i ha hν hf hv hi hε
      exact ⟨δ, hδ, fun _ => hh⟩
    · exact ⟨1, one_pos, fun h => absurd h hi⟩
  choose δ hδ0 hδ using hex
  refine ⟨(Finset.range (N + 1)).inf' ⟨0, by simp⟩ δ, ?_, fun h hh hlt i hi x => ?_⟩
  · exact (Finset.lt_inf'_iff _).2 fun i _ => hδ0 i
  · exact hδ i hi h hh (hlt.trans_le (Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))) x

/-- linearity on bounded continuous functions -/
theorem c1_ou_lin (a ν : ℝ) (h : ℝ) (c B B' : ℝ) {f g : Euc d → ℝ} (hf : Bd 0 B f) (hg : Bd 0 B' g) :
    ouSg (ouQ d a) ν h (fun x => c * f x + g x) = fun x => c * ouSg (ouQ d a) ν h f x + ouSg (ouQ d a) ν h g x := by
  funext x
  have hfc : Continuous f := by simpa using hf.1
  have hgc : Continuous g := by simpa using hg.1
  have hi1 : Integrable (fun y : Euc d => f (ouExp (ouQ d a) h x + y)) (ouLaw (ouQ d a) ν h) :=
    Integrable.of_bound (C := B) (hfc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa using hf.2 0 le_rfl _)
  have hi2 : Integrable (fun y : Euc d => g (ouExp (ouQ d a) h x + y)) (ouLaw (ouQ d a) ν h) :=
    Integrable.of_bound (C := B') (hgc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa using hg.2 0 le_rfl _)
  unfold ouSg
  rw [integral_add (hi1.const_mul c) hi2, integral_const_mul]

end HRS.MS.S104e.C
