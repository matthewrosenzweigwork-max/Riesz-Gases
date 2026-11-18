import HRS.MS.Fp81S21WeightedGenNL3
import HRS.MS.ProClosureS111WeightedAllTests
import HRS.MS.ProClosureS111WeightedDensity

/-! Pointwise growth of the input jet for the nonlocal source. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.Ul HRS.MS.ProClosureS111

local instance fp81s21_b3_nl4_measurableSpaceEuc (d : ℕ) : MeasurableSpace (Euc d) :=
  measureSpaceOfInnerProductSpace.toMeasurableSpace

/-- The first jet of a directional derivative of an arbitrary finite weighted
 test grows at most at the input weight; no global boundedness is assumed. -/
theorem fp81s21_b3_all_test_directional_growth (p : Parameters) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc p.d → ℝ,
      IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f →
      ∀ (v : Euc p.d) (i : ℕ), i ≤ 1 → ∀ x,
        ‖iteratedFDeriv ℝ i (fun y => fderiv ℝ f y v) x‖ ≤
          ‖v‖ * (C * jbracket x ^ (fp81s21_b3_P p) *
            (weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f).toReal) := by
  have hr : (2 : ℝ) + (p.d : ℝ) / 2 < (fp81s21_b3_q p + 2 : ℕ) := by
    unfold fp81s21_b3_q
    push_cast
    have := Nat.cast_nonneg (α := ℝ) p.d
    linarith
  obtain ⟨C, hC, heval⟩ := weighted_jet_evaluation_all p.d
    (fp81s21_b3_q p + 2) (fp81s21_b3_P p) hr
  refine ⟨C, hC, ?_⟩
  intro f hf v i hi x
  have hf2 : ContDiff ℝ (2 : ℕ) f :=
    hf.1.of_le (by exact_mod_cast (show 2 ≤ fp81s21_b3_q p + 2 by omega))
  have hcd : ContDiff ℝ (1 : ℕ) (fderiv ℝ f) :=
    hf2.fderiv_right (by norm_num)
  have hnorm := norm_iteratedFDeriv_clm_apply_const (N := (1 : WithTop ℕ∞))
    (c := v) (x := x) (n := i) hcd.contDiffAt (by exact_mod_cast hi)
  rw [norm_iteratedFDeriv_fderiv] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_left (heval f hf (i + 1) (by omega) x) (norm_nonneg _))

/-- A decaying factor absorbs polynomial growth of a first jet. -/
theorem fp81s21_b3_u2dec_mul_growth {d : ℕ} {L P A D : ℝ}
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hD : 0 ≤ D)
    {ρ φ : Euc d → ℝ} (hρ : U2Dec 1 (L + P) A ρ)
    (hφ : ContDiff ℝ 1 φ)
    (hφb : ∀ i ≤ 1, ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ D * jbracket x ^ P) :
    U2Dec 1 L (A * D * 2) (fun x => ρ x * φ x) := by
  have hw (x : Euc d) : u2Wt (L + P) x * jbracket x ^ P ≤ u2Wt L x := by
    have hx : 0 < 1 + ‖x‖ := by positivity
    have hj : jbracket x ^ P ≤ (1 + ‖x‖) ^ P :=
      Real.rpow_le_rpow (HRS.MS.Who.who_jb_pos x).le (u2_jb_le x) hP
    calc
      _ ≤ u2Wt (L + P) x * (1 + ‖x‖) ^ P :=
        mul_le_mul_of_nonneg_left hj (u2Wt_pos _ x).le
      _ = u2Wt L x := by
        unfold u2Wt
        rw [← Real.rpow_add hx]
        congr 1
        ring
  refine ⟨hρ.1.mul hφ, fun m hm x => ?_⟩
  refine (norm_iteratedFDeriv_mul_le hρ.1 hφ x (by exact_mod_cast hm)).trans ?_
  have hw0 : 0 ≤ u2Wt (L + P) x := (u2Wt_pos _ x).le
  have hw1 : 0 ≤ u2Wt L x := (u2Wt_pos _ x).le
  have ht : ∀ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i ρ x‖ *
          ‖iteratedFDeriv ℝ (m - i) φ x‖ ≤
        (m.choose i : ℝ) * (A * D * u2Wt L x) := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hh := mul_le_mul (hρ.2 i (hi'.trans hm) x)
      (hφb (m - i) (by omega) x) (norm_nonneg _) (mul_nonneg hA hw0)
    calc
      _ ≤ (m.choose i : ℝ) * ((A * u2Wt (L + P) x) * (D * jbracket x ^ P)) :=
        by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)
      _ = (m.choose i : ℝ) * (A * D * (u2Wt (L + P) x * jbracket x ^ P)) := by ring
      _ ≤ (m.choose i : ℝ) * (A * D * u2Wt L x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hw x) (mul_nonneg hA hD))
          (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (A * D * u2Wt L x) :=
      Finset.sum_le_sum ht
    _ = (2 : ℝ) ^ m * (A * D * u2Wt L x) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      rfl
    _ ≤ 2 * (A * D * u2Wt L x) :=
      mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm)
        (mul_nonneg (mul_nonneg hA hD) hw1)
    _ = A * D * 2 * u2Wt L x := by ring

/-- The cancellation-convolution integrand is integrable for every finite
weighted input test, without any bounded-jet assumption. -/
theorem fp81s21_b3_all_test_integrable (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) (u : ℝ) (hu : 0 ≤ u)
    (f : Euc p.d → ℝ)
    (hf : IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f) :
    ∀ j : Fin p.d, ∀ x : Euc p.d,
      Integrable (fun y =>
        if ‖x - y‖ ≤ (1 / 4 : ℝ) then
          (fp81s21_b3_source R u f j y - fp81s21_b3_source R u f j x) •
            rieszKernelGrad p.d p.s (x - y)
        else fp81s21_b3_source R u f j y • rieszKernelGrad p.d p.s (x - y)) := by
  obtain ⟨C, hC, hg⟩ := fp81s21_b3_all_test_directional_growth p
  obtain ⟨A, hA, hρ⟩ := fp81s21_g4_density_decay p R (2 * p.d + 3)
  have hP : 0 ≤ fp81s21_b3_P p := by unfold fp81s21_b3_P; positivity
  have hL : (p.d : ℝ) < (p.d : ℝ) + 1 := by linarith
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hd : 1 ≤ p.d := le_trans (by decide) p.hd
  intro j x
  let v := ul1w (r26t3_coeff R).M j
  let D := ‖v‖ * C * (weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f).toReal
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hf2 : ContDiff ℝ (2 : ℕ) f :=
    hf.1.of_le (by exact_mod_cast (show 2 ≤ fp81s21_b3_q p + 2 by omega))
  have hφ : ContDiff ℝ 1 (fun y => fderiv ℝ f y v) :=
    (hf2.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hφb : ∀ i ≤ 1, ∀ y, ‖iteratedFDeriv ℝ i (fun z => fderiv ℝ f z v) y‖ ≤
      D * jbracket y ^ (fp81s21_b3_P p) := by
    intro i hi y
    have hh := hg f hf v i hi y
    convert hh using 1 <;> dsimp [D] <;> ring
  have hρ' : U2Dec 1 ((p.d : ℝ) + 1 + fp81s21_b3_P p) A (R.ρ u) := by
    convert hρ u hu using 1
    unfold fp81s21_b3_P
    push_cast
    ring
  have hdec := fp81s21_b3_u2dec_mul_growth hP hA hD hρ' hφ hφb
  have heq : fp81s21_b3_source R u f j = fun y => R.ρ u y * fderiv ℝ f y v := by
    funext y
    simp only [fp81s21_b3_source, ul1_matVec, v]
  change Integrable (ultInt p.s (fp81s21_b3_source R u f j) x)
  rw [heq]
  exact (ult_conv_comp hd p.hs0 hsd hL (by positivity : 0 ≤ A * D * 2) hdec x).1

/-- A single compact cutoff family has local jet agreement and converges in
 the exact weighted L² jet norm. -/
theorem fp81s21_b3_all_test_cutoff_convergence (p : Parameters) (f : Euc p.d → ℝ)
    (hf : IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f) :
    ∃ h : ℕ → Euc p.d → ℝ,
      (∀ n, ContDiff ℝ (fp81s21_b3_q p + 2) (h n) ∧ HasCompactSupport (h n)) ∧
      (∀ x, ∀ᶠ n in atTop, ∀ m : ℕ,
        iteratedFDeriv ℝ m (h n) x = iteratedFDeriv ℝ m f x) ∧
      Tendsto (fun n => eLpNorm
        (weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n) -
          weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f) 2 volume)
        atTop (𝓝 0) := by
  obtain ⟨K, hK, h, hreg, hb, hl⟩ := fp81s21_b3_all_test_cutoffs p f hf
  refine ⟨h, hreg, hl, ?_⟩
  have hmem : MemLp (weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f) 2 volume :=
    (weightedJets_memLp_iff hf.1).2 hf.2
  have ht : ∀ x, Tendsto (fun n => weightedJets (fp81s21_b3_q p + 2)
      (fp81s21_b3_P p) (h n) x) atTop
      (𝓝 (weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f x)) := by
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [hl x] with n hn
    ext a
    change jbracket x ^ (-fp81s21_b3_P p) * partialDeriv a.2 f x =
      jbracket x ^ (-fp81s21_b3_P p) * partialDeriv a.2 (h n) x
    congr 1
    unfold partialDeriv
    rw [hn a.1]
  exact L2_norm_tendsto_of_dominated_pointwise volume
    (fun n => weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n))
    (weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f)
    (fun n => (weightedJets_continuous (hreg n).1).stronglyMeasurable)
    (weightedJets_continuous hf.1).stronglyMeasurable hmem
    (show 0 ≤ K + 1 by linarith)
    (fun n x => (norm_sub_le _ _).trans (by
      have hh := hb n x
      nlinarith [norm_nonneg (weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f x)])) ht

/-- Locally exact cutoffs eventually give the same cancellation integrand
at any prescribed pair of points. -/
theorem fp81s21_b3_cutoff_integrand_eventually (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) (u : ℝ) (f : Euc p.d → ℝ) (h : ℕ → Euc p.d → ℝ)
    (hl : ∀ x, ∀ᶠ n in atTop, ∀ m : ℕ,
      iteratedFDeriv ℝ m (h n) x = iteratedFDeriv ℝ m f x)
    (j : Fin p.d) (x y : Euc p.d) :
    ∀ᶠ n in atTop, ultInt p.s (fp81s21_b3_source R u (h n) j) x y =
      ultInt p.s (fp81s21_b3_source R u f j) x y := by
  filter_upwards [hl x, hl y] with n hx hy
  have hs : ∀ (z : Euc p.d),
      iteratedFDeriv ℝ 1 (h n) z = iteratedFDeriv ℝ 1 f z →
      fp81s21_b3_source R u (h n) j z = fp81s21_b3_source R u f j z := by
    intro z hz
    have hh := congrArg (fun T => T (fun _ => ul1w (r26t3_coeff R).M j)) hz
    simp only [iteratedFDeriv_one_apply] at hh
    simp only [fp81s21_b3_source, ul1_matVec, hh]
  simp only [ultInt, hs x (hx 1), hs y (hy 1)]

/-- Every source has the decay and first derivative needed for the
cancellation convolution, for arbitrary finite weighted inputs. -/
theorem fp81s21_b3_all_test_source_decay (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) (u : ℝ) (hu : 0 ≤ u)
    (f : Euc p.d → ℝ)
    (hf : IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f) :
    ∀ j : Fin p.d, ∃ A : ℝ, 0 ≤ A ∧
      U2Dec 1 ((p.d : ℝ) + 1) A (fp81s21_b3_source R u f j) := by
  obtain ⟨C, hC, hg⟩ := fp81s21_b3_all_test_directional_growth p
  obtain ⟨A, hA, hρ⟩ := fp81s21_g4_density_decay p R (2 * p.d + 3)
  have hP : 0 ≤ fp81s21_b3_P p := by unfold fp81s21_b3_P; positivity
  intro j
  let v := ul1w (r26t3_coeff R).M j
  let D := ‖v‖ * C * (weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f).toReal
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hf2 : ContDiff ℝ (2 : ℕ) f :=
    hf.1.of_le (by exact_mod_cast (show 2 ≤ fp81s21_b3_q p + 2 by omega))
  have hφ : ContDiff ℝ 1 (fun y => fderiv ℝ f y v) :=
    (hf2.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hφb : ∀ i ≤ 1, ∀ y, ‖iteratedFDeriv ℝ i (fun z => fderiv ℝ f z v) y‖ ≤
      D * jbracket y ^ (fp81s21_b3_P p) := by
    intro i hi y
    have hh := hg f hf v i hi y
    convert hh using 1 <;> dsimp [D] <;> ring
  have hρ' : U2Dec 1 ((p.d : ℝ) + 1 + fp81s21_b3_P p) A (R.ρ u) := by
    convert hρ u hu using 1
    unfold fp81s21_b3_P
    push_cast
    ring
  have hdec := fp81s21_b3_u2dec_mul_growth hP hA hD hρ' hφ hφb
  have heq : fp81s21_b3_source R u f j = fun y => R.ρ u y * fderiv ℝ f y v := by
    funext y
    simp only [fp81s21_b3_source, ul1_matVec, v]
  rw [heq]
  exact ⟨A * D * 2, by positivity, hdec⟩

/-- The nonlocal output of every finite weighted test is continuous. -/
theorem fp81s21_b3_all_test_nonlocal_continuous (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) (u : ℝ) (hu : 0 ≤ u)
    (f : Euc p.d → ℝ)
    (hf : IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f) :
    Continuous (fp81s21_g4N p R u f) := by
  have hd : 1 ≤ p.d := le_trans (by decide) p.hd
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hL : (p.d : ℝ) < (p.d : ℝ) + 1 := by linarith
  choose A hA hdec using fp81s21_b3_all_test_source_decay p R u hu f hf
  let F : Fin p.d → Euc p.d → ℝ := fun j =>
    ultK (u2_kap p.d p.s j) (fp81s21_b3_source R u f j)
  have hF : ∀ j, Continuous (F j) := fun j =>
    (ult_K_iter (k := 0) hd (ult_ker_kap p.hs0 hsd j) hL (hA j) (hdec j)).2.continuous
  have hN : fp81s21_g4N p R u f = fun x => ∑ j, F j x := by
    funext x
    unfold fp81s21_g4N
    exact Finset.sum_congr rfl fun j _ =>
      (ult_conv_comp hd p.hs0 hsd hL (hA j) (hdec j) x).2 j
  rw [hN]
  exact continuous_finset_sum _ fun j _ => hF j

/-- Fatou's lemma for the exact weighted norm, once the output jets have
been identified pointwise. -/
theorem fp81s21_b3_weighted_energy_fatou {d r : ℕ} {P : ℝ}
    (g : ℕ → Euc d → ℝ) (f : Euc d → ℝ) (K : ℝ≥0∞)
    (hg : ∀ n, ContDiff ℝ r (g n)) (hf : ContDiff ℝ r f)
    (ht : ∀ x, Tendsto (fun n => weightedJets r P (g n) x) atTop
      (𝓝 (weightedJets r P f x)))
    (hb : ∀ n, weightedSobolevE r P (g n) ≤ K) :
    weightedSobolevE r P f ≤ K := by
  rw [← weightedJets_eLpNorm hf]
  apply MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (f := fun n => weightedJets r P (g n))
  · exact Filter.Eventually.of_forall fun n => by
      rw [weightedJets_eLpNorm (hg n)]
      exact hb n
  · exact fun n => (weightedJets_continuous (hg n)).aestronglyMeasurable
  · exact (weightedJets_continuous hf).aestronglyMeasurable
  · exact Filter.Eventually.of_forall ht

/-- Fatou's lemma with convergent, rather than constant, energy bounds. -/
theorem fp81s21_b3_weighted_energy_fatou_varying {d r : ℕ} {P : ℝ}
    (g : ℕ → Euc d → ℝ) (f : Euc d → ℝ) (K : ℕ → ℝ≥0∞) (K₀ : ℝ≥0∞)
    (hg : ∀ n, ContDiff ℝ r (g n)) (hf : ContDiff ℝ r f)
    (ht : ∀ x, Tendsto (fun n => weightedJets r P (g n) x) atTop
      (𝓝 (weightedJets r P f x)))
    (hb : ∀ n, weightedSobolevE r P (g n) ≤ K n)
    (hK : Tendsto K atTop (𝓝 K₀)) : weightedSobolevE r P f ≤ K₀ := by
  have hfat := MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm
    (μ := (volume : Measure (Euc d))) (p := 2)
    (f := fun n => weightedJets r P (g n))
    (fun n => (weightedJets_continuous (hg n)).aestronglyMeasurable)
    (weightedJets r P f) (weightedJets_continuous hf).aestronglyMeasurable
    (Filter.Eventually.of_forall ht)
  calc
    weightedSobolevE r P f = eLpNorm (weightedJets r P f) 2 volume :=
      (weightedJets_eLpNorm hf).symm
    _ ≤ Filter.liminf (fun n => eLpNorm (weightedJets r P (g n)) 2 volume) atTop := hfat
    _ ≤ Filter.liminf K atTop := Filter.liminf_le_liminf
      (Filter.Eventually.of_forall fun n => by rw [weightedJets_eLpNorm (hg n)]; exact hb n)
    _ = K₀ := hK.liminf_eq

/-- Convergence of weighted jet vectors in L² implies convergence of the
exact weighted energies, for finite weighted tests. -/
theorem fp81s21_b3_weighted_energy_tendsto {d r : ℕ} {P : ℝ}
    (g : ℕ → Euc d → ℝ) (f : Euc d → ℝ)
    (hg : ∀ n, IsR2WeightedTest r P (g n)) (hf : IsR2WeightedTest r P f)
    (ht : Tendsto (fun n => eLpNorm (weightedJets r P (g n) - weightedJets r P f) 2 volume)
      atTop (𝓝 0)) :
    Tendsto (fun n => weightedSobolevE r P (g n)) atTop (𝓝 (weightedSobolevE r P f)) := by
  have hmem : ∀ n, MemLp (weightedJets r P (g n)) 2 volume :=
    fun n => (weightedJets_memLp_iff (hg n).1).2 (hg n).2
  have hfmem : MemLp (weightedJets r P f) 2 volume :=
    (weightedJets_memLp_iff hf.1).2 hf.2
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => weightedJets r P (g n)) hmem (weightedJets r P f) hfmem).2 ht
  have hnorm := hLp.norm
  have hLpE : ∀ n, eLpNorm (weightedJets r P (g n)) 2 volume = weightedSobolevE r P (g n) :=
    fun n => weightedJets_eLpNorm (hg n).1
  have hreal : Tendsto (fun n => (weightedSobolevE r P (g n)).toReal) atTop
      (𝓝 (weightedSobolevE r P f).toReal) := by
    simpa only [Lp.norm_toLp, hLpE, weightedJets_eLpNorm hf.1] using hnorm
  have h := ENNReal.tendsto_ofReal hreal
  simpa only [ENNReal.ofReal_toReal (hf.2.ne),
    ENNReal.ofReal_toReal ((hg _).2.ne)] using h

/-- A compact C^(q+2) function belongs to the actual input test space. -/
theorem fp81s21_b3_compact_input_test (p : Parameters) (f : Euc p.d → ℝ)
    (hf : ContDiff ℝ (fp81s21_b3_q p + 2) f) (hfc : HasCompactSupport f) :
    IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f := by
  have hd : 1 ≤ p.d := le_trans (by decide) p.hd
  have hPd : (p.d : ℝ) / 2 < fp81s21_b3_P p := by
    unfold fp81s21_b3_P
    have := Nat.cast_nonneg (α := ℝ) p.d
    linarith
  obtain ⟨_, D, hD⟩ := fp81s21_b3_compact_cb hf hfc
  have hfinN : HRS.MS.Who.Nsq (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f < ⊤ :=
    HRS.MS.Who.who_Nsq_lt_top hPd (fun j hj => ⟨D, hD j hj⟩)
  have hfinE : HRS.MS.Who.Esq (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f < ⊤ :=
    lt_of_le_of_lt (HRS.MS.Who.who_Esq_le hd)
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.natCast_lt_top p.d)) hfinN)
  refine ⟨hf, ?_⟩
  rw [HRS.MS.Who.who_E_eq]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfinE.ne

/-- Compact input cutoffs preserve local jets and converge in input energy. -/
theorem fp81s21_b3_compact_input_approximation (p : Parameters) (f : Euc p.d → ℝ)
    (hf : IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f) :
    ∃ h : ℕ → Euc p.d → ℝ,
      (∀ n, IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n) ∧
        HasCompactSupport (h n)) ∧
      (∀ x, ∀ᶠ n in atTop, ∀ m : ℕ,
        iteratedFDeriv ℝ m (h n) x = iteratedFDeriv ℝ m f x) ∧
      Tendsto (fun n => weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n))
        atTop (𝓝 (weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f)) := by
  obtain ⟨h, hreg, hl, ht⟩ := fp81s21_b3_all_test_cutoff_convergence p f hf
  have htest : ∀ n, IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n) :=
    fun n => fp81s21_b3_compact_input_test p (h n) (hreg n).1 (hreg n).2
  exact ⟨h, fun n => ⟨htest n, (hreg n).2⟩, hl,
    fp81s21_b3_weighted_energy_tendsto h f htest hf ht⟩

#print axioms HRS.Fp81.S21.fp81s21_b3_compact_input_approximation
#print axioms HRS.Fp81.S21.fp81s21_b3_compact_input_test
#print axioms HRS.Fp81.S21.fp81s21_b3_weighted_energy_tendsto
#print axioms HRS.Fp81.S21.fp81s21_b3_weighted_energy_fatou_varying
#print axioms HRS.Fp81.S21.fp81s21_b3_weighted_energy_fatou
#print axioms HRS.Fp81.S21.fp81s21_b3_all_test_nonlocal_continuous
#print axioms HRS.Fp81.S21.fp81s21_b3_all_test_source_decay
#print axioms HRS.Fp81.S21.fp81s21_b3_cutoff_integrand_eventually
#print axioms HRS.Fp81.S21.fp81s21_b3_all_test_cutoff_convergence
#print axioms HRS.Fp81.S21.fp81s21_b3_all_test_integrable
#print axioms HRS.Fp81.S21.fp81s21_b3_u2dec_mul_growth
#print axioms HRS.Fp81.S21.fp81s21_b3_all_test_directional_growth
end HRS.Fp81.S21
