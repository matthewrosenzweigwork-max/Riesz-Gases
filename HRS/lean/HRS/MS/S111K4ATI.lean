import HRS.MS.S111K4ATG

/-!
# S11.1 / all-tests boundary (S111K4AT), piece I: the covariance envelope
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4AT

open HRS HRS.Whole HRS.MS.FixEq HRS.MS.CovMeas

variable {d : ℕ}

theorem k4at_cov_envelope {r : ℕ} {Pw : ℝ} (hP : (d : ℝ) < 2 * Pw) {C : WholeCoeff d} {m H : ℝ}
    (horb : K4OscOrbitApprox C m H r) {z : ℝ → (Euc d → ℝ) → ℝ} (hz : IsR2L1F r Pw H z)
    {N : ℝ → ℝ≥0∞} (hzN : ∀ s ∈ Set.Icc (0 : ℝ) H, dualNormE r Pw (z s) ≤ N s)
    {φ ψ : Euc d → ℝ} (hφ : IsOscTest m φ) (hψ : IsOscTest m ψ) {Ta Tb : ℝ}
    (hTa : Ta ∈ Set.Icc (0 : ℝ) H) (hTb : Tb ∈ Set.Icc (0 : ℝ) H) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∃ e : ℕ → ℝ≥0∞, Tendsto e atTop (𝓝 0) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) (min Ta Tb),
        ‖z s (k4Gf (propagatorW C s Ta φ) (propagatorW C s Tb ψ))‖ₑ ≤ N s * c) ∧
      ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (0 : ℝ) (min Ta Tb),
        ‖z s (k4Gf (propagatorW C s Ta (k4hs m n φ)) (propagatorW C s Tb (k4hs m n ψ))) -
          z s (k4Gf (propagatorW C s Ta φ) (propagatorW C s Tb ψ))‖ₑ ≤ N s * e n := by
  obtain ⟨bf, hbf0, ε1, hε1, hε1t, hfJ, hfnJ, hfd⟩ := k4at_jets horb hφ hTa
  obtain ⟨bh, hbh0, ε2, hε2, hε2t, hhJ, hhnJ, hhd⟩ := k4at_jets horb hψ hTb
  set Bsm : ℝ := (d : ℝ) * (2 ^ r * (bf * bh)) with hBsm
  set Bn : ℝ := (d : ℝ) * (2 ^ r * ((bf + 1) * (bh + 1))) with hBn
  set Bd : ℕ → ℝ := fun n => (d : ℝ) * (2 ^ r * (ε1 n * (bh + ε2 n))) + (d : ℝ) * (2 ^ r * (bf * ε2 n))
    with hBd
  have hBd0 : ∀ n, 0 ≤ Bd n := fun n => by
    have := hε1 n; have := hε2 n
    simp only [hBd]; positivity
  refine ⟨ENNReal.ofReal (s57pC d r Pw * Bsm), ENNReal.ofReal_ne_top,
    fun n => ENNReal.ofReal (s57pC d r Pw * Bd n), ?_, ?_, ?_⟩
  · have h1 : Tendsto Bd atTop (𝓝 ((d : ℝ) * (2 ^ r * (0 * (bh + 0))) + (d : ℝ) * (2 ^ r * (bf * 0)))) :=
      (((hε1t.mul (hε2t.const_add bh)).const_mul ((2 : ℝ) ^ r)).const_mul (d : ℝ)).add
        ((hε2t.const_mul bf).const_mul ((2 : ℝ) ^ r) |>.const_mul (d : ℝ))
    simp only [zero_mul, mul_zero, add_zero] at h1
    simpa using ENNReal.tendsto_ofReal (h1.const_mul (s57pC d r Pw))
  · intro s hs
    have hsA : s ∈ Set.Icc (0 : ℝ) Ta := ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
    have hsB : s ∈ Set.Icc (0 : ℝ) Tb := ⟨hs.1, hs.2.trans (min_le_right _ _)⟩
    have hsH : s ∈ Set.Icc (0 : ℝ) H := ⟨hs.1, hs.2.trans ((min_le_left _ _).trans hTa.2)⟩
    obtain ⟨hf1, hf2⟩ := hfJ s hsA
    obtain ⟨hh1, hh2⟩ := hhJ s hsB
    have hcd := k4Gf_contDiff hf1 hh1
    have hb := k4Gf_bound hf1 hh1 hf2 hh2
    have hz1 := k4at_z_bound_iter hP hz hsH hcd hb
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact hz1.trans (mul_le_mul' (hzN s hsH) le_rfl)
  · filter_upwards [hfd, hhd, hε1t.eventually (ge_mem_nhds (show (0 : ℝ) < 1 from one_pos)),
      hε2t.eventually (ge_mem_nhds (show (0 : ℝ) < 1 from one_pos))] with n hn1 hn2 hε1n hε2n s hs
    have hsA : s ∈ Set.Icc (0 : ℝ) Ta := ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
    have hsB : s ∈ Set.Icc (0 : ℝ) Tb := ⟨hs.1, hs.2.trans (min_le_right _ _)⟩
    have hsH : s ∈ Set.Icc (0 : ℝ) H := ⟨hs.1, hs.2.trans ((min_le_left _ _).trans hTa.2)⟩
    obtain ⟨hf1, hf2⟩ := hfJ s hsA
    obtain ⟨hh1, hh2⟩ := hhJ s hsB
    have hfn1 := hfnJ n s hsA
    have hhn1 := hhnJ n s hsB
    have hdf := hn1 s hsA
    have hdh := hn2 s hsB
    -- jets of the perturbed functions
    have hfn2 : ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j (propagatorW C s Ta (k4hs m n φ)) x‖ ≤ bf + ε1 n := by
      intro j hj x
      exact (k4_iter_le_add hfn1 hf1 hj x).trans (add_le_add (hf2 j hj x) (hdf j hj x))
    have hhn2 : ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j (propagatorW C s Tb (k4hs m n ψ)) x‖ ≤ bh + ε2 n := by
      intro j hj x
      exact (k4_iter_le_add hhn1 hh1 hj x).trans (add_le_add (hh2 j hj x) (hdh j hj x))
    -- Gn and G are bounded by `Bn`
    have hGn := k4Gf_bound hfn1 hhn1 (bf := bf + 1) (bh := bh + 1)
      (fun j hj x => (hfn2 j hj x).trans (by linarith))
      (fun j hj x => (hhn2 j hj x).trans (by linarith))
    have hG := k4Gf_bound hf1 hh1 (bf := bf + 1) (bh := bh + 1)
      (fun j hj x => (hf2 j hj x).trans (by linarith))
      (fun j hj x => (hh2 j hj x).trans (by linarith))
    -- Leibniz splitting of the difference
    have hdiffeq := k4Gf_sub_eq
      (hfn1.differentiable (by exact_mod_cast Nat.succ_ne_zero r))
      (hf1.differentiable (by exact_mod_cast Nat.succ_ne_zero r))
      (hhn1.differentiable (by exact_mod_cast Nat.succ_ne_zero r))
      (hh1.differentiable (by exact_mod_cast Nat.succ_ne_zero r))
    have hc1 : ContDiff ℝ (r : WithTop ℕ∞)
        (k4Gf (fun y => propagatorW C s Ta (k4hs m n φ) y - propagatorW C s Ta φ y)
          (propagatorW C s Tb (k4hs m n ψ))) := k4Gf_contDiff (hfn1.sub hf1) hhn1
    have hc2 : ContDiff ℝ (r : WithTop ℕ∞)
        (k4Gf (propagatorW C s Ta φ)
          (fun y => propagatorW C s Tb (k4hs m n ψ) y - propagatorW C s Tb ψ y)) :=
      k4Gf_contDiff hf1 (hhn1.sub hh1)
    have hb1 := k4Gf_bound (hfn1.sub hf1) hhn1 (bf := ε1 n) (bh := bh + ε2 n)
      (fun j hj x => hdf j hj x) hhn2
    have hb2 := k4Gf_bound hf1 (hhn1.sub hh1) (bf := bf) (bh := ε2 n) hf2 (fun j hj x => hdh j hj x)
    have hdiffb : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (fun y =>
        k4Gf (propagatorW C s Ta (k4hs m n φ)) (propagatorW C s Tb (k4hs m n ψ)) y -
          k4Gf (propagatorW C s Ta φ) (propagatorW C s Tb ψ) y) x‖ ≤ Bd n := by
      intro j hj x
      rw [hdiffeq]
      have := iteratedFDeriv_add_apply (𝕜 := ℝ) (x := x) (i := j)
        (hc1.contDiffAt.of_le (by exact_mod_cast hj)) (hc2.contDiffAt.of_le (by exact_mod_cast hj))
      refine (le_of_eq (congrArg norm this)).trans ?_
      refine (norm_add_le _ _).trans ?_
      exact add_le_add (hb1 j hj x) (hb2 j hj x)
    have hz1 := k4at_z_diff_bound_iter hP hz hsH (k4Gf_contDiff hfn1 hhn1)
      (k4Gf_contDiff hf1 hh1) hGn hG hdiffb
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact hz1.trans (mul_le_mul' (hzN s hsH) le_rfl)

end HRS.MS.S111K4AT
