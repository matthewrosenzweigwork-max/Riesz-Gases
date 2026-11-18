import HRS.MS.S111K4ATA
import HRS.MS.S111K4ATB
import HRS.MS.S111K4ATC
import HRS.MS.GoCommAux1

/-!
# S11.1 / all-tests boundary (S111K4AT), piece D: the orbit approximation structure and the pointwise envelope

`K4OscOrbitApprox` is Pro's `r26t6_OscOrbitApprox` (copied; the Hermite section is `k4hs`).  `k4at_envelope`: for an
oscillator test `φ` and `L¹F` functional `z`, `z s (U^{s,t}(Hermite section of φ)) → z s (U^{s,t} φ)` with an explicit
envelope `N s · e_n`, `e_n → 0`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4AT

open HRS HRS.Whole HRS.MS.FixEq

variable {d : ℕ}

/-- Pro `r26t6_OscOrbitApprox` (statement copied). -/
structure K4OscOrbitApprox {d : ℕ} (C : WholeCoeff d) (m H : ℝ) (r : ℕ) : Prop where
  classical : ∀ phi, IsOscTest m phi → ∀ t ∈ Set.Icc (0 : ℝ) H, ∃ f, IsClassicalAdjointW C t phi f
  smooth : ∀ phi, IsOscTest m phi → ∀ v ∈ Set.Icc (0 : ℝ) H, ∀ t ∈ Set.Icc v H,
    ContDiff ℝ (r + 1) (propagatorW C v t phi)
  bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ phi, IsOscTest m phi →
    ∀ v ∈ Set.Icc (0 : ℝ) H, ∀ t ∈ Set.Icc v H,
      weightedSupE (r + 1) 0 (propagatorW C v t phi) ≤ ENNReal.ofReal (K * oscNorm m phi)
  limit : ∀ phi, IsOscTest m phi →
    Tendsto (fun n : ℕ => ⨆ v ∈ Set.Icc (0 : ℝ) H, ⨆ t ∈ Set.Icc v H,
      weightedSupE (r + 1) 0
        (propagatorW C v t (k4hs m n phi) - propagatorW C v t phi))
      atTop (𝓝 0)

theorem k4at_pd_of_wse {k : ℕ} {f : Euc d → ℝ} {Λ : ℝ} (h : weightedSupE k 0 f ≤ ENNReal.ofReal Λ) :
    ∀ j ≤ k, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i f x| ≤ max Λ 0 := by
  intro j hj i x
  have := HRS.MS.Go.s55_dse_bound (w := fun _ => (0 : ℝ)) (f := f) h hj i x
  simpa using this

theorem k4at_envelope {r : ℕ} {Pw : ℝ} (hP : (d : ℝ) < 2 * Pw) {C : WholeCoeff d} {m H : ℝ}
    (horb : K4OscOrbitApprox C m H r) {z : ℝ → (Euc d → ℝ) → ℝ} (hz : IsR2L1F r Pw H z)
    {N : ℝ → ℝ≥0∞} (hzN : ∀ s ∈ Set.Icc (0 : ℝ) H, dualNormE r Pw (z s) ≤ N s)
    {φ : Euc d → ℝ} (hφ : IsOscTest m φ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) H) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∃ e : ℕ → ℝ≥0∞, Tendsto e atTop (𝓝 0) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) t, ‖z s (propagatorW C s t φ)‖ₑ ≤ N s * c) ∧
      ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖z s (propagatorW C s t (k4hs m n φ)) - z s (propagatorW C s t φ)‖ₑ ≤ N s * e n := by
  obtain ⟨K, hK0, hKb⟩ := horb.bound
  have hst : ∀ s ∈ Set.Icc (0 : ℝ) t, s ∈ Set.Icc (0 : ℝ) H ∧ t ∈ Set.Icc s H := fun s hs =>
    ⟨⟨hs.1, hs.2.trans ht.2⟩, ⟨hs.2, ht.2⟩⟩
  set cc : ℝ := s57pC d r Pw * (((d : ℝ) + 1) ^ r * max (K * oscNorm m φ) 0) with hcc
  refine ⟨ENNReal.ofReal cc, ENNReal.ofReal_ne_top, ?_⟩
  set δ : ℕ → ℝ≥0∞ := fun n => ⨆ v ∈ Set.Icc (0 : ℝ) H, ⨆ t ∈ Set.Icc v H,
    weightedSupE (r + 1) 0 (propagatorW C v t (k4hs m n φ) - propagatorW C v t φ) with hδ
  have hδt : Tendsto δ atTop (𝓝 0) := horb.limit φ hφ
  set e : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (s57pC d r Pw * (((d : ℝ) + 1) ^ r * (δ n).toReal)) with he
  have het : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (δ n).toReal) atTop (𝓝 0) := by
      have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hδt
      rwa [ENNReal.toReal_zero] at h0
    have h2 : Tendsto (fun n => s57pC d r Pw * (((d : ℝ) + 1) ^ r * (δ n).toReal)) atTop (𝓝 0) := by
      simpa using (h1.const_mul (((d : ℝ) + 1) ^ r)).const_mul (s57pC d r Pw)
    simpa using ENNReal.tendsto_ofReal h2
  refine ⟨e, het, ?_, ?_⟩
  · intro s hs
    obtain ⟨hsH, htH⟩ := hst s hs
    have hsm : ContDiff ℝ r (propagatorW C s t φ) := (horb.smooth φ hφ s hsH t htH).of_le (by exact_mod_cast Nat.le_succ r)
    have hb := k4at_pd_of_wse (hKb φ hφ s hsH t htH)
    have hb' : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i (propagatorW C s t φ) x| ≤ max (K * oscNorm m φ) 0 :=
      fun j hj i x => hb j (hj.trans (Nat.le_succ r)) i x
    have hz1 := k4at_z_bound hP hz hsH hsm (le_max_right _ _) hb'
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact hz1.trans (mul_le_mul' (hzN s hsH) le_rfl)
  · have hfin : ∀ᶠ n in atTop, δ n < ⊤ := hδt.eventually (gt_mem_nhds (by simp))
    filter_upwards [hfin] with n hn s hs
    obtain ⟨hsH, htH⟩ := hst s hs
    have hφn : IsOscTest m (k4hs m n φ) := k4hs_osc m n φ
    have hsm : ContDiff ℝ r (propagatorW C s t φ) := (horb.smooth φ hφ s hsH t htH).of_le (by exact_mod_cast Nat.le_succ r)
    have hsmn : ContDiff ℝ r (propagatorW C s t (k4hs m n φ)) :=
      (horb.smooth _ hφn s hsH t htH).of_le (by exact_mod_cast Nat.le_succ r)
    have hb := k4at_pd_of_wse (hKb φ hφ s hsH t htH)
    have hbn := k4at_pd_of_wse (hKb _ hφn s hsH t htH)
    have hdle : weightedSupE (r + 1) 0 (propagatorW C s t (k4hs m n φ) - propagatorW C s t φ) ≤ δ n :=
      le_iSup₂_of_le s hsH (le_iSup₂_of_le t htH le_rfl)
    have hdle' : weightedSupE (r + 1) 0 (propagatorW C s t (k4hs m n φ) - propagatorW C s t φ) ≤
        ENNReal.ofReal (δ n).toReal := by rwa [ENNReal.ofReal_toReal hn.ne]
    have hd := k4at_pd_of_wse hdle'
    have hz1 := k4at_z_diff_bound hP hz hsH hsmn hsm
      (b := max (max (K * oscNorm m (k4hs m n φ)) 0) (max (K * oscNorm m φ) 0))
      (δ := max (δ n).toReal 0) (le_max_of_le_right (le_max_right _ _)) (le_max_right _ _)
      (fun j hj i x => (hbn j (hj.trans (Nat.le_succ r)) i x).trans (le_max_left _ _))
      (fun j hj i x => (hb j (hj.trans (Nat.le_succ r)) i x).trans (le_max_right _ _))
      (fun j hj i x => hd j (hj.trans (Nat.le_succ r)) i x)
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    refine hz1.trans (mul_le_mul' (hzN s hsH) ?_)
    have hmx : max (δ n).toReal 0 = (δ n).toReal := max_eq_left ENNReal.toReal_nonneg
    rw [hmx]

end HRS.MS.S111K4AT
