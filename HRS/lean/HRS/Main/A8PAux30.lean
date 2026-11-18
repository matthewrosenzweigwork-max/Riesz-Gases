import HRS.Main.A8PAux29

/-!
# Packet A8P, part 30: the trivial (energy-free) covariance bound
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

section Triv

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- The trivial covariance cost. -/
def a8pCovCostTriv (S : MainData d) (N : ℕ) (Ca Λ₁ : ℝ) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) : ℝ :=
  S.T * ∑ a, ∑ b, 4 * (S.sigma N ^ 2 * S.invβ N / N) * (d * (Ca * a8pK Λ₁ (ts a) (φ a)) *
    (Ca * a8pK Λ₁ (ts b) (φ b)))

theorem a8p_cov_entry_triv (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a))
    (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) S.T) (ω : (R N).Ω) (a b : Fin q) :
    |a8pSg S R N ts φ r ω a b - a8pSb S N ts φ r a b| ≤
      4 * (S.sigma N ^ 2 * S.invβ N / N) * (d * (Ca * a8pK Λ₁ (ts a) (φ a)) *
        (Ca * a8pK Λ₁ (ts b) (φ b))) := by
  have hT0 : 0 ≤ S.T := S.hT.le
  have hq0 : 0 ≤ S.sigma N ^ 2 * S.invβ N / N := by
    have := S.hinvβ N
    positivity
  have hKa := a8pK_nonneg Λ₁ (ts a) (φ a)
  have hKb := a8pK_nonneg Λ₁ (ts b) (φ b)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have he : a8pSg S R N ts φ r ω a b - a8pSb S N ts φ r a b =
      if 0 ≤ r ∧ r < min (ts a) (ts b) then
        2 * (S.sigma N ^ 2 * S.invβ N / N) *
          (∫ x, inner ℝ (Torus.grad (a8pF S N ts φ a r) x) (Torus.grad (a8pF S N ts φ b r) x)
              ∂(empirical ((R N).X (Real.toNNReal r) ω)) -
            ∫ x, inner ℝ (Torus.grad (a8pF S N ts φ a r) x) (Torus.grad (a8pF S N ts φ b r) x) *
              S.ρ N (Q54c.clampT S.T r) x)
      else 0 :=
    a8p_cov_entry_eq (hN) (S.dyn N) (S.sigma N) ts (a8pF S N ts φ) (R N).X
      (fun r => S.ρ N (Q54c.clampT S.T r)) r ω a b
  rw [he]
  by_cases h : 0 ≤ r ∧ r < min (ts a) (ts b)
  · rw [if_pos h]
    have hra : r ∈ Set.Icc (0 : ℝ) (ts a) := ⟨h.1, (lt_min_iff.1 h.2).1.le⟩
    have hrb : r ∈ Set.Icc (0 : ℝ) (ts b) := ⟨h.1, (lt_min_iff.1 h.2).2.le⟩
    obtain ⟨-, hcla, hba⟩ := a8p_adj_pkg hspec hCa hS hN (hts a) (hφc a) (hφ a)
    obtain ⟨-, hclb, hbb⟩ := a8p_adj_pkg hspec hCa hS hN (hts b) (hφc b) (hφ b)
    obtain ⟨-, -, hcba⟩ := hba r hra
    obtain ⟨-, -, hcbb⟩ := hbb r hrb
    set Bh : ℝ := d * (Ca * a8pK Λ₁ (ts a) (φ a)) * (Ca * a8pK Λ₁ (ts b) (φ b)) with hBh
    have hBh0 : 0 ≤ Bh := by simp only [hBh]; positivity
    have hpt : ∀ x, |inner ℝ (Torus.grad (a8pF S N ts φ a r) x) (Torus.grad (a8pF S N ts φ b r) x)| ≤ Bh := by
      intro x
      rw [a8p_inner_grad]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j, |Torus.partialDeriv j (a8pF S N ts φ a r) x * Torus.partialDeriv j (a8pF S N ts φ b r) x|
          ≤ ∑ _j : Fin d, (Ca * a8pK Λ₁ (ts a) (φ a)) * (Ca * a8pK Λ₁ (ts b) (φ b)) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            have h1 := (HRS.PDE.MFPair.abs_partialDeriv_le (L := 2) (by norm_num) (hcla.c2 r hra) j x).trans hcba
            have h2 := (HRS.PDE.MFPair.abs_partialDeriv_le (L := 2) (by norm_num) (hclb.c2 r hrb) j x).trans hcbb
            exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = Bh := by simp [hBh]; ring
    have hdens := (hS.mean_field.solution N hN).density r hr
    have hemp : |∫ x, inner ℝ (Torus.grad (a8pF S N ts φ a r) x) (Torus.grad (a8pF S N ts φ b r) x)
        ∂(empirical ((R N).X (Real.toNNReal r) ω))| ≤ Bh := by
      rw [gfb2_integral_empirical, abs_mul]
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      rw [abs_of_pos (inv_pos.2 hNr)]
      refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 hNr.le)).trans ?_
      calc (N : ℝ)⁻¹ * ∑ i, |inner ℝ (Torus.grad (a8pF S N ts φ a r) ((R N).X (Real.toNNReal r) ω i))
            (Torus.grad (a8pF S N ts φ b r) ((R N).X (Real.toNNReal r) ω i))|
          ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, Bh :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hpt _) (inv_nonneg.2 hNr.le)
        _ = Bh := by simp; field_simp
    have hrho : |∫ x, inner ℝ (Torus.grad (a8pF S N ts φ a r) x) (Torus.grad (a8pF S N ts φ b r) x) *
        S.ρ N (Q54c.clampT S.T r) x| ≤ Bh := by
      rw [Q54c.clampT_of_mem hr]
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ x, |inner ℝ (Torus.grad (a8pF S N ts φ a r) x) (Torus.grad (a8pF S N ts φ b r) x) * S.ρ N r x|
          ≤ ∫ x, Bh * S.ρ N r x := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) ?_
              (Eventually.of_forall fun x => ?_)
            · exact (MeasureTheory.Integrable.of_integral_ne_zero
                (by rw [hdens.integral_one]; norm_num)).const_mul _
            · show |_ * _| ≤ Bh * S.ρ N r x
              rw [abs_mul, abs_of_nonneg (hdens.nonneg x)]
              exact mul_le_mul_of_nonneg_right (hpt x) (hdens.nonneg x)
        _ = Bh := by
            rw [integral_const_mul, hdens.integral_one, mul_one]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (S.sigma N ^ 2 * S.invβ N / N))]
    have := (abs_sub _ _).trans (add_le_add hemp hrho)
    nlinarith [this]
  · rw [if_neg h, abs_zero]
    positivity

theorem a8p_cov_cost_triv (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) :
    covDiscrepancyMatrix (R N).P S.T (a8pSg S R N ts φ) (a8pSb S N ts φ) ≤
      a8pCovCostTriv S N Ca Λ₁ ts φ := by
  have hT0 : 0 ≤ S.T := S.hT.le
  set Cc' : ℝ := ∑ a, ∑ b, 4 * (S.sigma N ^ 2 * S.invβ N / N) * (d * (Ca * a8pK Λ₁ (ts a) (φ a)) *
    (Ca * a8pK Λ₁ (ts b) (φ b))) with hCc'
  have hg : ∀ ω, (∫ σ in Set.Icc (0 : ℝ) S.T, s1Norm (a8pSg S R N ts φ σ ω - a8pSb S N ts φ σ)) ≤
      S.T * Cc' := by
    intro ω
    have h1 := integral_mono_of_nonneg (μ := volume.restrict (Set.Icc (0 : ℝ) S.T))
      (f := fun σ => s1Norm (a8pSg S R N ts φ σ ω - a8pSb S N ts φ σ)) (g := fun _ => Cc')
      (Eventually.of_forall fun r => traceNormMatrix_nonneg _) (integrableOn_const (by simp))
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => by
        refine (a8p_s1Norm_le_sum _).trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_)
        simpa only [Matrix.sub_apply] using
          a8p_cov_entry_triv hspec hCa hS hN ts hts φ hφc hφ r hr ω a b))
    refine h1.trans (le_of_eq ?_)
    simp [Measure.real, Real.volume_Icc, hT0]
  unfold covDiscrepancyMatrix
  have h2 := integral_mono_of_nonneg (μ := (R N).P)
    (Eventually.of_forall fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _)
    (integrable_const (S.T * Cc')) (Eventually.of_forall hg)
  refine h2.trans (le_of_eq ?_)
  simp [a8pCovCostTriv, hCc']

end Triv

end HRS.Main.A8P
