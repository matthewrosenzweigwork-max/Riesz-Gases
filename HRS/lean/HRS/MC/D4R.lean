import HRS.MC.D47
import HRS.Energy.Commutator.StressAux
import HRS.Energy.Commutator.EnergyAux

/-!
# Packet D4R: the italic sentence of Lemma D.4(iii) (`HRS.fdl_compare_reverse_false`)

`fdl_compare_reverse_false_proof` (statement copied from `HRS/Appendix/FDL.lean`).  Route: the configuration
`x_j = (ε j) e_1` (`j < N`, `ε → 0`); `F_{N,λ}` stays bounded by `2 sup |g_λ|`, while by `fdl_compare_proof`
`F_N ≥ F_{N,λ} + ½ N⁻² w_λ(x_0 - x_1) - O(Λλ^{d-s})` and `w_λ = g - g_λ → ∞` (Lemma D.3 (i), (iv)).
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MC.D4R

open HRS HRS.MC.D47 HRS.MC.D3TAsm

variable {d : ℕ}

/-- A bounded kernel has a bounded modulated energy (`μ` a probability measure). -/
lemma d4r_energy_bound {g : Torus d → ℝ} {M : ℝ} (hg : ∀ x, |g x| ≤ M) {N : ℕ} (hN : 1 ≤ N)
    (X : Config d N) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    |modulatedEnergyKernel g X μ| ≤ 2 * M := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hg 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hint : ∀ a : Torus d, |∫ y, g (a - y) ∂μ| ≤ M := by
    intro a
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => g (a - y)) (C := M)
      (Filter.Eventually.of_forall fun y => by simpa using hg (a - y))
    simpa using this
  have h1 : |∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, g (X i - X j)| ≤ (N : ℝ) ^ 2 * M := by
    calc |∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, g (X i - X j)|
        ≤ ∑ i : Fin N, |∑ j ∈ Finset.univ.erase i, g (X i - X j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin N, (N : ℝ) * M := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc |∑ j ∈ Finset.univ.erase i, g (X i - X j)|
              ≤ ∑ j ∈ Finset.univ.erase i, |g (X i - X j)| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ j ∈ Finset.univ.erase i, M := Finset.sum_le_sum fun j _ => hg _
            _ = ((Finset.univ.erase i).card : ℝ) * M := by simp
            _ ≤ N * M := by
                apply mul_le_mul_of_nonneg_right _ hM
                have : (Finset.univ.erase i).card ≤ N := by
                  have := Finset.card_erase_le (s := (Finset.univ : Finset (Fin N))) (a := i)
                  simpa using this
                exact_mod_cast this
      _ = (N : ℝ) ^ 2 * M := by simp; ring
  have h2 : |∑ i : Fin N, ∫ y, g (X i - y) ∂μ| ≤ N * M := by
    calc |∑ i : Fin N, ∫ y, g (X i - y) ∂μ| ≤ ∑ i : Fin N, |∫ y, g (X i - y) ∂μ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin N, M := Finset.sum_le_sum fun i _ => hint _
      _ = N * M := by simp
  have h3 : |∫ x, ∫ y, g (x - y) ∂μ ∂μ| ≤ M := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => ∫ y, g (x - y) ∂μ) (C := M)
      (Filter.Eventually.of_forall fun x => by simpa using hint x)
    simpa using this
  unfold modulatedEnergyKernel modulatedEnergy
  have hpos : (0 : ℝ) < 2 * (N : ℝ) ^ 2 := by positivity
  have hA : |1 / (2 * (N : ℝ) ^ 2) * ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, g (X i - X j)|
      ≤ M / 2 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * (N : ℝ) ^ 2))]
    calc 1 / (2 * (N : ℝ) ^ 2) * |∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, g (X i - X j)|
        ≤ 1 / (2 * (N : ℝ) ^ 2) * ((N : ℝ) ^ 2 * M) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = M / 2 := by field_simp
  have hB : |1 / (N : ℝ) * ∑ i : Fin N, ∫ y, g (X i - y) ∂μ| ≤ M := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
    calc 1 / (N : ℝ) * |∑ i : Fin N, ∫ y, g (X i - y) ∂μ| ≤ 1 / (N : ℝ) * (N * M) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = M := by field_simp
  have hC : |1 / 2 * ∫ x, ∫ y, g (x - y) ∂μ ∂μ| ≤ M / 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  rw [abs_le] at hA hB hC ⊢
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2]

/-- `g_λ` is bounded (smooth on the compact torus, Lemma D.3 (ii)). -/
lemma d4r_trunc_bdd (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Torus d, |fdlTruncT ψ s b lam x| ≤ M := by
  obtain ⟨-, -, -, -, hsm, -⟩ := fdl_kernel_torus_proof hd hs0 hsd hψ hb
  have hc : Continuous (fdlTruncT ψ s b lam) :=
    HRS.Torus.continuous_of_continuous_lift
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (fdlTruncT ψ s b lam)) from hsm lam h0 h1).continuous
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  have := hM x (Set.mem_univ x)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- `g` is large near `0`. -/
lemma d4r_g_large (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) (R : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε → ε ≤ 1 / 2 →
      ∀ x : Torus d, x ≠ 0 → KernelGrad.tdist x 0 ≤ ε → R ≤ periodicRiesz d s x := by
  obtain ⟨hi, -, -, -, -, -, -, -, -, -, hiv1, hiv2, -⟩ := fdl_kernel_torus_proof hd hs0 hsd hψ hb
  obtain ⟨C2, -, hC2⟩ := hi
  have hg : ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d, lam ≤ KernelGrad.tdist x 0 →
      fdlTruncT ψ s b lam x = periodicRiesz d s x := fun lam h0 h1 x hx => (hC2 lam h0 h1).2.1 x hx |>.2
  rcases hs0.eq_or_lt with hs | hs
  · -- `s = 0`
    obtain ⟨c, C1, hc, -, h4⟩ := hiv2 hs.symm
    have ht : Tendsto (fun ε : ℝ => c * Real.log (1 / ε) - C1) (𝓝[>] 0) atTop := by
      have h1 : Tendsto (fun ε : ℝ => 1 / ε) (𝓝[>] (0 : ℝ)) atTop := by
        simpa [one_div] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
      have h2 := Real.tendsto_log_atTop.comp h1
      exact tendsto_atTop_add_const_right _ _ ((h2.const_mul_atTop hc))
    filter_upwards [ht.eventually_ge_atTop R] with ε hε hε0 hε2 x hx0 hxe
    have htpos := KernelGrad.tdist_pos hx0
    have hlam := h4 (KernelGrad.tdist x 0) htpos (by linarith) x le_rfl (by linarith)
    rw [hg _ htpos (by linarith) x le_rfl] at hlam
    have hlog : Real.log (1 / ε) ≤ Real.log (1 / KernelGrad.tdist x 0) :=
      Real.log_le_log (by positivity) (one_div_le_one_div_of_le htpos hxe)
    nlinarith
  · obtain ⟨c, C1, hc, -, h4⟩ := hiv1 hs
    have ht : Tendsto (fun ε : ℝ => c * ε ^ (-s) - C1) (𝓝[>] 0) atTop :=
      tendsto_atTop_add_const_right _ _
        ((tendsto_rpow_neg_nhdsGT_zero (by linarith : -s < 0)).const_mul_atTop hc)
    filter_upwards [ht.eventually_ge_atTop R] with ε hε hε0 hε2 x hx0 hxe
    have htpos := KernelGrad.tdist_pos hx0
    have hlam := h4 (KernelGrad.tdist x 0) htpos (by linarith) x le_rfl
    rw [hg _ htpos (by linarith) x le_rfl] at hlam
    have hpow : ε ^ (-s) ≤ KernelGrad.tdist x 0 ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos htpos hxe (by linarith)
    nlinarith

/-- The configuration `x_j = (ε j) e_0`. -/
def d4r_X (hd : 1 ≤ d) (N : ℕ) (ε : ℝ) : Config d N :=
  fun j => HRS.Commutator.StressAux.tr (⟨0, by omega⟩ : Fin d) (ε * (j : ℕ))

lemma d4r_tr_sub (i : Fin d) (a b : ℝ) :
    HRS.Commutator.StressAux.tr i a - HRS.Commutator.StressAux.tr i b =
      HRS.Commutator.StressAux.tr i (a - b) := by
  funext j
  simp [HRS.Commutator.StressAux.tr, Torus.mk, sub_smul, QuotientAddGroup.mk_sub]

lemma d4r_X_notcol (hd : 1 ≤ d) {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hεN : ε * N ≤ 1 / 2) :
    d4r_X hd N ε ∉ collisionSet d N := by
  rintro ⟨i, j, hij, h⟩
  have h0 : HRS.Commutator.StressAux.tr (⟨0, by omega⟩ : Fin d) (ε * (i : ℕ) - ε * (j : ℕ)) = 0 := by
    rw [← d4r_tr_sub]; exact sub_eq_zero.mpr h
  have hne : ε * (i : ℕ) - ε * (j : ℕ) ≠ 0 := by
    intro h'
    have : (i : ℕ) = (j : ℕ) := by
      have : ε * ((i : ℕ) - (j : ℕ) : ℝ) = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 hε.ne'
      · exact_mod_cast sub_eq_zero.mp h1
    exact hij (Fin.ext this)
  have hi : ((i : ℕ) : ℝ) ≤ N := by exact_mod_cast i.2.le
  have hj : ((j : ℕ) : ℝ) ≤ N := by exact_mod_cast j.2.le
  have hi0 : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
  have hab : |ε * (i : ℕ) - ε * (j : ℕ)| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> nlinarith
  have := HRS.Commutator.StressAux.tdist_tr (⟨0, by omega⟩ : Fin d) hab
  rw [h0] at this
  have h00 : KernelGrad.tdist (0 : Torus d) 0 = 0 := HRS.Commutator.EnergyAux.tdist_eq_zero_iff 0 |>.mpr rfl
  rw [h00] at this
  exact hne (abs_eq_zero.mp this.symm)

lemma d4r_pair_tdist (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    d4r_X hd N ε ⟨0, by omega⟩ - d4r_X hd N ε ⟨1, by omega⟩ ≠ 0 ∧
      KernelGrad.tdist (d4r_X hd N ε ⟨0, by omega⟩ - d4r_X hd N ε ⟨1, by omega⟩) 0 = ε := by
  have e : d4r_X hd N ε ⟨0, by omega⟩ - d4r_X hd N ε ⟨1, by omega⟩ =
      -HRS.Commutator.StressAux.tr (⟨0, by omega⟩ : Fin d) ε := by
    simp only [d4r_X, Nat.cast_zero, mul_zero, Nat.cast_one, mul_one,
      HRS.Commutator.StressAux.tr_zero, zero_sub]
  have ht : KernelGrad.tdist (-HRS.Commutator.StressAux.tr (⟨0, by omega⟩ : Fin d) ε) 0 = ε := by
    rw [HRS.Commutator.EnergyAux.tdist_neg_zero,
      HRS.Commutator.StressAux.tdist_tr _ (by rw [abs_of_pos hε]; exact hε2), abs_of_pos hε]
  refine ⟨?_, by rw [e, ht]⟩
  rw [e]
  exact HRS.Commutator.EnergyAux.ne_zero_of_tdist_pos (by rw [ht]; exact hε)

lemma d4r_pairW_ge {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s b η : ℝ} (hb0 : 0 ≤ b) {N : ℕ}
    (hN : 2 ≤ N) (X : Config d N) :
    1 / (N : ℝ) ^ 2 * fdlWT ψ s b η (X ⟨0, by omega⟩ - X ⟨1, by omega⟩) ≤ fdlPairW ψ s b η X := by
  unfold fdlPairW
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hne : (⟨1, by omega⟩ : Fin N) ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin N) := by
    simp [Fin.ext_iff]
  have h1 : fdlWT ψ s b η (X ⟨0, by omega⟩ - X ⟨1, by omega⟩) ≤
      ∑ j ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin N), fdlWT ψ s b η (X ⟨0, by omega⟩ - X j) :=
    Finset.single_le_sum (f := fun j => fdlWT ψ s b η (X ⟨0, by omega⟩ - X j))
      (fun j _ => d47_fdlWT_nonneg hψ hb0 _) hne
  refine h1.trans ?_
  exact Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.univ.erase i, fdlWT ψ s b η (X i - X j))
    (fun i _ => Finset.sum_nonneg fun j _ => d47_fdlWT_nonneg hψ hb0 _) (Finset.mem_univ _)

theorem fdl_compare_reverse_false_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) (C₀ C : ℝ) {N : ℕ} (hN : 2 ≤ N)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (hlam : smearScale d N Λ < 1 / 2)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρΛ : ∀ x, ρ x ≤ Λ) :
    ∃ X : Config d N, X ∉ collisionSet d N ∧
      C * (fdlEnergy ψ s b (smearScale d N Λ) X (withDensityReal ρ) + oNΛ d s C₀ Λ N)
        < rieszEnergy d s X (withDensityReal ρ) := by
  have hN1 : 1 ≤ N := by omega
  haveI := isProb_withDensityReal hρ
  obtain ⟨C₀', C', hC₀', hC', hcmp⟩ := fdl_compare_proof hd hs0 hsd hψ hb
  have hlam0 : 0 < smearScale d N Λ := d47_lam_pos hN1 hΛ
  have hlam1 : smearScale d N Λ < 1 := by linarith
  obtain ⟨M, hM, hMb⟩ := d4r_trunc_bdd hd hs0 hsd hψ hb hlam0 hlam1
  have hb0 : 0 ≤ b := hb.1.le
  have hΛ0 : 0 ≤ Λ := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set o := oNΛ d s C₀ Λ N with ho
  set E0 : ℝ := C' * Λ * smearScale d N Λ ^ ((d : ℝ) - s) with hE0def
  have hE0 : 0 ≤ E0 := by
    have : 0 ≤ smearScale d N Λ ^ ((d : ℝ) - s) := Real.rpow_nonneg hlam0.le _
    positivity
  set T : ℝ := |C| * (2 * M + |o|) with hT
  set R : ℝ := (N : ℝ) ^ 2 * (2 * (T + 2 * M + E0)) + M + 1 with hR
  have hev := d4r_g_large hd hs0 hsd hψ hb R
  have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioo (0 : ℝ) (1 / (2 * N)) :=
    Ioo_mem_nhdsGT (by positivity)
  obtain ⟨ε, hRε, hεmem⟩ := (hev.and hev2).exists
  obtain ⟨hε0, hεN⟩ := hεmem
  have hεN' : ε * N ≤ 1 / 2 := by
    have : ε * N < 1 / (2 * N) * N := mul_lt_mul_of_pos_right hεN hNpos
    have h2 : 1 / (2 * (N : ℝ)) * N = 1 / 2 := by field_simp
    linarith
  have hε2 : ε ≤ 1 / 2 := by
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    nlinarith
  have hnc := d4r_X_notcol hd hε0 hεN'
  refine ⟨d4r_X hd N ε, hnc, ?_⟩
  set X := d4r_X hd N ε with hX
  obtain ⟨hxne, hxd⟩ := d4r_pair_tdist hd hN hε0 hε2
  set x := X ⟨0, by omega⟩ - X ⟨1, by omega⟩ with hxdef
  have hg : R ≤ periodicRiesz d s x := hRε hε0 hε2 x hxne hxd.le
  have hw : periodicRiesz d s x - M ≤ fdlWT ψ s b (smearScale d N Λ) x := by
    have h1 : fdlTruncT ψ s b (smearScale d N Λ) x =
        periodicRiesz d s x - fdlWT ψ s b (smearScale d N Λ) x := by
      unfold fdlTruncT; simp [hxne]
    have h2 := (abs_le.mp (hMb x)).2
    linarith
  have hP : 1 / (N : ℝ) ^ 2 * fdlWT ψ s b (smearScale d N Λ) x ≤
      fdlPairW ψ s b (smearScale d N Λ) X := d4r_pairW_ge hψ hb0 hN X
  have hcm := (hcmp Λ hΛ N hN1 hlam ρ hρ hρΛ X hnc).2.2.1
  have hFl : |fdlEnergy ψ s b (smearScale d N Λ) X (withDensityReal ρ)| ≤ 2 * M :=
    d4r_energy_bound hMb hN1 X _
  have hkey : 1 / (N : ℝ) ^ 2 * (R - M) = 2 * (T + 2 * M + E0) + 1 / (N : ℝ) ^ 2 := by
    rw [hR]; field_simp; ring
  have hwR : 1 / (N : ℝ) ^ 2 * (R - M) ≤ 1 / (N : ℝ) ^ 2 * fdlWT ψ s b (smearScale d N Λ) x :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hpos2 : 0 < 1 / (N : ℝ) ^ 2 := by positivity
  have hE0' : C' * Λ * smearScale d N Λ ^ ((d : ℝ) - s) = E0 := rfl
  rw [hE0', abs_le] at hcm
  have hFl' := abs_le.mp hFl
  -- the right-hand side
  have hrhs : C * (fdlEnergy ψ s b (smearScale d N Λ) X (withDensityReal ρ) + o) ≤ T := by
    calc C * (fdlEnergy ψ s b (smearScale d N Λ) X (withDensityReal ρ) + o)
        ≤ |C * (fdlEnergy ψ s b (smearScale d N Λ) X (withDensityReal ρ) + o)| := le_abs_self _
      _ = |C| * |fdlEnergy ψ s b (smearScale d N Λ) X (withDensityReal ρ) + o| := abs_mul _ _
      _ ≤ |C| * (2 * M + |o|) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact (abs_add_le _ _).trans (by linarith)
  refine lt_of_le_of_lt hrhs ?_
  linarith [hcm.1, hcm.2, hFl'.1, hFl'.2]

example := (@fdl_compare_reverse_false_proof : type_of% @HRS.fdl_compare_reverse_false)

end HRS.MC.D4R
