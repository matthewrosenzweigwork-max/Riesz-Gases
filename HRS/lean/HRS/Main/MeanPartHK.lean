import HRS.Sections.Sec5
import HRS.Uniform.Q54cAux56
import HRS.PDE.MeanFieldWeak
import HRS.PDE.MeanFieldAprioriClassicalOn
import HRS.PDE.MeanFieldLocalB
import HRS.PDE.EnergyDrift
import HRS.PDE.MeanFieldAprioriPhi

/-!
# Corollary 5.17, defect R1 (lemma L1): the weak solution of `IsMeanTransient` is the `H^K` solution

`mphk_hk_of_meanTransient`: for `ρ` with `IsMeanTransient` (weak mean-field solution on every
`[0,T]`, smooth, positive, with the uniform `C^j` asymptotics), and every integer `K > d/2 + 6`,
`t ↦ coeffOf (ρ t)` is a solution `IsMFSolutionHK` with datum `ρ 0` and `mfPath = ρ` on `[0,∞)`.

Route: the `C^j` asymptotics give a bound of `cbNorm n (ρ t)` uniform in `t ≥ 0`
(`mphk_unif`), hence a bound of the `H^n` norms (`memHs_coeffOf_cbNorm`).  The junk-value trap of
the Bochner integral in `IsMeanFieldSolution.weak` is handled by the existing
`HRS.Uniform.Q54c.weak_continuity` (weak time continuity of `∫ψ ρ_t` for regular weak solutions),
which gives modewise continuity of `coeffOf (ρ t)`.  Together with the uniform `H^{n}` bound this
gives continuity in `H^K` (`tail_bound`), then continuity of the right-hand side (hence its
integrability), and finally the integrated equation mode by mode from the weak formulation tested
with `cos` and `sin` (`weak_integrand_eq`).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {d : ℕ}

theorem mphk_cbNorm_const (n : ℕ) (c : ℝ) : Torus.cbNorm n (fun _ : Torus d => c) ≤ |c| := by
  unfold Torus.cbNorm
  rw [Finset.sum_range_succ']
  have h0 : ∀ j ∈ Finset.range n,
      (⨆ x : Euc d, ‖iteratedFDeriv ℝ (j + 1) (Torus.lift fun _ : Torus d => c) x‖) = 0 := by
    intro j _
    have : iteratedFDeriv ℝ (j + 1) (Torus.lift fun _ : Torus d => c) = 0 :=
      iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j) c
    simp [this]
  rw [Finset.sum_eq_zero h0, zero_add]
  simp [Torus.lift]

theorem mphk_rate_nonneg (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (k : Lattice d) : 0 ≤ PDE.transientRate d s β k := by
  by_cases hk : k = 0
  · subst hk
    have h0 : Lattice.enorm (0 : Lattice d) = 0 := by
      have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
      simp [Lattice.enorm, this]
    simp [PDE.transientRate, h0]
  · exact (Cor516Aux.transientRate_pos' hd hs0 hsd hβ k hk).le

/-- The `C^n` norms of `ρ^t` are bounded uniformly in `t ≥ 0`. -/
theorem mphk_unif (hd : 2 ≤ d) {s β : ℝ} {hs0 : 0 ≤ s} {hsd : s < d} {hβ : 0 < β} {k : Lattice d}
    {ε A : ℝ} {ρ : ℝ → Torus d → ℝ} {C : ℝ} {Cj : ℕ → ℝ}
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (n : ℕ) :
    ∃ Λ : ℝ, ∀ t, 0 ≤ t → Torus.IsCk (n : WithTop ℕ∞) (ρ t) ∧ Torus.cbNorm n (ρ t) ≤ Λ := by
  refine ⟨|Cj n| * ε ^ 2 + 1 + |A| * Torus.cbNorm n (PDE.cosTest k), fun t ht => ?_⟩
  have hsm : Torus.IsCk (n : WithTop ℕ∞) (ρ t) :=
    Cor516Aux.isCk_of_isSmooth' (hρ.smooth_pos t ht).1 n
  refine ⟨hsm, ?_⟩
  set lam := PDE.transientRate d s β k with hlam
  have hl0 : 0 ≤ lam := mphk_rate_nonneg hd hs0 hsd hβ k
  set a : ℝ := A * Real.exp (-lam * t) with ha
  have hψ : Torus.IsCk (n : WithTop ℕ∞) (PDE.cosTest k) := Cor516Aux.isCk_cosTest' k n
  have hRck : Torus.IsCk (n : WithTop ℕ∞) (fun x => ρ t x - 1 - a * PDE.cosTest k x) :=
    Cor516Aux.isCk_sub' (Cor516Aux.isCk_sub' hsm (Cor516Aux.isCk_const' n 1))
      (Cor516Aux.isCk_const_mul' hψ a)
  have hc1 : Torus.IsCk (n : WithTop ℕ∞) (fun _ : Torus d => (1 : ℝ)) := Cor516Aux.isCk_const' n 1
  have haψ : Torus.IsCk (n : WithTop ℕ∞) (fun x => a * PDE.cosTest k x) :=
    Cor516Aux.isCk_const_mul' hψ a
  have e : ρ t = ((fun x => ρ t x - 1 - a * PDE.cosTest k x) + (fun _ : Torus d => (1 : ℝ))) +
      (fun x => a * PDE.cosTest k x) := by
    funext x; simp only [Pi.add_apply]; ring
  have hRc1 : Torus.IsCk (n : WithTop ℕ∞)
      ((fun x => ρ t x - 1 - a * PDE.cosTest k x) + (fun _ : Torus d => (1 : ℝ))) := by
    unfold Torus.IsCk Torus.lift at *
    exact hRck.add hc1
  have h1 := Torus.cbNorm_add_le n _ _ hRc1 haψ
  have h2 := Torus.cbNorm_add_le n _ _ hRck hc1
  have h3 := Cor516Aux.cbNorm_const_mul' hψ a
  have h4 := mphk_cbNorm_const (d := d) n 1
  have hasy := hρ.asymp n t ht
  have hex : Real.exp (-3 * lam * t / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [mul_nonneg hl0 ht]
  have hex2 : Real.exp (-lam * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [mul_nonneg hl0 ht]
  have hR : Torus.cbNorm n (fun x => ρ t x - 1 - a * PDE.cosTest k x) ≤ |Cj n| * ε ^ 2 := by
    refine hasy.trans ?_
    have h5 : Cj n * ε ^ 2 * Real.exp (-3 * lam * t / 2) ≤ |Cj n| * ε ^ 2 * Real.exp (-3 * lam * t / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
        (Real.exp_pos _).le
    have h6 : |Cj n| * ε ^ 2 * Real.exp (-3 * lam * t / 2) ≤ |Cj n| * ε ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hex (by positivity)
    linarith
  have hA : |a| ≤ |A| := by
    rw [ha, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (abs_nonneg _) hex2
  have hψ0 := Cor516Aux.cbNorm_nonneg' n (PDE.cosTest k)
  have h7 : |a| * Torus.cbNorm n (PDE.cosTest k) ≤ |A| * Torus.cbNorm n (PDE.cosTest k) :=
    mul_le_mul_of_nonneg_right hA hψ0
  rw [e]
  have h8 : |(1 : ℝ)| = 1 := abs_one
  linarith

/-- Continuity into `H^K` from modewise continuity and a bound in `H^{K+η}`. -/
theorem mphk_contHs {c : ℝ → PDE.Coeff d} {S : Set ℝ} (K η B : ℝ) (hη : 0 < η)
    (hmem : ∀ τ ∈ S, PDE.MemHs (K + η) (c τ) ∧ PDE.hsNorm (K + η) (c τ) ≤ B)
    (hmode : ∀ k, ContinuousOn (fun τ => c τ k) S) : PDE.ContinuousInHsOn K c S := by
  have hB0 : ∀ τ ∈ S, 0 ≤ B := fun τ hτ => (PDE.MFLocal.hsNorm_nonneg _ _).trans (hmem τ hτ).2
  by_cases hS : S = ∅
  · subst hS
    exact PDE.MFLocal.contInHs_of_trunc (fun τ hτ => absurd hτ (Set.notMem_empty _))
      (fun k => continuousOn_empty _) (fun ε hε => ⟨0, fun τ hτ => absurd hτ (Set.notMem_empty _)⟩)
  obtain ⟨τ₀, hτ₀⟩ := Set.nonempty_iff_ne_empty.2 hS
  have hB : 0 ≤ B := hB0 τ₀ hτ₀
  refine PDE.MFLocal.contInHs_of_trunc
    (fun τ hτ => PDE.MFLocal.memHs_mono (by linarith) (hmem τ hτ).1) hmode ?_
  intro ε hε
  obtain ⟨n, hn⟩ := ((PDE.MFLocal.tendsto_tail_const η hη).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / (B + 1) by positivity))).exists
  refine ⟨n, fun t ht => ?_⟩
  have h1 := PDE.MFLocal.tail_bound K η hη.le n (c t) (hmem t ht).1
  refine h1.trans ?_
  calc _ ≤ Real.sqrt ((1 + 4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) ^ (-η)) * B :=
        mul_le_mul_of_nonneg_left (hmem t ht).2 (Real.sqrt_nonneg _)
    _ ≤ ε / (B + 1) * B := mul_le_mul_of_nonneg_right hn.le hB
    _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

theorem mphk_integrable_of_continuous {φ : Torus d → ℝ} (hφ : Continuous φ) : Integrable φ :=
  hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem mphk_coeff_eq {φ : Torus d → ℝ} (hφ : Continuous φ) (k : Lattice d) :
    PDE.coeffOf φ k = ((∫ x, Torus.cosMode k x * φ x : ℝ) : ℂ) +
      ((-(∫ x, Torus.sinMode k x * φ x) : ℝ) : ℂ) * Complex.I := by
  rw [PDE.coeffOf_eq_fcoef]
  unfold Torus.fcoef
  exact Torus.integral_mode_mul_real (mphk_integrable_of_continuous hφ) k

/-- Weak time continuity of `t ↦ ∫ ψ ρ_t` on `[0,∞)`. -/
theorem mphk_weakcont (hd : 2 ≤ d) {s β : ℝ} {hs0 : 0 ≤ s} {hsd : s < d} {hβ : 0 < β}
    {k : Lattice d} {ε A : ℝ} {ρ : ℝ → Torus d → ℝ} {C : ℝ} {Cj : ℕ → ℝ}
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) {ψ : Torus d → ℝ} (hψ : Continuous ψ) :
    ContinuousOn (fun t => ∫ x, ψ x * ρ t x) (Set.Ici 0) := by
  obtain ⟨Λ, hΛ⟩ := mphk_unif hd hρ (d + 1)
  intro τ0 hτ0
  have hτ0' : (0 : ℝ) ≤ τ0 := hτ0
  have hT : (0 : ℝ) < τ0 + 1 := by linarith
  have hreg : IsRegularMF (d + 1) Λ (τ0 + 1) ρ := fun t ht => hΛ t ht.1
  have hc := HRS.Uniform.Q54c.weak_continuity (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ)
    (by omega) (τ0 + 1) Λ hT.le (d + 1) le_rfl ρ (hρ.sol _ hT) hreg
    (Cor516Aux.isCk_const' 1 0) ψ hψ
  refine (hc τ0 ⟨hτ0', by linarith⟩).mono_of_mem_nhdsWithin ?_
  exact mem_nhdsWithin.2 ⟨Set.Iio (τ0 + 1), isOpen_Iio, by simp, fun x hx => ⟨hx.2, hx.1.le⟩⟩

theorem mphk_modecont (hd : 2 ≤ d) {s β : ℝ} {hs0 : 0 ≤ s} {hsd : s < d} {hβ : 0 < β}
    {k : Lattice d} {ε A : ℝ} {ρ : ℝ → Torus d → ℝ} {C : ℝ} {Cj : ℕ → ℝ}
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (j : Lattice d) :
    ContinuousOn (fun t => PDE.coeffOf (ρ t) j) (Set.Ici 0) := by
  have hc : ∀ t ∈ Set.Ici (0 : ℝ), Continuous (ρ t) := fun t ht =>
    Cor516Aux.continuous_of_isCk' (Cor516Aux.isCk_of_isSmooth' (hρ.smooth_pos t ht).1 0)
  have h1 := mphk_weakcont hd hρ (Torus.continuous_cosMode j)
  have h2 := mphk_weakcont hd hρ (Torus.continuous_sinMode j)
  have hF : ContinuousOn (fun t => ((∫ x, Torus.cosMode j x * ρ t x : ℝ) : ℂ) +
      ((-(∫ x, Torus.sinMode j x * ρ t x) : ℝ) : ℂ) * Complex.I) (Set.Ici 0) :=
    (Complex.continuous_ofReal.comp_continuousOn h1).add
      ((Complex.continuous_ofReal.comp_continuousOn h2.neg).mul continuousOn_const)
  exact hF.congr (fun t ht => mphk_coeff_eq (hc t ht) j)

/-- Uniform bound of the `H^n` norms of `coeffOf (ρ t)`. -/
theorem mphk_hsbound (hd : 2 ≤ d) {s β : ℝ} {hs0 : 0 ≤ s} {hsd : s < d} {hβ : 0 < β}
    {k : Lattice d} {ε A : ℝ} {ρ : ℝ → Torus d → ℝ} {C : ℝ} {Cj : ℕ → ℝ}
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (n : ℕ) :
    ∃ B : ℝ, ∀ t, 0 ≤ t →
      PDE.MemHs (n : ℝ) (PDE.coeffOf (ρ t)) ∧ PDE.hsNorm (n : ℝ) (PDE.coeffOf (ρ t)) ≤ B := by
  obtain ⟨Λ, hΛ⟩ := mphk_unif hd hρ n
  refine ⟨Real.sqrt (((d : ℝ) + 1) ^ n * ((PDE.multiIndices d n).card : ℝ) * Λ ^ 2), fun t ht => ?_⟩
  obtain ⟨hck, hcb⟩ := hΛ t ht
  obtain ⟨hm, hn⟩ := PDE.memHs_coeffOf_cbNorm n (ρ t) hck
  refine ⟨hm, ?_⟩
  unfold PDE.hsNorm
  refine Real.sqrt_le_sqrt (hn.trans ?_)
  have h0 := Cor516Aux.cbNorm_nonneg' n (ρ t)
  have : Torus.cbNorm n (ρ t) ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ h0 hcb 2
  exact mul_le_mul_of_nonneg_left this (by positivity)

theorem mphk_cont (hd : 2 ≤ d) {s β : ℝ} {hs0 : 0 ≤ s} {hsd : s < d} {hβ : 0 < β}
    {k : Lattice d} {ε A : ℝ} {ρ : ℝ → Torus d → ℝ} {C : ℝ} {Cj : ℕ → ℝ}
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (K : ℕ) :
    PDE.ContinuousInHsOn (K : ℝ) (fun t => PDE.coeffOf (ρ t)) (Set.Ici 0) := by
  obtain ⟨B, hB⟩ := mphk_hsbound hd hρ (K + 1)
  refine mphk_contHs (K : ℝ) 1 B one_pos (fun τ hτ => ?_) (fun j => mphk_modecont hd hρ j)
  have := hB τ hτ
  rwa [show ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 by push_cast; ring] at this

theorem mphk_rhs_integrable (hd : 2 ≤ d) {s β : ℝ} {hs0 : 0 ≤ s} {hsd : s < d} {hβ : 0 < β}
    {k : Lattice d} {ε A : ℝ} {ρ : ℝ → Torus d → ℝ} {C : ℝ} {Cj : ℕ → ℝ}
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (K : ℕ) (hK : (d : ℝ) / 2 + 1 < K) :
    PDE.ContinuousInHsOn ((K : ℝ) - 2)
        (fun σ => PDE.mfRhsCoeff d s (fun _ => 0) β⁻¹ (PDE.coeffOf (ρ σ))) (Set.Ici 0) := by
  have hV : Torus.IsCk ((K : WithTop ℕ∞) + 2) (fun _ : Torus d => (0 : ℝ)) := by
    have := Cor516Aux.isCk_const' (d := d) (K + 2) 0
    simpa using this
  exact PDE.MFApriori.rhs_continuousInHsOn' (by omega) s hs0 hsd K hK _ hV β⁻¹ _ (Set.Ici 0)
    (mphk_cont hd hρ K)

theorem mphk_weak_pair {s β : ℝ} {hs0 : 0 ≤ s} {hsd : s < d} {hβ : 0 < β}
    {k : Lattice d} {ε A : ℝ} {ρ : ℝ → Torus d → ℝ} {C : ℝ} {Cj : ℕ → ℝ}
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, ψ x * ρ t x) - (∫ x, ψ x * ρ 0 x) =
      ∫ r in Set.Icc 0 t, HRS.Uniform.Q54c.wkG (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) ρ ψ r := by
  have hmf := hρ.sol (t + 1) (by linarith)
  have h := HRS.Uniform.Q54c.weak_eq_wkG hmf hψ (t := t) ⟨ht, by linarith⟩
  rwa [HRS.Uniform.Q54c.pair_wDR (hmf.density t ⟨ht, by linarith⟩),
    HRS.Uniform.Q54c.pair_wDR (hmf.density 0 ⟨le_rfl, by linarith⟩)] at h

theorem mphk_wk_integrand (hd : 2 ≤ d) {s β : ℝ} {hs0 : 0 ≤ s} {hsd : s < d} {hβ : 0 < β}
    {k : Lattice d} {ε A : ℝ} {ρ : ℝ → Torus d → ℝ} {C : ℝ} {Cj : ℕ → ℝ}
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (K : ℕ) (hK : (d : ℝ) / 2 + 6 < K)
    {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) {r : ℝ} (hr : 0 ≤ r) :
    HRS.Uniform.Q54c.wkG (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) ρ ψ r =
      ∫ x, ψ x * PDE.toFun (PDE.mfRhsCoeff d s (fun _ => 0) β⁻¹ (PDE.coeffOf (ρ r))) x := by
  have hρc : Continuous (ρ r) :=
    Cor516Aux.continuous_of_isCk' (Cor516Aux.isCk_of_isSmooth' (hρ.smooth_pos r hr).1 0)
  have hmem : PDE.MemHs (K : ℝ) (PDE.coeffOf (ρ r)) := (mphk_cont hd hρ K).1 r hr
  have hsum : Summable fun j => ‖PDE.coeffOf (ρ r) j‖ :=
    PDE.summable_norm_of_memHs (K : ℝ) (by linarith) _ hmem
  have hto : PDE.toFun (PDE.coeffOf (ρ r)) = ρ r := PDE.toFun_coeffOf (ρ r) hρc hsum
  have hreal : PDE.IsRealCoeff (PDE.coeffOf (ρ r)) :=
    PDE.isRealCoeff_coeffOf _ (mphk_integrable_of_continuous hρc)
  have hV : Torus.IsCk 2 (fun _ : Torus d => (0 : ℝ)) := by
    have := Cor516Aux.isCk_const' (d := d) 2 0
    simpa using this
  have hVK : PDE.MemHs (K : ℝ) (PDE.coeffOf (fun _ : Torus d => (0 : ℝ))) := by
    have := PDE.MFApriori.Aux.memHs_of_isCk_nat K (fun _ : Torus d => (0 : ℝ)) (by
      have := Cor516Aux.isCk_const' (d := d) (K + 2) 0
      simpa using this)
    exact this
  have h := PDE.MFWeak.weak_integrand_eq (by omega) s hs0 hsd (K : ℝ) (by linarith)
    (fun _ => 0) hV hVK β hβ (PDE.coeffOf (ρ r)) hmem hreal
    (fun x => by rw [hto]; exact ((hρ.smooth_pos r hr).2 x).le) ψ hψ
  rw [hto] at h
  exact h.symm

theorem mphk_rhs_trig (hd : 2 ≤ d) {s β : ℝ} {hs0 : 0 ≤ s} {hsd : s < d} {hβ : 0 < β}
    {k : Lattice d} {ε A : ℝ} {ρ : ℝ → Torus d → ℝ} {C : ℝ} {Cj : ℕ → ℝ}
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (K : ℕ) (hK : (d : ℝ) / 2 + 6 < K)
    (j : Lattice d) {r : ℝ} (hr : 0 ≤ r) :
    (∫ x, Torus.cosMode j x * PDE.toFun (PDE.mfRhsCoeff d s (fun _ => 0) β⁻¹ (PDE.coeffOf (ρ r))) x) =
        (PDE.mfRhsCoeff d s (fun _ => 0) β⁻¹ (PDE.coeffOf (ρ r)) j).re ∧
      (∫ x, Torus.sinMode j x * PDE.toFun (PDE.mfRhsCoeff d s (fun _ => 0) β⁻¹ (PDE.coeffOf (ρ r))) x) =
        -(PDE.mfRhsCoeff d s (fun _ => 0) β⁻¹ (PDE.coeffOf (ρ r)) j).im := by
  set f := PDE.mfRhsCoeff d s (fun _ => 0) β⁻¹ (PDE.coeffOf (ρ r)) with hf
  have hρc : Continuous (ρ r) :=
    Cor516Aux.continuous_of_isCk' (Cor516Aux.isCk_of_isSmooth' (hρ.smooth_pos r hr).1 0)
  have hreal : PDE.IsRealCoeff (PDE.coeffOf (ρ r)) :=
    PDE.isRealCoeff_coeffOf _ (mphk_integrable_of_continuous hρc)
  have hfreal : PDE.IsRealCoeff f :=
    PDE.MFApriori.isRealCoeff_mfRhsCoeff s _ (mphk_integrable_of_continuous continuous_const) _ _ hreal
  have hmem : PDE.MemHs ((K : ℝ) - 2) f :=
    (mphk_rhs_integrable hd hρ K (by linarith)).1 r hr
  have hsum : Summable fun j => ‖f j‖ := PDE.summable_norm_of_memHs ((K : ℝ) - 2) (by linarith) _ hmem
  have hco : PDE.coeffOf (PDE.toFun f) = f := PDE.coeffOf_toFun f hfreal hsum
  have h := mphk_coeff_eq (PDE.MFProduct.continuous_toFun f hsum) j
  rw [hco] at h
  constructor
  · have := congrArg Complex.re h
    simpa using this.symm
  · have := congrArg Complex.im h
    simp at this
    linarith

theorem mphk_eq (hd : 2 ≤ d) {s β : ℝ} {hs0 : 0 ≤ s} {hsd : s < d} {hβ : 0 < β}
    {k : Lattice d} {ε A : ℝ} {ρ : ℝ → Torus d → ℝ} {C : ℝ} {Cj : ℕ → ℝ}
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) (K : ℕ) (hK : (d : ℝ) / 2 + 6 < K)
    (j : Lattice d) {t : ℝ} (ht : 0 ≤ t) :
    PDE.coeffOf (ρ t) j = PDE.coeffOf (ρ 0) j +
      ∫ σ in (0 : ℝ)..t, PDE.mfRhsCoeff d s (fun _ => 0) β⁻¹ (PDE.coeffOf (ρ σ)) j := by
  have hint : IntegrableOn (fun σ => PDE.mfRhsCoeff d s (fun _ => 0) β⁻¹ (PDE.coeffOf (ρ σ)) j)
      (Set.Icc 0 t) :=
    ((PDE.MFLocal.continuousOn_mode (mphk_rhs_integrable hd hρ K (by linarith)) j).mono
      Set.Icc_subset_Ici_self).integrableOn_Icc
  have hc : ∀ r, 0 ≤ r → Continuous (ρ r) := fun r hr =>
    Cor516Aux.continuous_of_isCk' (Cor516Aux.isCk_of_isSmooth' (hρ.smooth_pos r hr).1 0)
  have hcos2 : Torus.IsCk 2 (Torus.cosMode j) := by
    exact_mod_cast PDE.MFPair.isCk_cos_ps (d := d) j 2
  have hsin2 : Torus.IsCk 2 (Torus.sinMode j) := by
    exact_mod_cast PDE.MFPair.isCk_sin_ps (d := d) j 2
  have hcos : (∫ x, Torus.cosMode j x * ρ t x) - (∫ x, Torus.cosMode j x * ρ 0 x) =
      (∫ σ in Set.Icc 0 t, PDE.mfRhsCoeff d s (fun _ => 0) β⁻¹ (PDE.coeffOf (ρ σ)) j).re := by
    rw [mphk_weak_pair hρ hcos2 ht]
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
    rw [mphk_wk_integrand hd hρ K hK hcos2 hr.1]
    exact (mphk_rhs_trig hd hρ K hK j hr.1).1
  have hsin : (∫ x, Torus.sinMode j x * ρ t x) - (∫ x, Torus.sinMode j x * ρ 0 x) =
      -(∫ σ in Set.Icc 0 t, PDE.mfRhsCoeff d s (fun _ => 0) β⁻¹ (PDE.coeffOf (ρ σ)) j).im := by
    rw [mphk_weak_pair hρ hsin2 ht]
    have := integral_im hint
    simp only [RCLike.im_to_complex] at this
    rw [← this, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
    rw [mphk_wk_integrand hd hρ K hK hsin2 hr.1]
    exact (mphk_rhs_trig hd hρ K hK j hr.1).2
  rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc,
    mphk_coeff_eq (hc t ht) j, mphk_coeff_eq (hc 0 le_rfl) j]
  apply Complex.ext
  · simp
    linarith [hcos]
  · simp
    linarith [hsin]

/-- **Lemma L1 (Corollary 5.17, defect R1).**  The weak solution of `IsMeanTransient` is the
`H^K` coefficient solution `PDE.IsMFSolutionHK` used by `PreparedData`, for every integer
`K > d/2 + 6`. -/
theorem mphk_hk_of_meanTransient (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (k : Lattice d) (ε A : ℝ) (ρ : ℝ → Torus d → ℝ) (C : ℝ) (Cj : ℕ → ℝ)
    (hρ : IsMeanTransient d s β hs0 hsd hβ k ε A ρ C Cj) :
    ∀ K : ℕ, (d : ℝ) / 2 + 6 < K → ∃ ρc : ℝ → PDE.Coeff d,
      PDE.IsMFSolutionHK d s (fun _ => 0) β⁻¹ (K : ℝ) (ρ 0) ρc ∧
        ∀ t, 0 ≤ t → PDE.mfPath ρc t = ρ t := by
  intro K hK
  refine ⟨fun t => PDE.coeffOf (ρ t), ⟨rfl, mphk_cont hd hρ K, ?_, ?_⟩, ?_⟩
  · intro j t ht
    exact ((PDE.MFLocal.continuousOn_mode (mphk_rhs_integrable hd hρ K (by linarith)) j).mono
      Set.Icc_subset_Ici_self).integrableOn_Icc
  · intro j t ht
    exact mphk_eq hd hρ K hK j ht
  · intro t ht
    have hρc : Continuous (ρ t) :=
      Cor516Aux.continuous_of_isCk' (Cor516Aux.isCk_of_isSmooth' (hρ.smooth_pos t ht).1 0)
    have hsum : Summable fun j => ‖PDE.coeffOf (ρ t) j‖ :=
      PDE.summable_norm_of_memHs (K : ℝ) (by linarith) _ ((mphk_cont hd hρ K).1 t ht)
    exact PDE.toFun_coeffOf (ρ t) hρc hsum
