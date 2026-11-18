import HRS.MS.FeatDecAux3

/-!
# S8.5 `feature_decay`, part 4 (S85 packet): the UL witness with the explicit order `j₀ = 5`

`s85_witness5` is `HRS.MS.UlW.ul_adjoint_input_witness` with the existential `j₀` replaced by its value `5` (the proof is the
proof of that theorem verbatim; the frozen statement hides the value, which is needed here to bound the oscillator index).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace HRS.MS.S85

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.Ul HRS.MS.UlW

variable {d : ℕ}

theorem s85_witness5 (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) :
    ∀ j : ℕ, 5 ≤ j → ∀ (T ν : ℝ) (Q M : Matrix (Fin d) (Fin d) ℝ) (c₀ : Euc d)
      (ρ : Euc d → ℝ), 0 ≤ T → 0 < ν → Q.IsSymm → IsSchwartzDensity ρ →
      ∃ K : ℝ, UlAdjointInput θ ((⟨s, M, quadV Q c₀, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) T j K := by
  intro j hj T ν Q M c₀ ρ hT hν hQ hρ
  set k : ℕ := j + 1 + ⌈(d : ℝ) / 2⌉₊ with hk
  have hceil : (d : ℝ) / 2 ≤ ⌈(d : ℝ) / 2⌉₊ := Nat.le_ceil _
  have hj5 : (5 : ℝ) ≤ j := by exact_mod_cast hj
  have hk5 : (5 : ℝ) + (d : ℝ) / 2 < k := by rw [hk]; push_cast; linarith
  have hk4 : (4 : ℝ) + (d : ℝ) / 2 < k := by linarith
  have hkj : (j : ℝ) + (d : ℝ) / 2 < k := by rw [hk]; push_cast; linarith
  have hk2 : (d : ℝ) / 2 < k := by linarith
  have hd1 : 1 ≤ d := by omega
  set c : Euc d → Euc d :=
    fun x => Torus.matVec M (convGradConvW (rieszKernelGrad d s) ρ x) - c₀ with hc
  have hcsb : IsSmoothBounded c := ulw_c_smoothBounded hd hs0 hsd M c₀ hρ.2
  obtain ⟨Cev, hCev⟩ := ul_evolution_exists hs0 hsd θ hθ k hk4 T ν hT hν Q M ρ hρ.2 c hcsb
  obtain ⟨Cap, hCap0, hap⟩ := ulw_approx_data k hk2 θ hθ
  obtain ⟨Ccb, hCcb0, hcb⟩ := ulClosure_cb k 5 hk5 θ hθ
  obtain ⟨χ, hχ⟩ := ul0_exists_ulocCutoff d
  obtain ⟨Ce, hCe, hequ⟩ := ul_equiv k θ χ hθ hχ
  obtain ⟨Cemb, hemb⟩ := HRS.MS.UlocCb.uloc_embedding_cb_proof k j hkj χ hχ
  obtain ⟨Kg, hU⟩ := ulw_genHyp hd1 hs0 hsd M Q hQ c₀ hν.le hρ.2 T
  have hcoef := ulw_coeff_eq (s := s) (ν := ν) M Q hQ c₀ ρ
  set Cev' : ℝ := max Cev 0 with hCev'
  set Cemb' : ℝ := max Cemb 0 with hCemb'
  have hCev'0 : 0 ≤ Cev' := le_max_right _ _
  refine ⟨Cemb' * Ce * Cev' * Cap, ?_⟩
  intro r t hr hrt htT φ hφC hφfin
  have ht : t ∈ Set.Icc (0 : ℝ) T := ⟨hr.trans hrt, htT⟩
  have hφcont : Continuous φ := hφC.continuous
  set U : ℝ := (ulNormE k θ φ).toReal with hUdef
  have hUe : ulNormE k θ φ = ENNReal.ofReal U := (ENNReal.ofReal_toReal hφfin.ne).symm
  have hU0 : 0 ≤ U := ENNReal.toReal_nonneg
  obtain ⟨ψ, hψ, hψb, hψt⟩ := hap φ hφcont hφfin
  have hclos : ∀ n, UlClosure k θ (ψ n) := fun n =>
    ⟨contDiff_infty.1 (hψ n).1 2, fun ε hε =>
      ⟨ψ n, ⟨ψ n, 0, (hψ n).1, (hψ n).2, by funext x; simp⟩,
        by simp [ulNormE, HRS.MS.UlocCut.uc_zero]⟩⟩
  choose u hev hbd using fun n => hCev t ht (ψ n) (hclos n)
  set Z : ℝ := Cev' * Cap * U with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hnorm : ∀ n, ∀ r' ∈ Set.Icc (0 : ℝ) t, ulNormE k θ (u n r') ≤ ENNReal.ofReal Z := by
    intro n r' hr'
    calc ulNormE k θ (u n r') ≤ ENNReal.ofReal Cev * ulNormE k θ (ψ n) := hbd n r' hr'
      _ ≤ ENNReal.ofReal Cev' * (ENNReal.ofReal Cap * ulNormE k θ φ) := by
          gcongr
          · exact le_max_left _ _
          · exact hψb n
      _ = ENNReal.ofReal Z := by
          rw [hUe, ← ENNReal.ofReal_mul hCap0.le, ← ENNReal.ofReal_mul hCev'0]
          congr 1
          rw [hZ]; ring
  have hsl : ∀ n, ∀ r' ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 5 (u n r') ∧
      ∀ j' ≤ 5, ∀ y, ‖iteratedFDeriv ℝ j' (u n r') y‖ ≤ Ccb * Z := by
    intro n r' hr'
    obtain ⟨hmem, hcbn⟩ := hcb (u n r') ((hev n).mem r' hr')
    refine ⟨by exact_mod_cast hmem.1, fun j' hj' y => ?_⟩
    have h1 : ‖iteratedFDeriv ℝ j' (u n r') y‖ ≤ cbNorm 5 (u n r') := by
      have hb := hmem.2 j' hj'
      refine (le_ciSup hb y).trans ?_
      unfold cbNorm
      exact Finset.single_le_sum (f := fun i => ⨆ z, ‖iteratedFDeriv ℝ i (u n r') z‖)
        (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
    refine h1.trans (hcbn.trans ?_)
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hnorm n r' hr')
    rw [ENNReal.toReal_ofReal hZ0] at this
    exact mul_le_mul_of_nonneg_left this hCcb0.le
  have hclass : ∀ n, IsClassicalAdjointW
      ((⟨s, M, quadV Q c₀, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) t (ψ n) (u n) := fun n => by
    rw [hcoef]; exact (hev n).classicalSol
  obtain ⟨ns, hns, g, hgcl, hpt, hgb⟩ :=
    ulw_compact hU ht (B := Ccb * Z) (mul_nonneg hCcb0.le hZ0) hclass hsl hψt
  have hr' : r ∈ Set.Icc (0 : ℝ) t := ⟨hr, hrt⟩
  have hprop := ulw_unique hd hs0 hsd M Q hQ c₀ hν hρ.1 hρ.2 T ht hgcl r hr'
  have hM : ∀ i, ulocNormE k χ (u (ns i) r) ≤ ENNReal.ofReal (Ce * Z) := by
    intro i
    calc ulocNormE k χ (u (ns i) r) ≤ ENNReal.ofReal Ce * ulNormE k θ (u (ns i) r) := (hequ _).2
      _ ≤ ENNReal.ofReal Ce * ENNReal.ofReal Z := by
          gcongr
          exact hnorm _ r hr'
      _ = ENNReal.ofReal (Ce * Z) := (ENNReal.ofReal_mul hCe.le).symm
  have hBd : ∀ i x, |u (ns i) r x| ≤ Ccb * Z := by
    intro i x
    have := (hsl (ns i) r hr').2 0 (by norm_num) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hlsc := ulocNormE_lsc k χ hχ (fun i => u (ns i) r) (g r) (Ccb * Z) hBd (hpt r hr')
    (ENNReal.ofReal (Ce * Z)) hM
  have hfin : ulocNormE k χ (g r) < ⊤ := lt_of_le_of_lt hlsc ENNReal.ofReal_lt_top
  obtain ⟨v, hvae, hv, hvb⟩ := hemb (g r) hfin
  have hvg : v = g r :=
    (Continuous.ae_eq_iff_eq volume hv.1.continuous
      ((hgb r hr').1.continuous)).1 hvae
  subst hvg
  refine ⟨⟨g, hgcl⟩, ?_, ?_⟩
  · rw [hprop]; exact hv
  · rw [hprop]
    refine hvb.trans ?_
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlsc
    rw [ENNReal.toReal_ofReal (mul_nonneg hCe.le hZ0)] at h1
    have h2 : Cemb * (ulocNormE k χ (g r)).toReal ≤ Cemb' * (Ce * Z) :=
      calc Cemb * (ulocNormE k χ (g r)).toReal ≤ Cemb' * (ulocNormE k χ (g r)).toReal :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg
        _ ≤ Cemb' * (Ce * Z) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
    refine h2.trans (le_of_eq ?_)
    rw [hZ]; ring

end HRS.MS.S85
