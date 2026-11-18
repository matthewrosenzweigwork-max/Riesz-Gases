import HRS.MS.UniqE4g
import HRS.MS.UniqE1b

/-!
# E4 of `UniqPlan.md`, part 8: the nonlocal residue

For `ρ' = ρ(t-σ)`, `ψ' = ς z_ε`:
`|fpNonloc D ρ t σ u φ_σ - nMain D ρ' z_ε ψ'| ≤ C ε B²`, with `C` independent of `ε, σ, c, u, B`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE4

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3 HRS.MS.UniqE3 HRS.MS.UniqN0

variable {d : ℕ}

theorem e4_nonlocal_residue (hd : 1 ≤ d) {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (hcoef : CoeffHypRd D.s m Λ T ρ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) {Cb K : ℝ} {χ χh : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d}
    (hχ : IsUlocCutoff χ)
    (hF : FlowBundle d m Cb t χ χh (fun σ => meanFieldDriftW D (ρ (t - σ))) Ψ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Euc d → ℝ) (B : ℝ), 0 ≤ B → ulocNormE 1 χ u ≤ ENNReal.ofReal B →
      ∀ σ ∈ Icc (0 : ℝ) t, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ c : Euc d,
        |fpNonloc D ρ t σ u (phiTest d χ Ψ σ c ε u) -
            HRS.MS.UniqNDefs.nMain D (ρ (t - σ)) (moll d ε u)
              (fun x => varsigma χ Ψ σ c x * moll d ε u x)| ≤ C * ε * B ^ 2 := by
  set A : ℝ := HRS.MS.UniqC1.c1A d m Λ with hAdef
  have hA : 0 ≤ A := HRS.MS.UniqE1.e1_A_nonneg m Λ
  set R : ℝ := max 1 (2 * Real.exp (Cb * t)) with hRdef
  have hR : 1 ≤ R := le_max_left _ _
  obtain ⟨Kp, Qc, hKp, hQc, hPQ⟩ := e4_PQ d K R
  have hCi := fun i : Fin d => e4_comm_integral_bound (d := d) hs0 hsd i hR A hA
  choose Ci hCi0 hCi using hCi
  set X : ℝ := A ^ 2 + Qc + A * Kp with hX
  have hX0 : 0 ≤ X := by positivity
  set Cm : ℝ := ∑ i, Ci i with hCm
  have hCm0 : 0 ≤ Cm := Finset.sum_nonneg fun i _ => hCi0 i
  set Mabs : ℝ := ∑ i : Fin d, ∑ j : Fin d, |D.M j i| with hMabs
  have hMabs0 : 0 ≤ Mabs := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨Mabs * Cm * X, by positivity, ?_⟩
  intro u B hB hu σ hσ ε hε hε1 c
  obtain ⟨v, hv, -, hvj⟩ := weakGrad_of_ulocNormE hχ hB hu
  have hLM : LocMass B u := locMass_of_ulocNormE hχ hB hu
  have hσT : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  have hρ1 : ContDiff ℝ 1 (ρ (t - σ)) := HRS.MS.UniqE1.e1_rho_smooth hcoef hσT
  obtain ⟨hρ0, hρd⟩ := HRS.MS.UniqE1.e1_rho_decay01 hd hcoef hσT
  have ht0 : 0 ≤ t := ht.1
  set ς : Euc d → ℝ := varsigma χ Ψ σ c with hς
  set z : Euc d → ℝ := moll d ε u with hz
  have hς2 : ContDiff ℝ 2 ς := hF.contDiff σ hσ c
  have hς1 : ContDiff ℝ 1 ς := hς2.of_le (by norm_num)
  have hzs : ContDiff ℝ ∞ z := moll_contDiff hε hLM.locallyIntegrable
  have hz2 : ContDiff ℝ 2 z := by exact_mod_cast contDiff_infty.1 hzs 2
  have hψ2 : ContDiff ℝ 2 (fun y => ς y * z y) := hς2.mul hz2
  have hψc : HasCompactSupport (fun y => ς y * z y) :=
    (hF.compact_supp σ hσ c).mul_right
  have hRsub : closedBall (Ψ σ c) (2 * Real.exp (Cb * t)) ⊆ closedBall (Ψ σ c) R :=
    closedBall_subset_closedBall (le_max_right _ _)
  have hts : tsupport ς ⊆ closedBall (Ψ σ c) R := (hF.supp σ hσ c).trans hRsub
  obtain ⟨hP, hQ⟩ := hPQ hχ u B hB hu ε hε hε1 ς (Ψ σ c) hς1 (hF.fderiv_le σ hσ c)
    (fun x => (hF.range σ hσ c x).1) (fun x => (hF.range σ hσ c x).2) hts (hF.compact_supp σ hσ c)
  have hsuppψ : Function.support (fun y => ς y * z y) ⊆ closedBall (Ψ σ c) R := by
    intro y hy
    apply hts
    apply subset_tsupport
    intro h0
    exact hy (by simp [h0])
  have key : ∀ i j : Fin d,
      |(∫ x, u x * D1 j (fun y => ρ (t - σ) y * kernelConvDeriv d D.s i
          (moll d ε (fun y => ς y * z y)) y) x) -
        (∫ x, z x * D1 j (fun y => ρ (t - σ) y *
          kernelConvDeriv d D.s i (fun y => ς y * z y) y) x)| ≤ ε * (Ci i * (X * B ^ 2)) := by
    intro i j
    rw [e4_identity hs0 hsd hε i j hB hLM hv (hvj j) hρ1 hρ0 hρd hψ2 hψc, abs_neg]
    have hb := hCi i ε hε hε1 B hB (fun x => v x j) (hvj j) (ρ (t - σ)) hρ1 hρd (Ψ σ c)
      (fun y => ς y * z y) (Kp * B) (Qc * B ^ 2) (by positivity) (hψ2.of_le (by norm_num)) hψc
      hsuppψ (hQ i) hP
    refine hb.trans ?_
    refine le_of_eq ?_
    simp only [hX]
    ring
  rw [phiTest_eq_moll]
  unfold fpNonloc HRS.MS.UniqNDefs.nMain
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i : Fin d, |∑ j : Fin d, D.M j i *
        (∫ x, u x * fderiv ℝ (fun y => ρ (t - σ) y * kernelConvDeriv d D.s i
            (moll d ε fun x => ς x * z x) y) x (EuclideanSpace.single j (1 : ℝ))) -
      ∑ j : Fin d, D.M j i *
        (∫ x, z x * fderiv ℝ (fun y => ρ (t - σ) y * kernelConvDeriv d D.s i
            (fun x => ς x * z x) y) x (EuclideanSpace.single j (1 : ℝ)))| ≤
      (∑ j : Fin d, |D.M j i|) * (Cm * (ε * (X * B ^ 2))) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← mul_sub, abs_mul]
    have hk := key i j
    have hCle : Ci i ≤ Cm := Finset.single_le_sum (f := Ci) (fun i _ => hCi0 i) (Finset.mem_univ i)
    have hXB : 0 ≤ X * B ^ 2 := by positivity
    refine mul_le_mul_of_nonneg_left ((hk.trans ?_)) (abs_nonneg _)
    calc ε * (Ci i * (X * B ^ 2)) ≤ ε * (Cm * (X * B ^ 2)) := by gcongr
      _ = Cm * (ε * (X * B ^ 2)) := by ring
  refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
  rw [← Finset.sum_mul]
  refine le_of_eq ?_
  simp only [hMabs]
  ring

end HRS.MS.UniqE4
