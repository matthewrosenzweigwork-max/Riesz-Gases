import HRS.MS.S104eC1B
import HRS.MS.S104eC1F
import HRS.MS.S104eC1K
import HRS.MS.S104eC1L

/-!
# S104E route C, packet C1 (part M): all semigroup-side fields of the Picard hypothesis (`C5PHyp` / `VolHyp`)

`c1_P_fields`: for `a, ν > 0`, `0 < η < 1`, `j`, `H`, there is `CP ≥ 1` such that the nine statements below hold for
`P h = ouSg (ouQ d a) ν h`; they are literally the fields `P_stab, P_gain, P_cont, P_jc, P_van, P_vgain, P_strong`
of `C5PHyp` (`S104eC5E`) and of `VolHyp` (`S104eC3C`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ContDiff

namespace HRS.MS.S104e.C
open HRS HRS.Whole HRS.MS.R2WinOrbNL HRS.MS.Ul
variable {d : ℕ}

theorem c1_P_fields (a ν : ℝ) (ha : 0 < a) (hν : 0 < ν) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (j : ℕ) (H : ℝ) :
    ∃ CP : ℝ, 1 ≤ CP ∧
    (∀ h : ℝ, 0 ≤ h → h ≤ H → ∀ (B : ℝ) (f : Euc d → ℝ), HolB j η B f →
      HolB j η (CP * B) (ouSg (ouQ d a) ν h f)) ∧
    (∀ h : ℝ, 0 < h → h ≤ H → ∀ (B : ℝ) (f : Euc d → ℝ), Bd j B f →
      HolB j η (CP * (1 + h ^ (-((1 + η) / 2))) * B) (ouSg (ouQ d a) ν h f)) ∧
    (∀ (B : ℝ) (f : Euc d → ℝ), HolB j η B f → ∀ i ≤ j + 1,
      ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (ouSg (ouQ d a) ν p.1 f) p.2)
        (Icc 0 H ×ˢ univ)) ∧
    (∀ t ∈ Icc (0 : ℝ) H, ∀ (B : ℝ) (G : ℝ → Euc d → ℝ), (∀ v ∈ Icc 0 t, Bd j B (G v)) →
      (∀ i ≤ j, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2) (Icc 0 t ×ˢ univ)) →
      ∀ i ≤ j + 1, ContinuousOn
        (fun q : ℝ × ℝ × Euc d => iteratedFDeriv ℝ i (ouSg (ouQ d a) ν q.1 (G q.2.1)) q.2.2)
        (Ioc 0 H ×ˢ Icc 0 t ×ˢ univ)) ∧
    (∀ h : ℝ, 0 ≤ h → h ≤ H → ∀ (B : ℝ) (f : Euc d → ℝ), HolB j η B f → VanB (j + 1) f →
      VanB (j + 1) (ouSg (ouQ d a) ν h f)) ∧
    (∀ h : ℝ, 0 < h → h ≤ H → ∀ (B : ℝ) (f : Euc d → ℝ), Bd j B f → VanB j f →
      VanB (j + 1) (ouSg (ouQ d a) ν h f)) ∧
    (∀ (B : ℝ) (f : Euc d → ℝ), HolB j η B f → VanB (j + 1) f → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ h ∈ Icc (0 : ℝ) H, ∀ h' ∈ Icc (0 : ℝ) H, |h - h'| < δ → ∀ i ≤ j + 1, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ i (ouSg (ouQ d a) ν h f) x - iteratedFDeriv ℝ i (ouSg (ouQ d a) ν h' f) x‖ ≤ ε) := by
  obtain ⟨Cg, hCg0, hgain⟩ := c1_ou_gain (d := d) a ν ha hν hη0 hη1 j H
  refine ⟨max 1 Cg, le_max_left _ _, ?_, ?_, ?_, c1_P_jc a ν ha hν H, ?_, ?_, ?_⟩
  · intro h hh _ B f hf
    have := s104c1_hol_stab a ν ha hν hη0 j hh hf
    exact this.mono_B (by nlinarith [hf.1.nonneg, le_max_left 1 Cg]) hη0.le
  · intro h hh hH B f hf
    have := hgain h hh hH B f hf
    have hB := hf.nonneg
    have hp : 0 ≤ h ^ (-((1 + η) / 2)) := Real.rpow_nonneg hh.le _
    refine this.mono_B ?_ hη0.le
    have : Cg * (1 + h ^ (-((1 + η) / 2))) ≤ max 1 Cg * (1 + h ^ (-((1 + η) / 2))) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    exact mul_le_mul_of_nonneg_right this hB
  · intro B f hf i hi
    exact c1_ou_joint a ν ha hν (j + 1) H hf.1 i hi
  · intro h hh _ B f hf hv
    exact s104c1_vanB ha hν.le hf.1 hv hh
  · intro h hh _ B f hf hv
    exact s104c1_vgain ha hν hh hf hv
  · intro B f hf hv ε hε
    exact c1_P_strong a ν ha hν H hf.1 hv hε

end HRS.MS.S104e.C
