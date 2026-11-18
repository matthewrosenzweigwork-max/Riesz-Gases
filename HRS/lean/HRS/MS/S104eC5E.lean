import HRS.MS.S104eC5D

/-!
# S104E route C, packet C5 part E: the `VolHyp` instance and `c5_hex`

`C5PHyp`: the semigroup-side fields of `VolHyp` for `P = ouSg (ouQ d a) ν` (to be supplied by packet C1: `c1_ou_stab`, `c1_ou_hol_stab`, `c1_ou_gain`, `c1_ou_joint`, `c1_ou_strong`, ...).
`C5Ajc`: the field `A_jc` of `VolHyp` for `A v = s103bQ d s (ρ v)` (open: C2, or a `TC`-hypothesis version in C3; see S104E_C_changes.md).
`c5_volHyp`: `VolHyp d 2 η H (ouSg (ouQ d a) β⁻¹) (s103bQ d s (ρ ·))` for a resulting solution `ρ`, from `C5PHyp`, `C5Ajc` and the C2 theorems.
`c5_hex`: `S104eHex d s a β ρβ ε* c₁ C₁` (no smallness of `ε*`) from `C5PHyp` (all horizons) and `C5Ajc` (all resulting solutions).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.R2WinOrbNL HRS.MS.R2WinOrb HRS.MS.Ul HRS.MS.S104b

variable {d : ℕ}

/-- semigroup-side fields of `VolHyp` (all `j = 2` statements are kept general in `j`) -/
structure C5PHyp (d : ℕ) (a ν : ℝ) (j : ℕ) (η H : ℝ) where
  CP : ℝ
  CP1 : 1 ≤ CP
  P_stab : ∀ h : ℝ, 0 ≤ h → h ≤ H → ∀ (B : ℝ) (f : Euc d → ℝ), HolB j η B f →
    HolB j η (CP * B) (ouSg (ouQ d a) ν h f)
  P_gain : ∀ h : ℝ, 0 < h → h ≤ H → ∀ (B : ℝ) (f : Euc d → ℝ), Bd j B f →
    HolB j η (CP * (1 + h ^ (-((1 + η) / 2))) * B) (ouSg (ouQ d a) ν h f)
  P_cont : ∀ (B : ℝ) (f : Euc d → ℝ), HolB j η B f → ∀ i ≤ j + 1,
    ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (ouSg (ouQ d a) ν p.1 f) p.2) (Icc 0 H ×ˢ univ)
  P_jc : ∀ t ∈ Icc (0 : ℝ) H, ∀ (B : ℝ) (G : ℝ → Euc d → ℝ), (∀ v ∈ Icc 0 t, Bd j B (G v)) →
    (∀ i ≤ j, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2) (Icc 0 t ×ˢ univ)) →
    ∀ i ≤ j + 1, ContinuousOn
      (fun q : ℝ × ℝ × Euc d => iteratedFDeriv ℝ i (ouSg (ouQ d a) ν q.1 (G q.2.1)) q.2.2)
      (Ioc 0 H ×ˢ Icc 0 t ×ˢ univ)
  P_van : ∀ h : ℝ, 0 ≤ h → h ≤ H → ∀ (B : ℝ) (f : Euc d → ℝ), HolB j η B f → VanB (j + 1) f →
    VanB (j + 1) (ouSg (ouQ d a) ν h f)
  P_vgain : ∀ h : ℝ, 0 < h → h ≤ H → ∀ (B : ℝ) (f : Euc d → ℝ), Bd j B f → VanB j f →
    VanB (j + 1) (ouSg (ouQ d a) ν h f)
  P_strong : ∀ (B : ℝ) (f : Euc d → ℝ), HolB j η B f → VanB (j + 1) f → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ h ∈ Icc (0 : ℝ) H, ∀ h' ∈ Icc (0 : ℝ) H, |h - h'| < δ → ∀ i ≤ j + 1, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (ouSg (ouQ d a) ν h f) x - iteratedFDeriv ℝ i (ouSg (ouQ d a) ν h' f) x‖ ≤ ε

/-- the field `A_jc` of `VolHyp` for `A v = s103bQ d s (ρ v)` -/
def C5Ajc (d : ℕ) (s : ℝ) (j : ℕ) (η H : ℝ) (ρ : ℝ → Euc d → ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) H, ∀ (B : ℝ) (G : ℝ → Euc d → ℝ), (∀ v ∈ Icc 0 t, HolB j η B (G v)) →
    (∀ i ≤ j + 1, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2) (Icc 0 t ×ˢ univ)) →
    ∀ i ≤ j, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (s103bQ d s (ρ p.1) (G p.1)) p.2)
      (Icc 0 t ×ˢ univ)

theorem c5_P_lin (Q : Matrix (Fin d) (Fin d) ℝ) (ν h : ℝ) (c B B' : ℝ) {f g : Euc d → ℝ} (hf : Bd 0 B f)
    (hg : Bd 0 B' g) :
    ouSg Q ν h (fun x => c * f x + g x) = fun x => c * ouSg Q ν h f x + ouSg Q ν h g x := by
  have hfc : Continuous f := by simpa using hf.1.continuous
  have hgc : Continuous g := by simpa using hg.1.continuous
  have hfb : ∀ x, |f x| ≤ B := fun x => by
    have := hf.2 0 le_rfl x; rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hgb : ∀ x, |g x| ≤ B' := fun x => by
    have := hg.2 0 le_rfl x; rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hcb : ∀ x, |c * f x| ≤ |c| * B := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hfb x) (abs_nonneg _)
  funext x
  have := congrFun (c4_ouSg_add Q ν h (f := fun x => c * f x) (g := g) (continuous_const.mul hfc).measurable hgc.measurable hcb hgb) x
  rw [this]
  congr 1
  unfold ouSg
  exact integral_const_mul c _

theorem c5_volHyp (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (hβ : 0 < β) (εstar c₁ C₁ : ℝ)
    {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {ε : ℝ} {ψ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ}
    (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) (ha : 0 < a)
    {η : ℝ} (hη0 : max 0 (s - d + 1) < η) (hη1 : η < 1) {H : ℝ} (hH : 0 ≤ H)
    (hP' : Nonempty (C5PHyp d a β⁻¹ 2 η H)) (hAjc : C5Ajc d s 2 η H ρ) :
    Nonempty (VolHyp d 2 η H (ouSg (ouQ d a) β⁻¹) (fun v f => s103bQ d s (ρ v) f)) := by
  obtain ⟨hP⟩ := hP'
  set Lnat : ℕ := d + 2 + ⌈s⌉₊ + 5 with hLnat
  have hL : (d : ℝ) + ((2 : ℕ) : ℝ) + s + 4 < (Lnat : ℝ) := by
    have : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
    rw [hLnat]; push_cast; linarith
  have hdL : (d : ℝ) < (Lnat : ℝ) := by
    have : (0 : ℝ) ≤ ((2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨Aρ, hA0, hρU⟩ := c5_rho_unif hd hs0 hsd ha hβ εstar c₁ C₁ (2 + 3) Lnat (by omega) hρβ hres
  have hρ1 : ∀ v : ℝ, 0 ≤ v → U2Dec 1 (Lnat : ℝ) Aρ (ρ v) := fun v hv => u2dec_lower (by norm_num) (hρU v hv)
  have hρc := c5_rho_cont hd hs0 hsd ha hβ εstar c₁ C₁ (2 + 3) Lnat (by omega) hρβ hres
  set η' : ℝ := (max 0 (s - d + 1) + η) / 2 with hη'
  have hη'0 : max 0 (s - d + 1) < η' := by rw [hη']; linarith
  have hη'η : η' < η := by rw [hη']; linarith
  obtain ⟨Cb, hCb0, hCb⟩ := c2_Q_bd hd hs0 hsd 2 hη0 hη1 hL
  have hmem : ∀ v ∈ Icc (0 : ℝ) H, 0 ≤ v := fun v hv => hv.1
  refine ⟨
    { CP := hP.CP
      CA := Cb * (1 + Aρ)
      CP1 := hP.CP1
      CA0 := by positivity
      P_zero := fun f => by funext x; exact ouSg_zero (ouQ d a) (inv_pos.2 hβ).le f x
      P_lin := fun h _ c B B' f g hf hg => c5_P_lin _ _ h c B B' hf hg
      A_lin := fun v hv c B B' f g hf hg => c2_Q_lin (by omega) hs0 hsd hη0 hη1 hdL (hρ1 v (hmem v hv)) hf hg c
      P_stab := hP.P_stab
      P_gain := hP.P_gain
      A_bd := fun v hv B f hf => by
        have := hCb Aρ (ρ v) hA0 (hρU v (hmem v hv)) B f hf
        simpa [mul_assoc] using this
      P_cont := hP.P_cont
      P_jc := hP.P_jc
      A_jc := hAjc
      P_van := hP.P_van
      P_vgain := hP.P_vgain
      P_strong := hP.P_strong
      A_van := fun v hv B f hf hvan => c2_Q_van hd hs0 hsd 2 hη0 hη1 hL (hρU v (hmem v hv)) hf hvan
      A_tc := fun t ht B u hu hTC =>
        c5_Atc hd hs0 hsd ρ hη'0 hη'η hη1 hL (fun v hv => hρU v (hmem v hv)) hA0
          (fun e he => hρc H e he) ht hu hTC }⟩

theorem c5_hex (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ)
    {η : ℝ} (hη0 : max 0 (s - d + 1) < η) (hη1 : η < 1)
    (hP : ∀ H : ℝ, 0 ≤ H → Nonempty (C5PHyp d a β⁻¹ 2 η H))
    (hAjc : ∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      IsAdmissiblePerturbation ρβ εstar ε ψ → IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
      ∀ H : ℝ, 0 ≤ H → C5Ajc d s 2 η H ρ) :
    S104eHex d s a β ρβ εstar c₁ C₁ := by
  intro ε ψ ρ hadm hres α t ht
  have hηp : 0 < η := lt_of_le_of_lt (le_max_left _ _) hη0
  obtain ⟨hyp⟩ := c5_volHyp hd hs0 hsd hβ εstar c₁ C₁ hρβ hres ha hη0 hη1 (by linarith)
    (hP (t + 1) (by linarith)) (hAjc ε ψ ρ hadm hres (t + 1) (by linarith))
  exact c5_exists s a β ha hβ ρ hηp hη1 α ht hyp

end HRS.MS.S104e.C
