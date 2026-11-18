import HRS.MS.S21A_Real
import HRS.MS.S21A_Err
import HRS.MS.S104bNL8
import HRS.MS.WsPrepI7

/-!
# S21A packet 5: `S21PrepMetric` from the named inputs (S2.1 (ii), metric bounds)

`S21aInputs` lists the inputs that are not proved in this file; the list below records which repository theorem discharges each one (`S21A_Metric` does not import those theorems).  Under the inputs, `s21a_metric` proves, for every `c₁, C₁`, that there are `ε_* > 0`,
`C₀`, `C ≥ 0` with `S21PrepMetric d s a β β₀ T c₁ C₁ ε_* C₀ C`, and `s21a_hmain` is the hypothesis of `whole_space_prepared_of_metric`; so
`s21a_whole_space_prepared` is the frozen statement S2.1 (ii) conditional on `S21aInputs` only.

The inputs:
* `h103` : S10.3 `r2_window_orbits` (frozen statement, D2/ED14 form; open at S103C/S103C2);
* `hNL`  : the terminal-time regularity of the adjoint orbits of the oscillator tests along the resulting solutions, for small `ε_*`
           (`S104nAllOrb`); discharged unconditionally by `s104b_allOrb_of_termRegGen` (S104bOrb1) applied to `s104j_termReg s104e_hexSmall` (S104J_Assembly, S104eFinal);
* `hreg` : `S105nReg`, the `IsRegularMFRd` regularity of the resulting solutions (analytic consequence of the class bounds); discharged unconditionally by `s105r_reg` (S105rReg2);
* `hDiss`: `SuperDiss d s` (S.B.1), which feeds S6.6 at the low indices `(1, d/2+8)` (`s21p_package_of_diss`);
* `htilt` : `S21iTiltClass` for `β₀ > 0` and `ε_* ≤ 1/2` (the ψ-uniform S4.7; discharged by `s21u_tiltClass` of the S21U packet).

Facts about the interface (see the handoff): S6.6 and S10.4 each choose their own existential completion constant `C₀`; `s21a_errors_up` (S10.4 with
`C₀` upward closed) and `s21a_mpb_up` (S6.6 bounds at a larger `C₀`) make the two compatible.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21A

open HRS.Whole HRS.MS.R2WinErr HRS.MS.R2GenInit

/-- The named inputs of S2.1 (ii) (metric bounds). -/
structure S21aInputs : Prop where
  h103 : type_of% @HRS.Whole.r2_window_orbits
  hNL : ∀ (d : ℕ), 2 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < d → ∀ (a β c₁ C₁ : ℝ), 0 < a → 0 < β →
    ∃ εn : ℝ, 0 < εn ∧ ∀ εstar : ℝ, εstar ≤ εn → S104nAllOrb d s a β εstar c₁ C₁
  hreg : ∀ (d : ℕ), 2 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < d → ∀ (a β c₁ C₁ : ℝ), 0 < a → 0 < β →
    ∃ εn : ℝ, 0 < εn ∧ ∀ εstar : ℝ, εstar ≤ εn → HRS.MS.S104b.S105nReg d s a β εstar c₁ C₁
  hDiss : ∀ (d : ℕ), 2 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < d → HRS.MS.MfeConf.SuperDiss d s
  htilt : ∀ (d : ℕ), 2 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < d → ∀ (a β β₀ : ℝ), 0 < a → 0 < β → 0 < β₀ →
    ∀ εstar : ℝ, εstar ≤ 1 / 2 → HRS.MS.S21.S21iTiltClass d s a β β₀ (4 * d + 42) εstar

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem s21a_metric (hin : S21aInputs) (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β β₀ : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hβ₀ : 0 ≤ β₀) {T : ℝ} (hT : 0 < T) (c₁ C₁ : ℝ) :
    ∃ εstar : ℝ, 0 < εstar ∧ ∃ C₀ C : ℝ, 0 ≤ C ∧ S21PrepMetric d s a β β₀ T c₁ C₁ εstar C₀ C := by
  have hd1 : 1 ≤ d := by omega
  -- S10.3, the terminal-time regularity, the regularity, the particle package
  obtain ⟨ε₃, hε₃, Cs0, cdec, hcdec, hsum, hmain⟩ := hin.h103 hd s hs0 hsd a β ha hβ T hT c₁ C₁
  obtain ⟨εn, hεn, hNL'⟩ := hin.hNL d hd s hs0 hsd a β c₁ C₁ ha hβ
  obtain ⟨εr, hεr, hreg'⟩ := hin.hreg d hd s hs0 hsd a β c₁ C₁ ha hβ
  obtain ⟨ε₆, hε₆, C₀₆, CB₆, CT₆, hpkg⟩ := s21p_package_of_diss hd hs0 hsd ha hβ hβ₀ hT (hin.hDiss d hd s hs0 hsd) c₁ C₁
  set εstar : ℝ := min (min (min ε₃ εn) (min εr ε₆)) (1 / 2) with hεstar
  have hεpos : 0 < εstar := lt_min (lt_min (lt_min hε₃ hεn) (lt_min hεr hε₆)) (by norm_num)
  have hle3 : εstar ≤ ε₃ := ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hlen : εstar ≤ εn := ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hler : εstar ≤ εr := ((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hle6 : εstar ≤ ε₆ := ((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hlehalf : εstar ≤ 1 / 2 := min_le_right _ _
  have hNLε : S104nAllOrb d s a β εstar c₁ C₁ := hNL' εstar hlen
  have hregε := hreg' εstar hler
  -- the gradient orbit bounds of S10.3 for the class at `εstar`
  have hgrad : ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ρ : ℝ → Euc d → ℝ,
      IsR2WindowTrajectory d s a β ρβ εstar c₁ C₁ ρ → ∀ α : MultiIndex d,
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) (Cs0 * s104_b d α) cdec) ∧
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
        (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))
        (Cs0 * s104_b d α) cdec) := by
    intro ρβ hρβ ρ htraj α
    have hm' := hmain ρβ hρβ ρ (s104_traj_mono hd hs0 hsd ha hβ hρβ hle3 htraj) α
    dsimp only at hm'
    exact ⟨fun t ht => (hm'.1 t ht).2.1, fun t ht => (hm'.1 t ht).2.2.2.1⟩
  -- S10.4 with an upward closed completion constant
  obtain ⟨C₀s, herr⟩ := s21a_errors_up hd s hs0 hsd a β ha hβ T hT εstar c₁ C₁ hNLε Cs0 cdec hcdec hsum hgrad
  set C₀ : ℝ := max (max C₀s C₀₆) 1 with hC₀
  have hC₀s : C₀s ≤ C₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hC₀6 : C₀₆ ≤ C₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hC₀1 : 1 ≤ C₀ := le_max_right _ _
  set CB : ℝ := max (max ((|CB₆| + 1) * (|C₀₆| + 1)) CT₆) 0 with hCB
  have hCBa : (|CB₆| + 1) * (|C₀₆| + 1) ≤ CB := (le_max_left _ _).trans (le_max_left _ _)
  have hCBb : CT₆ ≤ CB := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨CT4, hCT4⟩ := (herr C₀ hC₀s).2 CB
  set K : ℝ := max CT4 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  have hKle : CT4 ≤ K := le_max_left _ _
  -- the orbit input and INIT
  have horb := s21a_orbClass hd hs0 hsd ha hβ hT hle3 (C := Cs0) (fun ρβ hρβ ρ htraj α => by
      have h := hmain ρβ hρβ ρ htraj α
      dsimp only at h
      exact h.2) hNLε
  obtain ⟨Cinit, hCi, hW⟩ := HRS.MS.S21.s21i_init hd hs0 hsd ha hβ hβ₀ hT horb
    (fun hpos => hin.htilt d hd s hs0 hsd a β β₀ ha hβ hpos εstar hlehalf)
  obtain ⟨Cs, Cw, hCs, hCw, hCmp⟩ := s105_win_compare (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T hT
  set C : ℝ := max (Cs * K + K + Cinit) (Cw * Real.sqrt K + K + Cinit) with hC
  have hC1 : Cs * K + K + Cinit ≤ C := le_max_left _ _
  have hC2 : Cw * Real.sqrt K + K + Cinit ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := le_trans (by positivity) hC1
  refine ⟨εstar, hεpos, C₀, C, hC0, ?_⟩
  intro ρβ hρβ ε ψ hadm ρ hres N hN hGEC Ω _ P _ X₀ W X hBr hInd hlaw hstrong Ω' _ P' _ Z hZ a₀ ha₀
  obtain ⟨hadm6, hres6⟩ := s21a_cls_mono hd hs0 hsd ha hβ hρβ hle6 hadm hres
  obtain ⟨X', hmod, hreal, hMov, hwinmom⟩ := hpkg ρβ hρβ ε ψ hadm6 ρ hres6 N hN hGEC P X₀ W X hBr hInd hlaw hstrong
  have htraj : IsR2WindowTrajectory d s a β ρβ εstar c₁ C₁ ρ := Or.inr ⟨ε, ψ, hadm, hres⟩
  have hMov' := s21a_mpb_up hN hs0 hC₀6 hC₀1 hCBa hMov
  have hwinmom' : ∀ b : ℝ, 0 ≤ b → ∫⁻ ζ, ⨆ t ∈ Set.Icc b (b + T),
      ENNReal.ofReal (movSecondMoment (X' t.toNNReal ζ)) ∂P ≤ ENNReal.ofReal CB :=
    fun b hb => (hwinmom b hb).trans (ENNReal.ofReal_le_ofReal hCBb)
  obtain ⟨hBt, hFb⟩ := hCT4 ρβ hρβ ρ htraj N hN P X₀ W X' hreal hMov' hwinmom' a₀ ha₀
  obtain ⟨M, L, Mom, C₀c, hC₀c, hcl⟩ := s104n_hcls hd hs0 hsd ha hβ εstar c₁ C₁
  obtain ⟨hρc, -, hjm⟩ := hcl ρβ hρβ ρ htraj
  have hS := HRS.MS.S104b.s104b_data hd hs0 hsd ha hβ hρβ hres
    (fun α T0 h0 => hNLε ρβ hρβ ε ψ ρ hadm hres α T0 h0) Cs0 cdec hcdec hsum (hgrad ρβ hρβ ρ htraj)
    (hregε ρβ hρβ ε ψ ρ hadm hres) hjm (hρc 0 le_rfl).2.2.1 hT ha₀
  have hδ : 0 ≤ HRS.deltaN d s N := HRS.MS.S53.s53_deltaN_nonneg s (by omega)
  have hw : 0 ≤ localizationRate d s C₀ N := HRS.MS.S21T2.s21t2_localizationRate_nonneg
  have hF : ENNReal.ofReal (CT4 * Real.sqrt N * HRS.deltaN d s N) ≤
      ENNReal.ofReal (K * (Real.sqrt N * HRS.deltaN d s N)) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hKle (mul_nonneg (Real.sqrt_nonneg _) hδ)
  have hWt : ENNReal.ofReal (CT4 * localizationRate d s C₀ N) ≤ ENNReal.ofReal (K * localizationRate d s C₀ N) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKle hw)
  exact s21a_window (K1 := K) (K2 := K) (Corb := max Cs0 0) (Cinit := Cinit) (C₀ := C₀) (Cs := Cs) (Cw := Cw)
    (C := C) (F := ENNReal.ofReal (CT4 * Real.sqrt N * HRS.deltaN d s N))
    (Wt := ENNReal.ofReal (CT4 * localizationRate d s C₀ N)) hd hs0 hsd ha hβ hT horb hW hCs hCw hK0 hK0 hCi hC0 hC1
    hC2 hCmp hρβ hadm hres hN ha₀ P X₀ W X hlaw (hstrong 0).cont X' hmod hreal hS hFb hBt hF hWt P' Z hZ

/-- The hypothesis of `whole_space_prepared_of_metric`, from the named inputs. -/
theorem s21a_hmain (hin : S21aInputs) :
    ∀ (d : ℕ), 2 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < 2 * (d : ℝ) / 3 → ∀ (a β : ℝ), 0 < a → 0 < β →
      ∀ β₀ : ℝ, 0 ≤ β₀ → ∀ T : ℝ, 0 < T → ∀ c₁ C₁ : ℝ,
      ∃ εstar : ℝ, 0 < εstar ∧ ∃ C₀ C : ℝ, 0 ≤ C ∧ S21PrepMetric d s a β β₀ T c₁ C₁ εstar C₀ C := by
  intro d hd s hs0 hs a β ha hβ β₀ hβ₀ T hT c₁ C₁
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  exact s21a_metric hin hd hs0 hsd ha hβ hβ₀ hT c₁ C₁

/-- **S2.1 (ii)** (`HRS.Whole.whole_space_prepared`) conditional on the named inputs `S21aInputs` only. -/
theorem s21a_whole_space_prepared (hin : S21aInputs) : HRS.Whole.WholeSpacePreparedStatement :=
  whole_space_prepared_of_metric (s21a_hmain hin)

end HRS.MS.S21A
