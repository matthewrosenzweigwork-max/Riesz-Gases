import HRS.MS.S81pGauss
import HRS.MS.S81pPathLaw

/-!
# S8.1 (worker S81P), item (d), assembly: from three blocks to the burn-in coupling

Namespace `HRS.Whole.S81P`, prefix `s81p_`.

`s81p_assemble`: on a probability space `(Ω'', Q)` over `(Ω, P)` (measure preserving `π`) suppose the physical window path `Aw ∘ π` is
a.s. the sum `win I + win O + win R - win F` of four window paths (the Duhamel decomposition: initial, old current, recent current, forcing),
and that three jointly independent Gaussian blocks `G 0, G 1, G 2` (processes with Gaussian finite-dimensional laws, positive semidefinite
covariances adding up to the stationary profile `s81p_Qmat`) approximate `I, O, R` in `L²` up to `ε₀, ε₁, ε₂`, while `F` is `L²`-small
(`εF`).  Then, for EVERY frozen stationary Gaussian field `Z`, the window of `Z` and `Aw` are coupled on `Ω''` with
`L²` cost at most `ε₀ + ε₁ + ε₂ + εF`: exactly the shape of the conclusion of `S81W2Coupling`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.GenPath HRS.Whole.S81W2

namespace HRS.Whole.S81P

/-- The `L²(P)` size of a Banach-valued function, as an extended real. -/
def s81p_L2 {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] (P : Measure Ω) (f : Ω → E) : ℝ≥0∞ :=
  (∫⁻ ω, ENNReal.ofReal (‖f ω‖ ^ (2 : ℝ)) ∂P) ^ (1 / (2 : ℝ))

section L2

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] {P : Measure Ω}

theorem s81p_L2_eq (f : Ω → E) : s81p_L2 P f = (∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
  unfold s81p_L2
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), ofReal_norm_eq_enorm]

theorem s81p_L2_neg (f : Ω → E) : s81p_L2 P (fun ω => -f ω) = s81p_L2 P f := by
  simp [s81p_L2]

theorem s81p_L2_congr {f g : Ω → E} (h : f =ᵐ[P] g) : s81p_L2 P f = s81p_L2 P g := by
  unfold s81p_L2
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [h] with ω hω
  rw [hω]

theorem s81p_L2_add_le {f g : Ω → E} (hf : AEMeasurable (fun ω => ‖f ω‖ₑ) P)
    (hg : AEMeasurable (fun ω => ‖g ω‖ₑ) P) :
    s81p_L2 P (fun ω => f ω + g ω) ≤ s81p_L2 P f + s81p_L2 P g := by
  rw [s81p_L2_eq, s81p_L2_eq, s81p_L2_eq]
  refine le_trans ?_ (ENNReal.lintegral_Lp_add_le hf hg (by norm_num : (1 : ℝ) ≤ 2))
  refine ENNReal.rpow_le_rpow (lintegral_mono fun ω => ?_) (by norm_num)
  exact ENNReal.rpow_le_rpow (enorm_add_le _ _) (by norm_num)

end L2

section Win

variable {d : ℕ} {m T : ℝ}

theorem s81p_win_apply {f : ℝ → OscDual d m} (hf : ContinuousOn f (Icc 0 T)) (t : Icc (0 : ℝ) T) :
    OscPath.at' (windowPathOf m T 0 f) t = f t := by
  have hc0 : Continuous fun t : Icc (0 : ℝ) T => f (t : ℝ) := continuousOn_iff_continuous_restrict.1 hf
  have hc : Continuous fun t : Icc (0 : ℝ) T => f (0 + (t : ℝ)) := by simpa [zero_add] using hc0
  have e1 : windowPathOf m T 0 f =
      (⟨fun t => f (0 + t), hc⟩ : C(Icc (0 : ℝ) T, OscDual d m)) := by
    unfold windowPathOf; exact dif_pos hc
  rw [e1]
  simp [OscPath.at']

theorem s81p_win_ext {w w' : OscPath d m T} (h : ∀ t, OscPath.at' w t = OscPath.at' w' t) : w = w' :=
  ContinuousMap.ext h

theorem s81p_win_add {f g : ℝ → OscDual d m} (hf : ContinuousOn f (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T)) :
    windowPathOf m T 0 (fun t => f t + g t) = windowPathOf m T 0 f + windowPathOf m T 0 g := by
  refine s81p_win_ext fun t => ?_
  rw [s81p_win_apply (show ContinuousOn (fun t => f t + g t) (Icc 0 T) from hf.add hg), show OscPath.at' (windowPathOf m T 0 f + windowPathOf m T 0 g) t =
    OscPath.at' (windowPathOf m T 0 f) t + OscPath.at' (windowPathOf m T 0 g) t from rfl,
    s81p_win_apply hf, s81p_win_apply hg]

theorem s81p_win_sub {f g : ℝ → OscDual d m} (hf : ContinuousOn f (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T)) :
    windowPathOf m T 0 (fun t => f t - g t) = windowPathOf m T 0 f - windowPathOf m T 0 g := by
  refine s81p_win_ext fun t => ?_
  rw [s81p_win_apply (show ContinuousOn (fun t => f t - g t) (Icc 0 T) from hf.sub hg), show OscPath.at' (windowPathOf m T 0 f - windowPathOf m T 0 g) t =
    OscPath.at' (windowPathOf m T 0 f) t - OscPath.at' (windowPathOf m T 0 g) t from rfl,
    s81p_win_apply hf, s81p_win_apply hg]

/-- A process which is measurable at each time and a.s. continuous on `[0,T]`. -/
def S81PProc {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (T : ℝ) (Y : ℝ → Ω → OscDual d m) : Prop :=
  (∀ t, Measurable (Y t)) ∧ ∀ᵐ ζ ∂Q, ContinuousOn (fun t => Y t ζ) (Icc 0 T)

theorem S81PProc.aemeasurable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {Y : ℝ → Ω → OscDual d m}
    (hY : S81PProc Q T Y) (hT : 0 ≤ T) : AEMeasurable (processWindow m T 0 Y) Q := by
  have h := HRS.GF.gfb4_aemeasurable_windowPath Q hT Y (fun t _ => hY.1 t) hY.2
  rw [← HRS.MS.GenPath.s56_wpo_eq_windowPath] at h
  exact h

theorem S81PProc.add {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {Y Y' : ℝ → Ω → OscDual d m}
    (hY : S81PProc Q T Y) (hY' : S81PProc Q T Y') : S81PProc Q T (fun t ζ => Y t ζ + Y' t ζ) :=
  ⟨fun t => (hY.1 t).add (hY'.1 t), by
    filter_upwards [hY.2, hY'.2] with ζ h h'
    exact h.add h'⟩

theorem S81PProc.sub {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {Y Y' : ℝ → Ω → OscDual d m}
    (hY : S81PProc Q T Y) (hY' : S81PProc Q T Y') : S81PProc Q T (fun t ζ => Y t ζ - Y' t ζ) :=
  ⟨fun t => (hY.1 t).sub (hY'.1 t), by
    filter_upwards [hY.2, hY'.2] with ζ h h'
    exact h.sub h'⟩

end Win

section Assemble

variable {d : ℕ} {a β : ℝ} {ρ : Euc d → ℝ} {e : ℕ → Euc d → ℝ} {om : ℕ → ℝ} {m : ℝ}

/-- **Assembly of the burn-in coupling from three blocks.** -/
theorem s81p_assemble (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) (hm : (wholeSpaceIndex d : ℝ) ≤ m)
    (hdata : IsSpectralData d β ρ e om) (hcoef : S81W2Coef d a β ρ e om m) {T : ℝ} (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Ω'' : Type} [MeasurableSpace Ω''] (Q : Measure Ω'') [IsProbabilityMeasure Q]
    (π : Ω'' → Ω) (hπ : MeasurePreserving π Q P)
    (Aw : Ω → OscPath d m T) (hAw : AEMeasurable Aw P)
    (Ip Op Rp Fp : ℝ → Ω'' → OscDual d m) (G : Fin 3 → ℝ → Ω'' → OscDual d m)
    (hI : S81PProc Q T Ip) (hO : S81PProc Q T Op) (hR : S81PProc Q T Rp) (hF : S81PProc Q T Fp)
    (hG : ∀ i, S81PProc Q T (G i))
    (hduh : ∀ᵐ ζ ∂Q, Aw (π ζ) = processWindow m T 0 Ip ζ + processWindow m T 0 Op ζ +
      processWindow m T 0 Rp ζ - processWindow m T 0 Fp ζ)
    (hind : iIndepFun (fun (i : Fin 3) (ζ : Ω'') (t : ℝ) => G i t ζ) Q)
    (S : Fin 3 → ∀ (p : ℕ), (Fin p → ℝ) → (Fin p → MultiIndex d) → Matrix (Fin p) (Fin p) ℝ)
    (hpsd : ∀ i p ts αs, (∀ c, ts c ∈ Icc (0 : ℝ) T) → (S i p ts αs).PosSemidef)
    (hlaw : ∀ i p ts αs, (∀ c, ts c ∈ Icc (0 : ℝ) T) →
      Q.map (s81p_vec (G i) ts αs) = multivariateGaussian 0 (S i p ts αs))
    (hsum : ∀ p ts αs, (∀ c, ts c ∈ Icc (0 : ℝ) T) →
      S 0 p ts αs + S 1 p ts αs + S 2 p ts αs = s81p_Qmat d β ρ e om m ts αs)
    (ε₀ ε₁ ε₂ εF : ℝ≥0∞)
    (b₀ : s81p_L2 Q (fun ζ => processWindow m T 0 Ip ζ - processWindow m T 0 (G 0) ζ) ≤ ε₀)
    (b₁ : s81p_L2 Q (fun ζ => processWindow m T 0 Op ζ - processWindow m T 0 (G 1) ζ) ≤ ε₁)
    (b₂ : s81p_L2 Q (fun ζ => processWindow m T 0 Rp ζ - processWindow m T 0 (G 2) ζ) ≤ ε₂)
    (bF : s81p_L2 Q (fun ζ => processWindow m T 0 Fp ζ) ≤ εF)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → OscDual d m) (hZ : IsStationaryGaussianField d ((d : ℝ) / 2) a β m ρ P' Z) :
    ∃ A Gp : Ω'' → OscPath d m T, AEMeasurable A Q ∧ AEMeasurable Gp Q ∧
      Q.map A = law P Aw ∧ Q.map Gp = law P' (processWindow m T 0 Z) ∧
      s81p_L2 Q (fun ζ => A ζ - Gp ζ) ≤ ε₀ + ε₁ + ε₂ + εF := by
  classical
  set Gs : ℝ → Ω'' → OscDual d m := fun t ζ => G 0 t ζ + G 1 t ζ + G 2 t ζ with hGs
  have hGsP : S81PProc Q T Gs := ((hG 0).add (hG 1)).add (hG 2)
  have hwin : ∀ Y : ℝ → Ω'' → OscDual d m, S81PProc Q T Y → AEMeasurable (processWindow m T 0 Y) Q :=
    fun Y hY => hY.aemeasurable hT.le
  have hfdd : ∀ (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d), (∀ c, ts c ∈ Icc (0 : ℝ) T) →
      Q.map (s81p_vec Gs ts αs) = multivariateGaussian 0 (s81p_Qmat d β ρ e om m ts αs) := by
    intro p ts αs hts
    have := s81p_triple_fdd (T := T) Q G (fun i t => (hG i).1 t) hind S
      (fun p ts αs => s81p_Qmat d β ρ e om m ts αs) hpsd hlaw hsum ts αs hts
    exact this
  have hA : AEMeasurable (fun ζ => Aw (π ζ)) Q := hAw.comp_quasiMeasurePreserving hπ.quasiMeasurePreserving
  have hwI := hwin Ip hI
  have hwO := hwin Op hO
  have hwR := hwin Rp hR
  have hwF := hwin Fp hF
  have hw0 := hwin (G 0) (hG 0)
  have hw1 := hwin (G 1) (hG 1)
  have hw2 := hwin (G 2) (hG 2)
  refine ⟨fun ζ => Aw (π ζ), processWindow m T 0 Gs, hA, hwin Gs hGsP, ?_, ?_, ?_⟩
  · calc Q.map (fun ζ => Aw (π ζ)) = (Q.map π).map Aw :=
          (AEMeasurable.map_map_of_aemeasurable (by rw [hπ.map_eq]; exact hAw) hπ.aemeasurable).symm
      _ = law P Aw := by rw [hπ.map_eq]
  · exact s81p_window_law_of_profile hd ha hβ hρ hm hdata hcoef hT Q P' Z hZ Gs hGsP.1 hGsP.2 hfdd
  · have hsplit : (fun ζ => Aw (π ζ) - processWindow m T 0 Gs ζ) =ᵐ[Q] fun ζ =>
        (((processWindow m T 0 Ip ζ - processWindow m T 0 (G 0) ζ) +
          (processWindow m T 0 Op ζ - processWindow m T 0 (G 1) ζ)) +
          (processWindow m T 0 Rp ζ - processWindow m T 0 (G 2) ζ)) + -processWindow m T 0 Fp ζ := by
      filter_upwards [hduh, (hG 0).2, (hG 1).2, (hG 2).2] with ζ h h0 h1 h2
      have e1 : processWindow m T 0 Gs ζ = processWindow m T 0 (G 0) ζ + processWindow m T 0 (G 1) ζ +
          processWindow m T 0 (G 2) ζ := by
        unfold processWindow
        rw [hGs]
        simp only
        rw [s81p_win_add (f := fun t => G 0 t ζ + G 1 t ζ) (g := fun t => G 2 t ζ) (h0.add h1) h2,
          s81p_win_add h0 h1]
      rw [h, e1]
      abel
    rw [s81p_L2_congr hsplit]
    have hX0 : AEMeasurable (fun ζ => processWindow m T 0 Ip ζ - processWindow m T 0 (G 0) ζ) Q := hwI.sub hw0
    have hX1 : AEMeasurable (fun ζ => processWindow m T 0 Op ζ - processWindow m T 0 (G 1) ζ) Q := hwO.sub hw1
    have hX2 : AEMeasurable (fun ζ => processWindow m T 0 Rp ζ - processWindow m T 0 (G 2) ζ) Q := hwR.sub hw2
    have hF' : AEMeasurable (fun ζ => -processWindow m T 0 Fp ζ) Q := hwF.neg
    have s1 := s81p_L2_add_le (P := Q) (f := fun ζ => (processWindow m T 0 Ip ζ - processWindow m T 0 (G 0) ζ) +
        (processWindow m T 0 Op ζ - processWindow m T 0 (G 1) ζ) +
        (processWindow m T 0 Rp ζ - processWindow m T 0 (G 2) ζ)) (g := fun ζ => -processWindow m T 0 Fp ζ)
      ((hX0.add hX1).add hX2).enorm hF'.enorm
    have s2 := s81p_L2_add_le (P := Q) (f := fun ζ => (processWindow m T 0 Ip ζ - processWindow m T 0 (G 0) ζ) +
        (processWindow m T 0 Op ζ - processWindow m T 0 (G 1) ζ)) (g := fun ζ =>
        processWindow m T 0 Rp ζ - processWindow m T 0 (G 2) ζ) (hX0.add hX1).enorm hX2.enorm
    have s3 := s81p_L2_add_le (P := Q) (f := fun ζ => processWindow m T 0 Ip ζ - processWindow m T 0 (G 0) ζ)
      (g := fun ζ => processWindow m T 0 Op ζ - processWindow m T 0 (G 1) ζ) hX0.enorm hX1.enorm
    rw [s81p_L2_neg] at s1
    calc _ ≤ _ := s1
      _ ≤ (s81p_L2 Q (fun ζ => processWindow m T 0 Ip ζ - processWindow m T 0 (G 0) ζ) +
          s81p_L2 Q (fun ζ => processWindow m T 0 Op ζ - processWindow m T 0 (G 1) ζ) +
          s81p_L2 Q (fun ζ => processWindow m T 0 Rp ζ - processWindow m T 0 (G 2) ζ)) +
          s81p_L2 Q (fun ζ => processWindow m T 0 Fp ζ) := by
        gcongr
        exact s2.trans (by gcongr)
      _ ≤ ε₀ + ε₁ + ε₂ + εF := by gcongr

end Assemble

end HRS.Whole.S81P
