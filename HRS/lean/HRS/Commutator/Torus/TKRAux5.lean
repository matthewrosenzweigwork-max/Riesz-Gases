import HRS.Commutator.Torus.TKRAux4

/-!
# T-KR helpers, part 5: Fourier coefficients of `∇g_{>}` and of `(e_j - 1)^M ∇g_{>}`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s η : ℝ}

lemma tkr_integral_trig {n : ℕ} {c : Lattice d → ℂ} (hc : HRS.PDE.IsTrigPoly n c) (k : Lattice d) :
    ∫ x : Torus d, Torus.mode (-k) x * HRS.PDE.Kern.trig c x = c k := by
  classical
  have hpt : ∀ x : Torus d, Torus.mode (-k) x * HRS.PDE.Kern.trig c x =
      ∑ l ∈ HRS.PDE.Kern.boxF d n, c l * (Torus.mode (-k) x * Torus.mode l x) := by
    intro x
    rw [HRS.PDE.Kern.trig_eq_sum hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun l _ => (Torus.integrable_mode_mul _ _).const_mul _)]
  simp_rw [integral_const_mul, Torus.integral_mode_mul]
  have : ∀ l : Lattice d, (c l * (if -k + l = 0 then (1 : ℂ) else 0)) = if l = k then c l else 0 := by
    intro l
    have h : (-k + l = 0) ↔ (l = k) := by
      constructor
      · intro h; exact (neg_add_eq_zero.1 h).symm
      · intro h; rw [h]; simp
    simp only [h]
    split_ifs <;> simp
  simp_rw [this]
  rw [Finset.sum_ite_eq' (HRS.PDE.Kern.boxF d n) k c]
  split_ifs with hk
  · rfl
  · by_contra hne
    exact hk (HRS.PDE.Kern.mem_boxF.2 (hc k (Ne.symm (Ne.symm (fun h => hne h.symm)))))

lemma tkr_ghi_eq (x : Torus d) (i : Fin d) :
    ((ghiForceT s η x i : ℝ) : ℂ) = ((periodicRieszGrad d s x i : ℝ) : ℂ) -
      ((PleqT η (periodicRieszGrad d s) x i : ℝ) : ℂ) := by
  unfold ghiForceT gloForceT
  simp [PiLp.sub_apply]

lemma tkr_glo_continuous (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd1 : s + 1 < d) (hη : 0 < η) (i : Fin d) :
    Continuous fun x : Torus d => PleqT η (periodicRieszGrad d s) x i := by
  have hT2 : HRS.PDE.IsTrigPoly ⌈2 / η⌉₊ (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) :=
    tkr_isTrigPoly hη (fun k hk => by
      intro h0; apply hk; simp [h0])
  have hc : Continuous fun x : Torus d => HRS.PDE.Kern.trig
      (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) x := by
    have : (fun x : Torus d => HRS.PDE.Kern.trig
        (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) x) =
        fun x => ∑ k ∈ HRS.PDE.Kern.boxF d ⌈2 / η⌉₊, ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k *
          Torus.mode k x := funext fun x => HRS.PDE.Kern.trig_eq_sum hT2 x
    rw [this]
    exact continuous_finset_sum _ fun k _ => continuous_const.mul (Torus.continuous_mode k)
  have h2 : (fun x : Torus d => PleqT η (periodicRieszGrad d s) x i) =
      fun x => (HRS.PDE.Kern.trig
        (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) x).re := by
    funext x
    rw [← tkr_glo hd hs0 hsd1 hη x i]
    simp
  rw [h2]
  exact Complex.continuous_re.comp hc

lemma tkr_ghi_integrable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd1 : s + 1 < d) (hη : 0 < η) (i : Fin d) :
    Integrable fun x : Torus d => ((ghiForceT s η x i : ℝ) : ℂ) := by
  have h1 : Integrable fun x : Torus d => ((periodicRieszGrad d s x i : ℝ) : ℂ) :=
    (tkr_Gi_integrable hd hs0 hsd1 i).ofReal
  have h2 : Integrable fun x : Torus d => ((PleqT η (periodicRieszGrad d s) x i : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.comp (tkr_glo_continuous hd hs0 hsd1 hη i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have := h1.sub h2
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  rw [tkr_ghi_eq]

/-- Fourier coefficient of the `i`-th component of `∇g_{>}`. -/
lemma tkr_ghi_coef (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd1 : s + 1 < d) (hη : 0 < η) (i : Fin d)
    (k : Lattice d) :
    ∫ x : Torus d, Torus.mode (-k) x * ((ghiForceT s η x i : ℝ) : ℂ) =
      (1 - ((tkrChi η k : ℝ) : ℂ)) * tkrCI d s i k := by
  have hT2 : HRS.PDE.IsTrigPoly ⌈2 / η⌉₊ (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) :=
    tkr_isTrigPoly hη (fun k hk => by
      intro h0; apply hk; simp [h0])
  have hint2 : Integrable fun y : Torus d => Torus.mode (-k) y *
      ((periodicRieszGrad d s y i : ℝ) : ℂ) := by
    have h1 : Integrable (fun y : Torus d => ((periodicRieszGrad d s y i : ℝ) : ℂ)) :=
      (tkr_Gi_integrable hd hs0 hsd1 i).ofReal
    refine h1.bdd_mul (c := 1) ?_ ?_
    · exact (Torus.continuous_mode _).aestronglyMeasurable
    · exact Eventually.of_forall fun y => by rw [Torus.norm_mode]
  have hint3 : Integrable fun y : Torus d => Torus.mode (-k) y *
      HRS.PDE.Kern.trig (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) y := by
    have hc : Continuous fun x : Torus d => Torus.mode (-k) x * HRS.PDE.Kern.trig
        (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) x := by
      simp only [HRS.PDE.Kern.trig_eq_sum hT2]
      exact (Torus.continuous_mode _).mul
        (continuous_finset_sum _ fun k _ => continuous_const.mul (Torus.continuous_mode k))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ x : Torus d, Torus.mode (-k) x * ((ghiForceT s η x i : ℝ) : ℂ) =
      Torus.mode (-k) x * ((periodicRieszGrad d s x i : ℝ) : ℂ) -
        Torus.mode (-k) x * HRS.PDE.Kern.trig
          (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) x := by
    intro x
    rw [tkr_ghi_eq, tkr_glo hd hs0 hsd1 hη x i]
    ring
  simp_rw [hpt]
  rw [integral_sub hint2 hint3, tkr_fcoef_G hd hs0 hsd1 k i, tkr_integral_trig hT2 k]
  unfold tkrCI
  ring

/-- Coefficients of `(e_j - 1)^M · ∇g_{>,i}` are iterated lattice differences. -/
lemma tkr_coef_mulJ_pow {F : Torus d → ℂ} (hF : Integrable F) (j : Fin d) (M : ℕ) (k : Lattice d) :
    ∫ x : Torus d, Torus.mode (-k) x * ((Torus.mode (HRS.PDE.Kern.eI j) x - 1) ^ M * F x) =
      HRS.PDE.Kern.Dls (List.replicate M j) (fun l => ∫ x : Torus d, Torus.mode (-l) x * F x) k := by
  induction M generalizing F k with
  | zero => simp [HRS.PDE.Kern.Dls]
  | succ M ih =>
    have hF' : Integrable fun x : Torus d => (Torus.mode (HRS.PDE.Kern.eI j) x - 1) * F x := by
      refine hF.bdd_mul (c := 2) ?_ ?_
      · exact ((Torus.continuous_mode _).sub continuous_const).aestronglyMeasurable
      · refine Eventually.of_forall fun x => ?_
        calc ‖Torus.mode (HRS.PDE.Kern.eI j) x - 1‖ ≤ ‖Torus.mode (HRS.PDE.Kern.eI j) x‖ + ‖(1 : ℂ)‖ :=
              norm_sub_le _ _
          _ = 2 := by rw [Torus.norm_mode]; norm_num
    have e1 : ∀ x : Torus d, (Torus.mode (HRS.PDE.Kern.eI j) x - 1) ^ (M + 1) * F x =
        (Torus.mode (HRS.PDE.Kern.eI j) x - 1) ^ M * ((Torus.mode (HRS.PDE.Kern.eI j) x - 1) * F x) := by
      intro x; ring
    simp_rw [e1]
    rw [ih hF', List.replicate_succ]
    simp only [HRS.PDE.Kern.Dls]
    congr 1
    funext l
    simp only [HRS.PDE.Kern.Dl]
    have h1 : ∀ x : Torus d, Torus.mode (-l) x * ((Torus.mode (HRS.PDE.Kern.eI j) x - 1) * F x) =
        Torus.mode (-(l - HRS.PDE.Kern.eI j)) x * F x - Torus.mode (-l) x * F x := by
      intro x
      have : Torus.mode (-(l - HRS.PDE.Kern.eI j)) x =
          Torus.mode (-l) x * Torus.mode (HRS.PDE.Kern.eI j) x := by
        rw [← Torus.mode_add]; congr 1; abel
      rw [this]; ring
    simp_rw [h1]
    have hi1 : Integrable fun x : Torus d => Torus.mode (-(l - HRS.PDE.Kern.eI j)) x * F x := by
      refine hF.bdd_mul (c := 1) ?_ ?_
      · exact (Torus.continuous_mode _).aestronglyMeasurable
      · exact Eventually.of_forall fun y => by rw [Torus.norm_mode]
    have hi2 : Integrable fun x : Torus d => Torus.mode (-l) x * F x := by
      refine hF.bdd_mul (c := 1) ?_ ?_
      · exact (Torus.continuous_mode _).aestronglyMeasurable
      · exact Eventually.of_forall fun y => by rw [Torus.norm_mode]
    exact integral_sub hi1 hi2

end HRS.Commutator.TorusNote
