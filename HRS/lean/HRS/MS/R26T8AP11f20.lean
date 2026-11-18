import HRS.MS.R26T8AP11f19

/-!
# S8.2 T8A P11f (part 20): the smooth model `D̃ = PF - chi(x-y) PC + (1-chi(x-y)) T2` and its joint jets
`PF = ∫ |w|^(-s) θ1(x-w-y) Stil(x-w,y) dw`, `PC` the same with `θ2 = θ1 chi`, `T2 = ∫ Kc(x-y-v) ψ0(v) Stil(y+v,y) dv`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

/-- potential of the cut-off source `θ(u-y) Stil(u,y)`. -/
def r26t8a_f20_Pot (θ : Euc d → ℝ) (s : ℝ) (ρ : Euc d → ℝ) (Q : Euc d → Euc d → ℝ) (p : Euc d × Euc d) : ℝ :=
  ∫ w, ‖w‖ ^ (-s) * (θ (p.1 - w - p.2) * r26t8a_Stil ρ Q (p.1 - w) p.2)

/-- the three cutoffs -/
def r26t8a_f20_psi (chi : Euc d → ℝ) (v : Euc d) : ℝ := chi ((4 : ℝ) • v)
def r26t8a_f20_th1 (chi : Euc d → ℝ) (v : Euc d) : ℝ := 1 - chi ((4 : ℝ) • v)
def r26t8a_f20_th2 (chi : Euc d → ℝ) (v : Euc d) : ℝ := (1 - chi ((4 : ℝ) • v)) * chi v

/-- the model -/
def r26t8a_f20_model (chi : Euc d → ℝ) (s alpha : ℝ) (ρ : Euc d → ℝ) (Q : Euc d → Euc d → ℝ)
    (p : Euc d × Euc d) : ℝ :=
  (r26t8a_f20_Pot (r26t8a_f20_th1 chi) s ρ Q p -
      chi (p.1 - p.2) * r26t8a_f20_Pot (r26t8a_f20_th2 chi) s ρ Q p) +
    (1 - chi (p.1 - p.2)) * ∫ v, r26t8a_f5_G (r26t8a_Kc alpha chi (1 / 2 : ℝ)) (r26t8a_f20_psi chi)
      (fun v y => r26t8a_Stil ρ Q (y + v) y) v p

theorem r26t8a_f20_cutoffs {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k : ℕ) :
    ContDiff ℝ ∞ (r26t8a_f20_psi chi) ∧ ContDiff ℝ ∞ (r26t8a_f20_th1 chi) ∧ ContDiff ℝ ∞ (r26t8a_f20_th2 chi) ∧
    (∀ v, |r26t8a_f20_psi chi v| ≤ 1) ∧ (∀ v : Euc d, 1 / 2 < ‖v‖ → r26t8a_f20_psi chi v = 0) ∧
    (∀ v : Euc d, ‖v‖ ≤ 1 / 4 → r26t8a_f20_th1 chi v = 0) ∧
    (∀ v : Euc d, ‖v‖ ≤ 1 / 4 → r26t8a_f20_th2 chi v = 0) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ k, ∀ v : Euc d, ‖iteratedFDeriv ℝ j (r26t8a_f20_th1 chi) v‖ ≤ C) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ k, ∀ v : Euc d, ‖iteratedFDeriv ℝ j (r26t8a_f20_th2 chi) v‖ ≤ C) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ k, ∀ v : Euc d, ‖iteratedFDeriv ℝ j chi v‖ ≤ C) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ k, ∀ v : Euc d, ‖iteratedFDeriv ℝ j (fun v => 1 - chi v) v‖ ≤ C) := by
  have hc4 : ContDiff ℝ ∞ (fun v : Euc d => chi ((4 : ℝ) • v)) := hchi.1.comp (contDiff_const_smul _)
  have hψ : ContDiff ℝ ∞ (r26t8a_f20_psi chi) := hc4
  have hθ1 : ContDiff ℝ ∞ (r26t8a_f20_th1 chi) := contDiff_const.sub hc4
  have hθ2 : ContDiff ℝ ∞ (r26t8a_f20_th2 chi) := (contDiff_const.sub hc4).mul hchi.1
  have h4 : ∀ v : Euc d, ‖v‖ ≤ 1 / 4 → chi ((4 : ℝ) • v) = 1 := fun v hv =>
    hchi.2.2.2.1 _ (by rw [norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith)
  have h4' : ∀ v : Euc d, 1 / 2 ≤ ‖v‖ → chi ((4 : ℝ) • v) = 0 := fun v hv =>
    hchi.2.2.2.2 _ (by rw [norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith)
  refine ⟨hψ, hθ1, hθ2, fun v => ?_, fun v hv => h4' v hv.le, fun v hv => ?_, fun v hv => ?_, ?_, ?_, ?_, ?_⟩
  · have := hchi.2.2.1 ((4 : ℝ) • v)
    rw [abs_le]; constructor <;> simp only [r26t8a_f20_psi] <;> linarith [this.1, this.2]
  · simp only [r26t8a_f20_th1, h4 v hv]; norm_num
  · simp only [r26t8a_f20_th2, h4 v hv]; norm_num
  · exact r26t8a_f19_bdd_jets hθ1 (c := 1) (R := 1 / 2) (fun v hv => by simp only [r26t8a_f20_th1, h4' v hv]; norm_num) k
  · exact r26t8a_f19_bdd_jets hθ2 (c := 0) (R := 2) (fun v hv => by
      simp only [r26t8a_f20_th2, hchi.2.2.2.2 v hv]; ring) k
  · exact r26t8a_f19_bdd_jets hchi.1 (c := 0) (R := 2) (fun v hv => hchi.2.2.2.2 v hv) k
  · exact r26t8a_f19_bdd_jets (contDiff_const.sub hchi.1) (c := 1) (R := 2) (fun v hv => by
      simp only [hchi.2.2.2.2 v hv]; norm_num) k

end HRS.MS.R26T8A
