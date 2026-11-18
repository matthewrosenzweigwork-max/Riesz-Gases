import HRS.MC.E213U13h
import HRS.MC.E213U11j

/-!
# Packet e213u13, file i: the window process `Z_a` and the covariance field `J_a` lie in the first chaos
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U13

section Congr

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}
  {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem InFirstChaos.congr_ae {q : ℝ} {W W' : Ω → B} (h : W =ᵐ[P] W') (hW : InFirstChaos P ξ q W) :
    InFirstChaos P ξ q W' := by
  obtain ⟨hm, n, c, hlim⟩ := hW
  refine ⟨hm.congr h, n, c, hlim.congr fun m => ?_⟩
  refine lintegral_congr_ae ?_
  filter_upwards [h] with ω hω
  rw [hω]

theorem InSecondChaos.congr_ae {q : ℝ} {W W' : Ω → B} (h : W =ᵐ[P] W') (hW : InSecondChaos P ξ q W) :
    InSecondChaos P ξ q W' := by
  obtain ⟨hm, n, c, hlim⟩ := hW
  refine ⟨hm.congr h, n, c, hlim.congr fun m => ?_⟩
  refine lintegral_congr_ae ?_
  filter_upwards [h] with ω hω
  rw [hω]

end Congr

section GdChaos

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U11

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem gd_exists_xi :
    ∃ (ξ : ℕ → gd.Ω₀ → ℝ) (hm : ∀ i, Measurable (ξ i)) (hξ : IsStdGaussianSeq gd.P₀ ξ),
      ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
        InQ1 hξ hm (fun ω => NegSobolev.fourierCoeff (gd.η t ω) k) :=
  eta_exists_xi S β₀ (rLvl d) hE.β₀_nonneg gd.P₀ gd.η gd.limit

theorem gd_procWin_chaos {ξ : ℕ → gd.Ω₀ → ℝ} {hm : ∀ i, Measurable (ξ i)} {hξ : IsStdGaussianSeq gd.P₀ ξ}
    (hX : ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
      InQ1 hξ hm (fun ω => NegSobolev.fourierCoeff (gd.η t ω) k))
    (R : ℝ) (hR : 0 < R) (s : ℝ) (hs : 0 ≤ s) {q : ℝ} (hq : 2 ≤ q) :
    InFirstChaos gd.P₀ ξ q (procWin (rLvl d) R s gd.η) := by
  have hmom : ∀ q : ℝ, 1 ≤ q → AEStronglyMeasurable (procWin (rLvl d) R s gd.η) gd.P₀ ∧
      MemLp (procWin (rLvl d) R s gd.η) (ENNReal.ofReal q) gd.P₀ := by
    intro q hq
    obtain ⟨C, -, hC⟩ := u11_eta_moment gd R hR q hq
    obtain ⟨hmeas, hI, -⟩ := hC s hs
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    refine (integrable_norm_rpow_iff hmeas.aestronglyMeasurable (by simp; linarith)
      ENNReal.ofReal_ne_top).1 ?_
    rwa [ENNReal.toReal_ofReal (by linarith)]
  refine inFirstChaos_path hξ hm hR (hmom 1 le_rfl).1 (fun q hq => (hmom q hq).2) (fun t k => ?_) hq
  have hcont := u11_eta_cont gd (s + R)
  refine InQ1_congr ?_ (hX (s + t) (by linarith [t.2.1]) k)
  filter_upwards [hcont] with ω hω
  have hc : ContinuousOn (fun t => gd.η t ω) (Set.Icc s (s + R)) :=
    hω.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  rw [u11_procWin_at gd.η R s ω hc hR.le t]

theorem gd_Z_chaos {ξ : ℕ → gd.Ω₀ → ℝ} {hm : ∀ i, Measurable (ξ i)} {hξ : IsStdGaussianSeq gd.P₀ ξ}
    (hX : ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
      InQ1 hξ hm (fun ω => NegSobolev.fourierCoeff (gd.η t ω) k))
    (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {q : ℝ} (hq : 2 ≤ q) :
    InFirstChaos gd.P₀ ξ q (gd.Zwin T a) :=
  InFirstChaos.clm (HRS.MD.EQInterp.epath (rLvl_le hE) T) (by linarith) (gd_procWin_chaos gd hX T hT a ha hq)

theorem gd_Z_gaussian {ξ : ℕ → gd.Ω₀ → ℝ} {hm : ∀ i, Measurable (ξ i)} {hξ : IsStdGaussianSeq gd.P₀ ξ}
    (hX : ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
      InQ1 hξ hm (fun ω => NegSobolev.fourierCoeff (gd.η t ω) k))
    (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) :
    IsCenteredGaussian (law gd.P₀ (gd.Zwin T a)) :=
  law_gaussian_of_inFirstChaos hξ hm (gd_Z_chaos gd hX T hT a ha le_rfl)

theorem gd_J_chaos {ξ : ℕ → gd.Ω₀ → ℝ} {hm : ∀ i, Measurable (ξ i)} {hξ : IsStdGaussianSeq gd.P₀ ξ}
    (hX : ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
      InQ1 hξ hm (fun ω => NegSobolev.fourierCoeff (gd.η t ω) k))
    (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {q : ℝ} (hq : 2 ≤ q) :
    InFirstChaos gd.P₀ ξ q (gd.JwinP T a) := by
  have hL0 : (0 : ℝ) ≤ a + T + 1 := by linarith
  obtain ⟨Λ, hΛ⟩ := u11_exists_Lambda (S := S) (β₀ := β₀) hE T hT a ha hL0 (by linarith)
  have hmem : ∀ w, Λ w ∈ projTensor (PathSpace d m T) 2 := fun w => by
    rw [hΛ]; exact u11_winJ_cp_mem hE T hT a ha hL0 w
  let Λ' := Λ.codRestrict (projTensor (PathSpace d m T) 2) hmem
  have heq := u11_Jwin_eq gd T hT a ha Λ hΛ
  have hch := InFirstChaos.clm Λ' (by linarith)
    (gd_procWin_chaos gd hX (a + T + 1) (by linarith) 0 le_rfl hq)
  refine InFirstChaos.congr_ae ?_ hch
  filter_upwards [heq] with ω h
  unfold GaussData.JwinP
  rw [dif_pos (h ▸ hmem _)]
  exact Subtype.ext h.symm

end GdChaos

end HRS.MC.E213U13
