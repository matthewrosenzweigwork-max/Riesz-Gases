import HRS.MS.SuppU15Aux1
import HRS.MS.SuppU15Aux2
import HRS.MS.SuppU15Aux3
import HRS.Whole.Bias
import HRS.Whole.Window
import HRS.Whole.Adjoint

/-!
# U15: the conditional statement `sharp_all_sub_of_decay_and_tail` (packet N4, S4.14)

`sharp_all_sub` follows from `adjoint_decay` (S4.12) and `sharp_tail_bound` (S4.13 at `a = d+1`) and the proved
sub-Coulomb commutator estimate `whole_commutator_sub_sharp_of_subcoulomb`, with `Λ' = max Λ 1`, a log moment
from the weighted bound on `ρ_r`, and the conversion `oNΛ → oN`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SuppU15

open HRS.Whole

variable {d : ℕ} {s : ℝ}

theorem sharp_all_sub_of_decay_and_tail_proof (hd : 2 ≤ d) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) (s : ℝ)
    (M Q : Matrix (Fin d) (Fin d) ℝ) (c : Euc d) (T νstar : ℝ) (k : ℕ) (L Λ K : ℝ)
    (hs : s < (d : ℝ) - 2) (hk : ((d : ℝ) + 1) / 2 + 1 < k)
    (hAD : ∃ C : ℝ, ∀ (ν : ℝ) (ρ : ℝ → Euc d → ℝ), AdjointDecayHyp θ s M Q c T νstar k L Λ K ν ρ →
      ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ,
        ContDiff ℝ ((k + 2 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ →
        ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ < ⊤ →
        ContDiff ℝ k (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) r t φ) ∧
        decayNormE k (s + 1) (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) r t φ) ≤
          ENNReal.ofReal C * (decayNormE k (s + 1) φ +
            ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ))
    (hST : 0 ≤ s → ∃ C : ℝ, ∀ f : Euc d → ℝ, ContDiff ℝ k f → decayNormE k (s + 1) f < ⊤ →
      ∃ w : Fin d → Euc d → ℝ,
        (∀ i, IsFracDerivRep (((d : ℝ) + 1) / 2) (fun x => gradient f x i) (w i)) ∧
        (∀ i, MemLp (w i) (ENNReal.ofReal (2 * d / (((d : ℝ) + 1) - 2))) volume) ∧
        (⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) +
          ∑ i, eLpNorm (w i) (ENNReal.ofReal (2 * d / (((d : ℝ) + 1) - 2))) volume ≤
            ENNReal.ofReal C * decayNormE k (s + 1) f) :
    ∃ C₀ C : ℝ, ∀ (ν : ℝ) (ρ : ℝ → Euc d → ℝ), AdjointDecayHyp θ s M Q c T νstar k L Λ K ν ρ →
      ∀ (N : ℕ), 2 ≤ N → ∀ X : EucConfig d N, Function.Injective X →
      ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ,
        ContDiff ℝ ((k + 2 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ →
        decayNormE k (s + 1) φ < ⊤ → ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ < ⊤ →
        |commN d s (fun x => Torus.matVec M.transpose
              (gradient (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) r t φ) x))
            X (HRS.Whole.withDensityReal (ρ r))| ≤
          C * ((decayNormE k (s + 1) φ).toReal +
              (ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ).toReal) *
            (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (ρ r)) + oN d s C₀ N) := by
  by_cases hs0 : 0 ≤ s
  swap
  · exact ⟨0, 0, fun ν ρ hyp => absurd hyp.s_range.1 hs0⟩
  by_cases hL : (d : ℝ) + 1 < L
  swap
  · refine ⟨0, 0, fun ν ρ hyp => ?_⟩
    exfalso; apply hL
    have h1 := hyp.L_range
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  obtain ⟨CAD, hAD'⟩ := hAD
  obtain ⟨CST, hST'⟩ := hST hs0
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hk2 : 2 ≤ k := by
    have h1 : (2 : ℝ) < k := by linarith
    have h2 : (2 : ℕ) < k := by exact_mod_cast h1
    omega
  obtain ⟨Lm, hLm⟩ := u15_logmoment hL Λ
  have ha : (d : ℝ) < (d : ℝ) + 1 ∧ (d : ℝ) + 1 < (d : ℝ) + 2 := ⟨by linarith, by linarith⟩
  obtain ⟨C₀', Csub, hC₀', hCsub, H⟩ :=
    HRS.Commutator.Whole.whole_commutator_sub_sharp_of_subcoulomb hs0 hs ((d : ℝ) + 1) ha Lm
  have hcM0 : 0 ≤ u15_cM M.transpose := u15_cM_nonneg _
  refine ⟨C₀' * (max Λ 1) ^ (s / d) + Real.log (max Λ 1) / (2 * d),
    Csub * (u15_cM M.transpose * max CST 0 * max CAD 0), ?_⟩
  intro ν ρ hyp N hN X hX r t hr hrt htT φ hφ hdec hul
  obtain ⟨hcd, hdecf⟩ := hAD' ν ρ hyp r t hr hrt htT φ hφ hul
  set f := propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) r t φ with hf
  have hdecf' : decayNormE k (s + 1) f < ⊤ :=
    lt_of_le_of_lt hdecf (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hdec, hul⟩))
  obtain ⟨w, hw1, hw2, hw3⟩ := hST' f hcd hdecf'
  have hSne : ((⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) +
      ∑ i, eLpNorm (w i) (ENNReal.ofReal (2 * d / (((d : ℝ) + 1) - 2))) volume) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdecf'.ne) hw3
  have hp : 1 ≤ 2 * (d : ℝ) / (((d : ℝ) + 1) - 2) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hf2 : ContDiff ℝ 2 f := hcd.of_le (by exact_mod_cast hk2)
  have hTr := u15_transport M.transpose hp hf2 hw1 hw2 hSne
  -- the numeric bound on the constant
  have hSle : ((⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) +
      ∑ i, eLpNorm (w i) (ENNReal.ofReal (2 * d / (((d : ℝ) + 1) - 2))) volume).toReal ≤
      max CST 0 * (decayNormE k (s + 1) f).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdecf'.ne) hw3
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at this
  have hdle : (decayNormE k (s + 1) f).toReal ≤
      max CAD 0 * ((decayNormE k (s + 1) φ).toReal +
        (ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ).toReal) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨hdec.ne, hul.ne⟩)) hdecf
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_add hdec.ne hul.ne] at this
  set S' := (decayNormE k (s + 1) φ).toReal + (ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ).toReal with hS'
  have hS'0 : 0 ≤ S' := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hKle : u15_cM M.transpose * ((⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) +
      ∑ i, eLpNorm (w i) (ENNReal.ofReal (2 * d / (((d : ℝ) + 1) - 2))) volume).toReal ≤
      u15_cM M.transpose * max CST 0 * max CAD 0 * S' := by
    calc _ ≤ u15_cM M.transpose * (max CST 0 * (max CAD 0 * S')) :=
          mul_le_mul_of_nonneg_left (hSle.trans (mul_le_mul_of_nonneg_left hdle (le_max_right _ _))) hcM0
      _ = _ := by ring
  have hv := u15_hasFrac_mono hTr hKle
  -- the density
  obtain ⟨hprob, -, hwt⟩ := hyp.density r ⟨hr, hrt.trans htT⟩
  have hL0 : (0 : ℝ) ≤ L := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hb0 : ∀ x, jbracket x ^ L * |ρ r x| ≤ max Λ 0 := u15_weighted_zero hwt
  have hρle : ∀ x, ρ r x ≤ max Λ 1 := fun x =>
    (u15_dens_le hL0 hprob.nonneg hb0 x).trans (max_le_max le_rfl zero_le_one)
  have hlog : s = 0 → HRS.Whole.HasLogMoment (HRS.Whole.withDensityReal (ρ r)) Lm :=
    fun _ => hLm (ρ r) hprob hb0
  obtain ⟨-, hb⟩ := H (max Λ 1) (le_max_right _ _) N hN (ρ r) hprob hρle hlog X hX _ _ hv
  have hd1 : 1 ≤ d := by omega
  have hoN := u15_oNΛ_le hd1 hs0 C₀' (max Λ 1) (le_max_right _ _) (N := N) (by omega)
  have hnn : 0 ≤ Csub * (u15_cM M.transpose * max CST 0 * max CAD 0 * S') :=
    mul_nonneg hCsub.le (mul_nonneg (mul_nonneg (mul_nonneg hcM0 (le_max_right _ _)) (le_max_right _ _)) hS'0)
  calc _ ≤ _ := hb
    _ ≤ Csub * (u15_cM M.transpose * max CST 0 * max CAD 0 * S') *
          (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (ρ r)) +
            oN d s (C₀' * (max Λ 1) ^ (s / d) + Real.log (max Λ 1) / (2 * d)) N) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hoN _) hnn
    _ = _ := by ring

end HRS.MS.SuppU15
