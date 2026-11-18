import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.Energy
import HRS.Commutator.Whole.Local
import HRS.Commutator.Whole.ProductEstimate
import HRS.Commutator.Whole.INHOMAux1
import HRS.Commutator.Whole.UHIGHAux1

/-!
# Packet CMX-HIGH auxiliary 2: bounds on `u = ∇g_{≤1} * ν` and the background term

`uhigh_u_main`: for `σ = ν` with `‖P_{≤4}σ‖²_{Ḣ^{-α}} ≤ T`: `u` is continuous, band-limited, in `L^{p₂}` with
`‖u‖_{p₂} ≲ T^{1/2}` (`(3.potentialSobolev)`) and `(∑_j sup_{Q_j}|u|^{p₂})^{1/p₂} ≲ T^{1/2}` (`(3.usample)`).
`uhigh_background_main` is `(5.backgroundclosing)`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole.UHIGH

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

theorem uhigh_sqrt_mul_sqrt (X : ℝ≥0∞) : X ^ ((1 : ℝ) / 2) * X ^ ((1 : ℝ) / 2) = X := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

theorem uhigh_u_main (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ Cps Cu : ℝ, 0 < Cps ∧ 0 < Cu ∧ ∀ σ : SMeas d, σ.IsFinite → σ.CompactSupp →
      (s = 0 → σ.mass = 0) → ∀ T : ℝ≥0∞, T ≠ ⊤ →
      homSqE (-alphaE d s) (lowFreq 4 σ.fourier) ≤ T →
        Continuous (fun x => σ.convForce (gloForce s) x) ∧
        (∀ i, FourierSuppIn 2 (fun x => σ.convForce (gloForce s) x i)) ∧
        MemLp (fun x => ‖σ.convForce (gloForce s) x‖) (ENNReal.ofReal (p2E d s)) volume ∧
        eLpNorm (fun x => ‖σ.convForce (gloForce s) x‖) (ENNReal.ofReal (p2E d s)) volume ≤
          ENNReal.ofReal Cps * T ^ ((1 : ℝ) / 2) ∧
        cubeSupNorm (p2E d s) (fun x => σ.convForce (gloForce s) x) ≤
          ENNReal.ofReal Cu * (ENNReal.ofReal Cps * T ^ ((1 : ℝ) / 2)) := by
  obtain ⟨Cps, hCps, hps⟩ := potentialSobolev hd hs0 hsd
  obtain ⟨Cu, hCu, hus⟩ := usample hd hs0 hsd
  refine ⟨Cps, Cu, hCps, hCu, fun σ hfin hcpt hmass T hT hhom => ?_⟩
  haveI := hfin.1
  haveI := hfin.2
  have hcont := uhigh_u_cont hd hs0 hsd σ
  have hsupp := uhigh_u_fsupp hd hs0 hsd σ
  have hadm : IsAdmissible σ := ⟨hfin, Or.inl hcpt⟩
  have h1 := hps σ hadm hmass
  have h2 : eLpNorm (fun x => ‖σ.convForce (gloForce s) x‖) (ENNReal.ofReal (p2E d s)) volume ≤
      ENNReal.ofReal Cps * T ^ ((1 : ℝ) / 2) := by
    refine h1.trans ?_
    gcongr
  have hTq : T ^ ((1 : ℝ) / 2) < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) hT
  have hmem : MemLp (fun x => ‖σ.convForce (gloForce s) x‖) (ENNReal.ofReal (p2E d s)) volume :=
    lt_of_le_of_lt h2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hTq)
  obtain ⟨U, -, hU⟩ := hus _ hcont hmem hsupp
  refine ⟨hcont, hsupp, hmem, h2, ?_⟩
  calc cubeSupNorm (p2E d s) (fun x => σ.convForce (gloForce s) x)
      ≤ eLpNorm (fun x => ‖U x‖) (ENNReal.ofReal (p2E d s)) volume +
          cubeSupNorm (p2E d s) (fun x => σ.convForce (gloForce s) x) := le_add_self
    _ ≤ ENNReal.ofReal Cu *
          eLpNorm (fun x => ‖σ.convForce (gloForce s) x‖) (ENNReal.ofReal (p2E d s)) volume := hU
    _ ≤ ENNReal.ofReal Cu * (ENNReal.ofReal Cps * T ^ ((1 : ℝ) / 2)) := by gcongr

/-- `(5.backgroundclosing)` (`[N] L716-728`). -/
theorem uhigh_background_main (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p → p⁻¹ + q⁻¹ = 1 →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp →
      ∀ ρ : Euc d → ℝ, BddCptDensity ρ →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
        |∫ x, ρ x * inner ℝ (Pgt 1 v x) ((chargeOf X ρ).convForce (gloForce s) x)| ≤
          C * K * (modEnergy s X ρ + Cp * (1 / (N : ℝ) + normE p ρ)) := by
  obtain ⟨Cprod, hCprod, hprod⟩ := product_estimate_aesm hd hs0 hsd
  obtain ⟨Cps, Cu, hCps, hCu, hu⟩ := uhigh_u_main hd hs0 hsd
  obtain ⟨Ci, hCi, hint⟩ := intro_control hd hs0 hsd
  obtain ⟨Cb, hCb, hEC⟩ := energy_control hd hs0 hsd
  refine ⟨Cprod * Cps * Ci, by positivity, fun p q hp hpq => ?_⟩
  obtain ⟨Cp1, hCp1, hI⟩ := hint p q hp hpq
  obtain ⟨Cp2, hCp2, hE⟩ := hEC p q hp hpq
  refine ⟨max Cp1 Cp2, lt_max_of_lt_left hCp1,
    fun Cp hCp ρ hρ N X hN hX v K hv => ?_⟩
  have h1 := hI Cp (le_trans (le_max_left _ _) hCp) ρ hρ N X hN hX
  obtain ⟨h0, -⟩ := hE Cp (le_trans (le_max_right _ _) hCp) ρ hρ N X hN hX
  set Ec := modEnergy s X ρ + Cp * (1 / (N : ℝ) + normE p ρ) with hEc
  have hNpos : (0 : ℝ) < 1 / (N : ℝ) := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hnp : 0 ≤ normE p ρ := ENNReal.toReal_nonneg
  have hf0 : 0 ≤ normE q (fTrunc s 1 : Euc d → ℝ) := ENNReal.toReal_nonneg
  have hEc0 : 0 ≤ Ec := by
    have : 0 ≤ (1 + normE q (fTrunc s 1 : Euc d → ℝ)) * normE p ρ :=
      mul_nonneg (by linarith) hnp
    linarith
  obtain ⟨L, F, hF0, hL, ⟨w, hrep, hw⟩, hLF⟩ := hv
  have hfd : HasFracData d s v L w F := ⟨hL, hrep, hw⟩
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hK0 : 0 ≤ K := by linarith
  have hadm := chargeOf_admissible ρ hρ hN X
  set T : ℝ≥0∞ := ENNReal.ofReal (Ci * Ec) with hT
  have hTtop : T ≠ ⊤ := ENNReal.ofReal_ne_top
  have hhom : homSqE (-alphaE d s) (lowFreq 4 (chargeOf X ρ).fourier) ≤ T :=
    le_trans (le_trans le_self_add le_self_add) h1
  have hsob : sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 ρ) ≤ T :=
    le_trans (le_trans le_add_self le_self_add) h1
  obtain ⟨hucont, hsupp, hmemu, hunorm, -⟩ :=
    hu (chargeOf X ρ) hadm.1 hadm.2.1 (fun _ => hadm.2.2) T hTtop hhom
  obtain ⟨hg2, hgb⟩ := hprod v L w F hfd _ hucont.aestronglyMeasurable hmemu hsupp
  have hρ2 : MemLp ρ 2 volume := energyAux_memLp_two ρ hρ
  have hcs := inhom_pairing_le hρ2 hg2 (-alphaE d s)
  rw [neg_neg] at hcs
  have hFK : F ≤ K := by linarith
  have hTq : T ^ ((1 : ℝ) / 2) < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) hTtop
  have hmain : ENNReal.ofReal |∫ x, ρ x * inner ℝ (Pgt 1 v x) ((chargeOf X ρ).convForce (gloForce s) x)| ≤
      ENNReal.ofReal (Cprod * Cps * Ci * K * Ec) := by
    calc ENNReal.ofReal |∫ x, ρ x * inner ℝ (Pgt 1 v x) ((chargeOf X ρ).convForce (gloForce s) x)|
        ≤ sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 ρ) ^ ((1 : ℝ) / 2) *
            sobSqE (alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 fun x =>
              inner ℝ (Pgt 1 v x) ((chargeOf X ρ).convForce (gloForce s) x)) ^ ((1 : ℝ) / 2) := hcs
      _ ≤ T ^ ((1 : ℝ) / 2) * (ENNReal.ofReal (Cprod * F) *
            (ENNReal.ofReal Cps * T ^ ((1 : ℝ) / 2))) := by
          gcongr
          exact hgb.trans (by gcongr)
      _ = ENNReal.ofReal (Cprod * F) * ENNReal.ofReal Cps * T := by
          have := uhigh_sqrt_mul_sqrt T
          generalize T ^ ((1 : ℝ) / 2) = Y at this ⊢
          rw [← this]
          ring
      _ = ENNReal.ofReal (Cprod * F * Cps * (Ci * Ec)) := by
          rw [hT, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (Cprod * Cps * Ci * K * Ec) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have : Cprod * F * Cps * (Ci * Ec) = (Cprod * Cps * Ci * Ec) * F := by ring
          rw [this]
          have e2 : Cprod * Cps * Ci * K * Ec = (Cprod * Cps * Ci * Ec) * K := by ring
          rw [e2]
          exact mul_le_mul_of_nonneg_left hFK (by positivity)
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hmain
  calc _ ≤ Cprod * Cps * Ci * K * Ec := this
    _ = Cprod * Cps * Ci * K * Ec := rfl

end HRS.Commutator.Whole.UHIGH
