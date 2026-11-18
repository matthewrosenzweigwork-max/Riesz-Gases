import HRS.MS.Sf8Aux1
import HRS.MS.Sf8Aux4

/-!
# Lemma S.B.8(ii) (`same_function_rd_weighted`) on `ℝ^d` (packet MS-SF8II)

`same_function_rd_weighted_proof` restates `HRS.Whole.same_function_rd_weighted` (frozen in
`HRS/Whole/AppendixBKernel.lean`, statement copied verbatim).  Route: `Sf8Plan.md`.  The weight
`ς = χ_z^τ²` lies in `[0,1]`, is `2Lχ`-Lipschitz and vanishes outside `B(Ψ_τ z, 2L)`, `L = e^{Cb T}`; the
abstract estimate `Sf8Aux4.core` needs only local `L²` bounds of `w` on balls, which follow from the
bound `S` on the flow cells by the cell cover `Sf8Aux1.cell_cover`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Sf8

open HRS.Whole HRS.MS.SameFunction

variable {d : ℕ}

theorem same_function_rd_weighted_proof (hd : 1 ≤ d) (s : ℝ) (hs1 : (d : ℝ) - 1 < s) (hsd : s < d)
    (m : ℕ) (Cb T : ℝ) :
    ∀ χ χh : Euc d → ℝ, IsCutoffPair χ χh →
    ∃ C : ℝ, ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
      ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ z : Euc d, ∀ Lχ : ℝ,
        HRS.PDE.ToolboxRd.IsLipschitz Lχ (advCutoff χ Ψ τ z) →
      ∀ (κ : Euc d → ℝ) (K₀ : ℝ), (∀ z, κ (-z) = -κ z) →
      ContDiffOn ℝ ∞ κ {z | z ≠ 0} → (∀ z : Euc d, z ≠ 0 → |κ z| ≤ K₀ * ‖z‖ ^ (-s - 1)) →
      ∀ (La Λ : ℝ) (a w : Euc d → ℝ), HRS.PDE.ToolboxRd.IsLipschitz La a →
        (∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) → Measurable w →
      ∀ S : ℝ, 0 ≤ S → (∀ z' : Fin d → ℤ,
        eLpNorm ((flowCell Ψ τ z').indicator w) 2 volume ≤ ENNReal.ofReal S) →
      Integrable (fun p : Euc d × Euc d => κ (p.1 - p.2) * w p.1 * w p.2 *
        (a p.2 * advCutoff χ Ψ τ z p.1 ^ 2 - a p.1 * advCutoff χ Ψ τ z p.2 ^ 2)) ∧
      Tendsto (fun ε => truncPairing ε κ a w (fun x => advCutoff χ Ψ τ z x ^ 2)) (𝓝[>] 0)
        (𝓝 (symPairing κ a w (fun x => advCutoff χ Ψ τ z x ^ 2))) ∧
      |symPairing κ a w (fun x => advCutoff χ Ψ τ z x ^ 2)| ≤
        C * K₀ * (La + Λ) * (1 + Lχ) ^ 2 * S ^ 2 * (C * Real.exp (C * d * τ)) := by
  intro χ χh hχ
  set L : ℝ := Real.exp (Cb * T) with hLdef
  have hL0 : 0 < L := Real.exp_pos _
  set R₀ : ℝ := 2 * L with hR₀def
  set V1 : ℝ := (volume (Metric.ball (0 : Euc d) 1)).toReal with hV1
  set VR : ℝ := (volume (Metric.ball (0 : Euc d) R₀)).toReal with hVR
  set P2 : ℝ := (2 * L * (R₀ + 1) + 3) ^ d with hP2
  set P1 : ℝ := (2 * L * 1 + 3) ^ d with hP1
  set I1 : ℝ := ∫ z : Euc d, msf_I1 s z with hI1
  have hs2 : (d : ℝ) < s + 1 := by linarith
  have hfc := farConst_nonneg hd hs2
  have hI1nn : 0 ≤ I1 := integral_nonneg (msf_I1_nonneg s)
  have hP2nn : 0 ≤ P2 := by positivity
  have hP1nn : 0 ≤ P1 := by positivity
  have hV1nn : 0 ≤ V1 := ENNReal.toReal_nonneg
  have hVRnn : 0 ≤ VR := ENNReal.toReal_nonneg
  set X : ℝ := I1 * P2 + farConst d s * (P2 + VR) * (P1 + V1) with hX
  have hXnn : 0 ≤ X := by positivity
  refine ⟨max 1 (2 * X), ?_⟩
  intro b Ψ hb hΨ τ hτ z Lχ hLχ κ K₀ hodd hsm hbd La Λ a w ha hjb hwm S hS hcell
  obtain ⟨hCb, hΨlip, hΦlip, hΦΨ, hΨΦ⟩ := flow_data hb hΨ hτ
  have hτ0 : 0 ≤ τ := hτ.1
  set Φ : Euc d → Euc d := Function.invFun (Ψ τ) with hΦdef
  have hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := hχ.1.2.2.2.1
  have hχts : tsupport χ ⊆ Metric.ball 0 2 := hχ.1.2.2.1
  set ς : Euc d → ℝ := fun x => advCutoff χ Ψ τ z x ^ 2 with hςdef
  have hadv01 : ∀ x, advCutoff χ Ψ τ z x ∈ Set.Icc (0 : ℝ) 1 := fun x => hχ01 _
  have hς0 : ∀ x, 0 ≤ ς x := fun x => sq_nonneg _
  have hς1 : ∀ x, ς x ≤ 1 := fun x => by
    have h := hadv01 x
    show advCutoff χ Ψ τ z x ^ 2 ≤ 1
    nlinarith [h.1, h.2]
  have hLχ0 : 0 ≤ Lχ := lip_nonneg hd hLχ
  have hςL : ∀ x y, |ς x - ς y| ≤ (2 * Lχ) * ‖x - y‖ := by
    intro x y
    have hx := hadv01 x
    have hy := hadv01 y
    have e : ς x - ς y = (advCutoff χ Ψ τ z x - advCutoff χ Ψ τ z y) *
        (advCutoff χ Ψ τ z x + advCutoff χ Ψ τ z y) := by
      simp only [hςdef]; ring
    rw [e, abs_mul]
    have h1 : |advCutoff χ Ψ τ z x + advCutoff χ Ψ τ z y| ≤ 2 := by
      rw [abs_of_nonneg (add_nonneg hx.1 hy.1)]; linarith [hx.2, hy.2]
    calc |advCutoff χ Ψ τ z x - advCutoff χ Ψ τ z y| * |advCutoff χ Ψ τ z x + advCutoff χ Ψ τ z y|
        ≤ (Lχ * ‖x - y‖) * 2 := mul_le_mul (hLχ x y) h1 (abs_nonneg _) (by positivity)
      _ = (2 * Lχ) * ‖x - y‖ := by ring
  have hsupp : ∀ x, ς x ≠ 0 → x ∈ Metric.ball (Ψ τ z) R₀ := by
    intro x hx
    have hadv : advCutoff χ Ψ τ z x ≠ 0 := fun h0 => hx (by simp only [hςdef, h0]; norm_num)
    have hχx : χ (Φ x - z) ≠ 0 := hadv
    have hmem : Φ x - z ∈ Metric.ball (0 : Euc d) 2 := hχts (subset_tsupport _ hχx)
    rw [mem_ball_zero_iff] at hmem
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖Ψ τ (Φ x) - Ψ τ z‖ ≤ L * ‖Φ x - z‖ := hΨlip _ _
    rw [hΨΦ x] at h1
    calc ‖x - Ψ τ z‖ ≤ L * ‖Φ x - z‖ := h1
      _ < L * 2 := mul_lt_mul_of_pos_left hmem hL0
      _ = R₀ := by rw [hR₀def]; ring
  -- local L² bounds from the cell bound
  have hcell' : ∀ z' : Fin d → ℤ, eLpNorm ((Ψ τ '' HRS.Whole.AppendixALemmas.latticeCell z').indicator w)
      2 volume ≤ ENNReal.ofReal S := by
    intro z'
    rw [← flowCell_eq]; exact hcell z'
  have hcov := fun (u : Euc d) {R : ℝ} (hR : 0 ≤ R) =>
    cell_cover hL0.le hΦΨ hΨΦ hΦlip hwm hS hcell' u hR
  have hm2 : ∫⁻ x in Metric.ball (Ψ τ z) (R₀ + 1), ENNReal.ofReal (w x ^ 2) ≤
      ENNReal.ofReal (P2 * S ^ 2) := hcov _ (by positivity)
  have hm2' : ∫⁻ x in Metric.ball (Ψ τ z) R₀, ENNReal.ofReal (w x ^ 2) ≤
      ENNReal.ofReal (P2 * S ^ 2) :=
    (lintegral_mono_set (Metric.ball_subset_ball (by linarith))).trans hm2
  have hm1 : ∫⁻ x in Metric.ball (Ψ τ z) R₀, ENNReal.ofReal |w x| ≤
      ENNReal.ofReal (S * (P2 + VR)) := by
    have h := l1_of_l2 (B := Metric.ball (Ψ τ z) R₀) measurableSet_ball measure_ball_lt_top.ne hwm
      hP2nn hS hm2'
    rwa [Measure.addHaar_ball_center] at h
  have hm3 : ∀ u : Euc d, ∫⁻ x in Metric.ball u 1, ENNReal.ofReal |w x| ≤
      ENNReal.ofReal (S * (P1 + V1)) := by
    intro u
    have h := l1_of_l2 (B := Metric.ball u 1) measurableSet_ball measure_ball_lt_top.ne hwm hP1nn hS
      (hcov u zero_le_one)
    rwa [Measure.addHaar_ball_center] at h
  have hM1 : 0 ≤ S * (P2 + VR) := by positivity
  have hM2 : 0 ≤ P2 * S ^ 2 := by positivity
  have hM3 : 0 ≤ S * (P1 + V1) := by positivity
  obtain ⟨hint, hlim, hbound⟩ := core hd hs1 hsd hodd hsm hbd ha hjb hς0 hς1 hςL hsupp hwm
    hM1 hM2 hM3 hm2 hm1 hm3
  refine ⟨hint, hlim, ?_⟩
  obtain ⟨hK, hLa, hΛ⟩ := nonneg_facts hd hbd ha hjb
  set C : ℝ := max 1 (2 * X) with hC
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCX : 2 * X ≤ C := le_max_right _ _
  have he1 : 1 ≤ Real.exp (C * d * τ) :=
    Real.one_le_exp (mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg d)) hτ0)
  have hQ : 0 ≤ K₀ * (La + Λ) * S ^ 2 := by positivity
  have e1 : K₀ * (La + Λ) * (1 + 2 * Lχ) *
      (I1 * (P2 * S ^ 2) + farConst d s * (S * (P2 + VR)) * (S * (P1 + V1))) =
      (K₀ * (La + Λ) * S ^ 2) * ((1 + 2 * Lχ) * X) := by
    simp only [hX]; ring
  have e2 : C * K₀ * (La + Λ) * (1 + Lχ) ^ 2 * S ^ 2 * (C * Real.exp (C * d * τ)) =
      (K₀ * (La + Λ) * S ^ 2) * ((1 + Lχ) ^ 2 * (C * (C * Real.exp (C * d * τ)))) := by ring
  refine hbound.trans ?_
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_left ?_ hQ
  have h1 : (1 + 2 * Lχ) * X ≤ (1 + Lχ) ^ 2 * (2 * X) := by
    have e : (1 + Lχ) ^ 2 * (2 * X) - (1 + 2 * Lχ) * X = X * (1 + 2 * Lχ + 2 * Lχ ^ 2) := by ring
    have : 0 ≤ X * (1 + 2 * Lχ + 2 * Lχ ^ 2) := by positivity
    linarith
  have h2 : 2 * X ≤ C * (C * Real.exp (C * d * τ)) := by
    have h : 1 ≤ C * Real.exp (C * d * τ) := one_le_mul_of_one_le_of_one_le hC1 he1
    calc 2 * X ≤ C := hCX
      _ = C * 1 := (mul_one _).symm
      _ ≤ C * (C * Real.exp (C * d * τ)) := mul_le_mul_of_nonneg_left h (by linarith)
  calc (1 + 2 * Lχ) * X ≤ (1 + Lχ) ^ 2 * (2 * X) := h1
    _ ≤ (1 + Lχ) ^ 2 * (C * (C * Real.exp (C * d * τ))) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

example := (@same_function_rd_weighted_proof : type_of% @HRS.Whole.same_function_rd_weighted)

end HRS.MS.Sf8
