import HRS.MH.ScreenedAsmLocal
import HRS.MH.ScreenedS5c
import HRS.MH.ScreenedK5
import HRS.MH.ScreenedF1
import HRS.MH.ScreenedF5
import HRS.MH.ScreenedF6

/-!
# Assembly `screened_comm_local` (S.B.4(iv), local part)

`screened_local_proof` (valid for all `0 ≤ s < d`, with `kgOrder d s ∈ [0,1)`) applied to the three
localised data `(χ̂_z - χ_z) v`, `v`, `χ_z v`; the Sobolev norms of the first and third are controlled by
`mult_sobolev_proof` (`B = 1`, Lipschitz constants `2 Lχ L`, `Lχ L`, `L = exp(CF τ)` from
`flow_lip_sep_proof`, `advCutoff_facts_proof`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

lemma acl_cont {La : ℝ} {ϕ : Euc d → ℝ} (hLa : 0 ≤ La) (hL : HRS.PDE.ToolboxRd.IsLipschitz La ϕ) :
    Continuous ϕ := by
  refine (LipschitzWith.of_dist_le_mul (K := La.toNNReal) (fun x y => ?_)).continuous
  simpa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hLa] using hL x y

lemma acl_ind_mul_le {ϕ w : Euc d → ℝ} (hϕ : ∀ x, |ϕ x| ≤ 1) (hc : Continuous ϕ)
    (hw : LocallyIntegrable w volume) {B : Set (Euc d)} (hB : MeasurableSet B) :
    eLpNorm (B.indicator (fun x => ϕ x * w x)) 2 volume ≤ eLpNorm (B.indicator w) 2 volume := by
  refine eLpNorm_mono ((hc.aestronglyMeasurable.mul hw.aestronglyMeasurable).indicator hB) fun x => ?_
  by_cases hx : x ∈ B
  · simp only [Set.indicator_of_mem hx, norm_mul, Real.norm_eq_abs]
    calc |ϕ x| * |w x| ≤ 1 * |w x| := mul_le_mul_of_nonneg_right (hϕ x) (abs_nonneg _)
      _ = |w x| := one_mul _
  · simp [Set.indicator_of_notMem hx]

lemma acl_alg {p y₁ : ℝ} (hp : 0 ≤ p) (_hy₁ : 0 ≤ y₁) (N : ℝ≥0∞) :
    ENNReal.ofReal p * (ENNReal.ofReal y₁ * N) = ENNReal.ofReal (p * y₁) * N := by
  rw [ENNReal.ofReal_mul hp, mul_assoc]

lemma acl_alg2 {p y : ℝ} (hp : 0 ≤ p) (hy : 0 ≤ y) (N : ℝ≥0∞) :
    ENNReal.ofReal p * N + ENNReal.ofReal p * (ENNReal.ofReal y * N) =
      ENNReal.ofReal (p * (1 + y)) * N := by
  rw [ENNReal.ofReal_mul hp, ENNReal.ofReal_add (by norm_num) hy, ENNReal.ofReal_one]
  ring

theorem screened_comm_local_proof : type_of% @HRS.Whole.screened_comm_local := by
  intro d hd s hs0 hsd m Cb T χ χh hχ
  obtain ⟨Cl0, Cl, hloc⟩ := screened_local_proof hd hs0 hsd
  obtain ⟨CF, hCF0, hF⟩ := flow_lip_sep_proof hd m Cb T χ χh hχ
  obtain ⟨Lχ, hLχ0, hLχ1, hLχ2⟩ := cutoff_lipschitz_proof χ χh hχ
  have hkg0 : 0 ≤ kgOrder d s := le_max_right _ _
  have hkg1 : kgOrder d s < 1 := max_lt (by linarith) one_pos
  obtain ⟨Cm, hCm0, hCm⟩ := mult_sobolev_proof hd hkg0 hkg1
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set X : ℝ := 1 + Cm * (2 * Lχ + 1) with hX
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith [mul_nonneg hCm0 (by linarith : (0:ℝ) ≤ 2 * Lχ + 1)]
  set C : ℝ := max (max Cl 0 * X) CF with hC
  have hCle1 : max Cl 0 * X ≤ C := le_max_left _ _
  have hCle2 : CF ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := le_trans hCF0 hCle2
  refine ⟨Cl0, C, ?_⟩
  intro b Ψ hb hΨ τ hτ z i ρ hρ c v hsupp hv
  obtain ⟨-, hL2, -⟩ := hF b Ψ hb hΨ τ hτ
  set L : ℝ := Real.exp (CF * τ) with hLdef
  have hL1 : 1 ≤ L := Real.one_le_exp (mul_nonneg hCF0 hτ.1)
  obtain ⟨hf0, hf1, -, -, -, -, hlipχ, hlipχh⟩ :=
    advCutoff_facts_proof χ χh hχ Ψ τ L Lχ (by linarith) hL2 ⟨hLχ1, hLχ2⟩ z
  have hLexp : L ≤ Real.exp (C * d * τ) := by
    refine Real.exp_le_exp.2 ?_
    have : CF ≤ C * d := le_trans hCle2 (le_mul_of_one_le_right hC0 hd1)
    exact mul_le_mul_of_nonneg_right this hτ.1
  -- the multipliers
  set ϕ3 : Euc d → ℝ := advCutoff χ Ψ τ z with hϕ3
  set ϕ1 : Euc d → ℝ := fun y => advCutoff χh Ψ τ z y - advCutoff χ Ψ τ z y with hϕ1
  have hLχL : 0 ≤ Lχ * L := mul_nonneg hLχ0 (by linarith)
  have hϕ3L : HRS.PDE.ToolboxRd.IsLipschitz (Lχ * L) ϕ3 := hlipχ
  have hϕ3B : ∀ x, |ϕ3 x| ≤ 1 := fun x => by
    have := hf0 x
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hϕ1L : HRS.PDE.ToolboxRd.IsLipschitz (2 * (Lχ * L)) ϕ1 := fun x y => by
    have h1 := hlipχh x y
    have h2 := hlipχ x y
    have : ϕ1 x - ϕ1 y = (advCutoff χh Ψ τ z x - advCutoff χh Ψ τ z y) -
        (advCutoff χ Ψ τ z x - advCutoff χ Ψ τ z y) := by simp only [hϕ1]; ring
    rw [this]
    calc _ ≤ |advCutoff χh Ψ τ z x - advCutoff χh Ψ τ z y| +
          |advCutoff χ Ψ τ z x - advCutoff χ Ψ τ z y| := abs_sub _ _
      _ ≤ 2 * (Lχ * L) * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]
  have hϕ1B : ∀ x, |ϕ1 x| ≤ 1 := fun x => by
    have a1 := hf0 x
    have a2 := hf1 x
    simp only [hϕ1]
    rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  have hc3 : Continuous ϕ3 := acl_cont hLχL hϕ3L
  set N : ℝ≥0∞ := sobolevNormE (kgOrder d s) v with hNdef
  have hN1 : sobolevNormE (kgOrder d s) (fun x => ϕ1 x * v x) ≤
      ENNReal.ofReal (Cm * (2 * (Lχ * L) + 1)) * N := hCm _ _ ϕ1 v hϕ1L hϕ1B
  have hN3 : sobolevNormE (kgOrder d s) (fun x => ϕ3 x * v x) ≤
      ENNReal.ofReal (Cm * (Lχ * L + 1)) * N := hCm _ _ ϕ3 v hϕ3L hϕ3B
  have hv1 : sobolevNormE (kgOrder d s) (fun x => ϕ1 x * v x) < ⊤ :=
    lt_of_le_of_lt hN1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv)
  have hv3 : sobolevNormE (kgOrder d s) (fun x => ϕ3 x * v x) < ⊤ :=
    lt_of_le_of_lt hN3 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv)
  have hs1 : Function.support (fun x => ϕ1 x * v x) ⊆ Metric.closedBall c ρ :=
    (Function.support_mul_subset_right _ _).trans hsupp
  have hs3 : Function.support (fun x => ϕ3 x * v x) ⊆ Metric.closedBall c ρ :=
    (Function.support_mul_subset_right _ _).trans hsupp
  obtain ⟨w₁, hr1, hb1⟩ := hloc i ρ hρ c _ hs1 hv1
  obtain ⟨w₂, hr2, hb2⟩ := hloc i ρ hρ c v hsupp hv
  obtain ⟨w₃, hr3, hb3⟩ := hloc i ρ hρ c _ hs3 hv3
  refine ⟨w₁, w₂, w₃, hr1, hr2, hr3, fun c' r' hr' => ?_⟩
  have hρ0 : 0 ≤ ρ ^ Cl0 := (Real.rpow_pos_of_pos (by linarith) _).le
  set p : ℝ := max Cl 0 * ρ ^ Cl0 with hp
  have hp0 : 0 ≤ p := mul_nonneg (le_max_right _ _) hρ0
  have hpl : ENNReal.ofReal (Cl * ρ ^ Cl0) ≤ ENNReal.ofReal p :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ0)
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ X * L → p * y ≤ C * Real.exp (C * d * τ) * ρ ^ Cl0 := by
    intro y hy0 hy
    calc p * y ≤ p * (X * L) := mul_le_mul_of_nonneg_left hy hp0
      _ = (max Cl 0 * X) * L * ρ ^ Cl0 := by rw [hp]; ring
      _ ≤ C * Real.exp (C * d * τ) * ρ ^ Cl0 := by
          gcongr
  have hy1 : Cm * (2 * (Lχ * L) + 1) ≤ X * L := by
    rw [hX]; nlinarith [mul_nonneg hCm0 hLχ0, mul_nonneg (mul_nonneg hCm0 hLχ0) (sub_nonneg.2 hL1),
      mul_nonneg hCm0 (sub_nonneg.2 hL1)]
  have hy3 : 1 + Cm * (Lχ * L + 1) ≤ X * L := by
    rw [hX]; nlinarith [mul_nonneg hCm0 hLχ0, mul_nonneg (mul_nonneg hCm0 hLχ0) (sub_nonneg.2 hL1),
      mul_nonneg hCm0 (sub_nonneg.2 hL1)]
  have hy1' : 0 ≤ Cm * (2 * (Lχ * L) + 1) := by positivity
  have hy3' : 0 ≤ Cm * (Lχ * L + 1) := by positivity
  constructor
  · calc eLpNorm ((Metric.closedBall c' r').indicator (fun x => advCutoff χ Ψ τ z x * w₁ x)) 2 volume
        ≤ eLpNorm ((Metric.closedBall c' r').indicator w₁) 2 volume := acl_ind_mul_le hϕ3B hc3 (k5a_locInt i hr1) measurableSet_closedBall
      _ ≤ ENNReal.ofReal (Cl * ρ ^ Cl0) * sobolevNormE (kgOrder d s) (fun x => ϕ1 x * v x) :=
          hb1 c' r' hr'
      _ ≤ ENNReal.ofReal p * (ENNReal.ofReal (Cm * (2 * (Lχ * L) + 1)) * N) :=
          mul_le_mul' hpl hN1
      _ = ENNReal.ofReal (p * (Cm * (2 * (Lχ * L) + 1))) * N := acl_alg hp0 hy1' N
      _ ≤ ENNReal.ofReal (C * Real.exp (C * d * τ) * ρ ^ Cl0) * N := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal (key _ hy1' hy1)) le_rfl
  · have hsplit : (Metric.closedBall c' r').indicator (fun x => advCutoff χ Ψ τ z x * w₂ x - w₃ x) =
        fun x => (Metric.closedBall c' r').indicator (fun x => advCutoff χ Ψ τ z x * w₂ x) x -
          (Metric.closedBall c' r').indicator w₃ x := by
      funext x
      by_cases hx : x ∈ Metric.closedBall c' r' <;> simp [Set.indicator, hx]
    rw [hsplit]
    calc eLpNorm (fun x => (Metric.closedBall c' r').indicator (fun x => advCutoff χ Ψ τ z x * w₂ x) x -
            (Metric.closedBall c' r').indicator w₃ x) 2 volume
        ≤ eLpNorm ((Metric.closedBall c' r').indicator (fun x => advCutoff χ Ψ τ z x * w₂ x)) 2 volume +
          eLpNorm ((Metric.closedBall c' r').indicator w₃) 2 volume :=
          eLpNorm_sub_le (by norm_num)
      _ ≤ ENNReal.ofReal (Cl * ρ ^ Cl0) * N +
          ENNReal.ofReal (Cl * ρ ^ Cl0) * sobolevNormE (kgOrder d s) (fun x => ϕ3 x * v x) :=
          add_le_add ((acl_ind_mul_le hϕ3B hc3 (k5a_locInt i hr2) measurableSet_closedBall).trans (hb2 c' r' hr')) (hb3 c' r' hr')
      _ ≤ ENNReal.ofReal p * N + ENNReal.ofReal p * (ENNReal.ofReal (Cm * (Lχ * L + 1)) * N) :=
          add_le_add (mul_le_mul' hpl le_rfl) (mul_le_mul' hpl hN3)
      _ = ENNReal.ofReal (p * (1 + Cm * (Lχ * L + 1))) * N := acl_alg2 hp0 hy3' N
      _ ≤ ENNReal.ofReal (C * Real.exp (C * d * τ) * ρ ^ Cl0) * N := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal (key _ (by positivity) hy3)) le_rfl

end HRS.MH.Screened
