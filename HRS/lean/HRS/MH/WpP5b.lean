import HRS.MH.WpSpec2
import HRS.MH.WpP3b
import HRS.MH.WpP4
import HRS.MH.WpQ1
import HRS.Main.GFFinal4

/-!
# P5b: `HRS.MH.Wp.gff_core_Wp_transport`

Order-`p` copy-edit of `HRS.GF.gff_core_transport` (GFFinal4.lean:18-241), with the gradient provider `gf_ev_grad_proof`,
stage 1 `gff_stage1_p_proof` (P3b), stage 2 `gff_stage2_p_proof` (P4), and the proved transport coupling
`gf_adapted_coupling_transport`.  The exponent algebra in `ℝ≥0∞` is isolated in three lemmas:
`wp5b_cost_term` (`(∫⁻ (ofReal c * w)^{p/2})^{1/p} = ofReal √c * (∫⁻ w^{p/2})^{1/p}`),
`wp5b_ofReal_toReal_sq_le` (`ofReal (w.toReal ^ 2) ≤ w ^ 2`, also at `w = ⊤`) and `wp5b_ae_lt_top`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.WpP

open HRS HRS.GF HRS.Uniform HRS.Uniform.Kot

/-- The constant pulled out of an `L^{p/2}`-type norm: `(∫⁻ (ofReal c * w)^{p/2})^{1/p} = ofReal √c * (∫⁻ w^{p/2})^{1/p}`. -/
theorem wp5b_cost_term {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ) (hc : 0 ≤ c) (p : ℝ)
    (hp : 0 < p) (w : Ω → ℝ≥0∞) :
    (∫⁻ ω, (ENNReal.ofReal c * w ω) ^ (p / 2) ∂μ) ^ (1 / p) =
      ENNReal.ofReal (Real.sqrt c) * (∫⁻ ω, w ω ^ (p / 2) ∂μ) ^ (1 / p) := by
  have hp2 : 0 ≤ p / 2 := by positivity
  have h1 : ∀ ω, (ENNReal.ofReal c * w ω) ^ (p / 2) = ENNReal.ofReal c ^ (p / 2) * w ω ^ (p / 2) :=
    fun ω => ENNReal.mul_rpow_of_nonneg _ _ hp2
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp2 ENNReal.ofReal_ne_top),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.2 hp.le), ← ENNReal.rpow_mul]
  have e : p / 2 * (1 / p) = 1 / 2 := by field_simp
  rw [e, ENNReal.ofReal_rpow_of_nonneg hc (by norm_num), Real.sqrt_eq_rpow]

/-- `ofReal (w.toReal ^ 2) ≤ w ^ 2` in `ℝ≥0∞`, also at `w = ⊤`. -/
theorem wp5b_ofReal_toReal_sq_le (w : ℝ≥0∞) : ENNReal.ofReal (w.toReal ^ 2) ≤ w ^ 2 := by
  rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg]
  exact pow_le_pow_left' ENNReal.ofReal_toReal_le 2

/-- From `(∫⁻ E^p)^{1/p} ≠ ⊤` for a measurable `E`, `E < ⊤` almost everywhere. -/
theorem wp5b_ae_lt_top {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : Ω → ℝ≥0∞) (hE : Measurable E)
    (p : ℝ) (hp : 0 < p) (h : (∫⁻ ω, E ω ^ p ∂μ) ^ (1 / p) ≠ ⊤) : ∀ᵐ ω ∂μ, E ω < ⊤ := by
  have h1 : ∫⁻ ω, E ω ^ p ∂μ ≠ ⊤ := by
    intro h0
    rw [h0, ENNReal.top_rpow_of_pos (by positivity)] at h
    exact h rfl
  have h2 := ae_lt_top (hE.pow_const p) h1
  filter_upwards [h2] with ω hω
  by_contra hne
  rw [not_lt, top_le_iff] at hne
  rw [hne, ENNReal.top_rpow_of_pos hp] at hω
  exact lt_irrefl _ hω

/-- `Σ aᵢ xᵢ ≤ C Σ xᵢ` when all `aᵢ ≤ C`. -/
theorem wp5b_combine (a b c C x y z : ℝ≥0∞) (ha : a ≤ C) (hb : b ≤ C) (hc : c ≤ C) :
    a * x + b * y + c * z ≤ C * (x + y + z) := by
  calc a * x + b * y + c * z ≤ C * x + C * y + C * z := by gcongr
    _ = C * (x + y + z) := by ring

set_option maxHeartbeats 1600000 in
theorem gff_core_Wp_transport_proof : type_of% @HRS.MH.Wp.gff_core_Wp_transport := by
  intro d b p hp
  have hp0 : 0 < p := by linarith
  obtain ⟨K, hK0, hev⟩ := gf_ev_grad_proof b
  obtain ⟨C₀a, hs1⟩ := gff_stage1_p_proof b (-1) K p hp0
  refine ⟨C₀a, fun C₀ hC₀ => ?_⟩
  by_cases hex : ∃ S₀ : GeneralSetup d, S₀.Within { b with C₀ := C₀ }
  swap
  · exact ⟨1, one_pos, fun S hS => absurd ⟨S, hS⟩ hex⟩
  obtain ⟨S₀, hS₀⟩ := hex
  have hbT : 0 ≤ b.T := by rw [← hS₀.2.1]; exact S₀.hT.le
  have hd1 : 1 ≤ d := by have := S₀.hd; omega
  have hγb : (d : ℝ) / 2 + 2 < (b.γ : ℝ) := by
    have h1 : 2 * d + 10 < S₀.γ := S₀.hγ
    have h2 : S₀.γ = b.γ := hS₀.2.2.1
    have h3 : ((2 * d + 10 : ℕ) : ℝ) < (b.γ : ℝ) := by exact_mod_cast (h2 ▸ h1)
    push_cast at h3
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Cr, hCr, hs1'⟩ := hs1 C₀ hC₀
  obtain ⟨C2, hC20, hs2⟩ := gff_stage2_p_proof b.T K p hbT hp
  obtain ⟨Ctr, hCtr⟩ := gf_adapted_coupling_transport (d := d) hd1
  have hCtrb : 0 < Ctr (b.γ : ℝ) := (hCtr (b.γ : ℝ) hγb).1
  set C : ℝ := C2 + Cr + C2 * Real.sqrt (Ctr (b.γ : ℝ)) + 1 with hCdef
  have hCpos : 0 < C := by
    have : 0 ≤ C2 + Cr + C2 * Real.sqrt (Ctr (b.γ : ℝ)) := by positivity
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro S hS hMF hPos N hN Ω mΩ P _ X₀ W _hBr X hX hF η₀ hη hind Y hY σ A q Ξ YN ε En Wt hEn
  have hT' : 0 ≤ S.T := S.hT.le
  have hST : S.T = b.T := hS.2.1
  have hSw : S.Within { b with C₀ := S.C₀ } := by
    have hC : S.C₀ = C₀ := hS.2.2.2.2.2.1
    rw [hC]; exact hS
  obtain ⟨EV, hEV⟩ := hev S hSw hMF hPos N
  have hm : (S.γ : ℝ) ≤ (S.γ : ℝ) := le_rfl
  have hj : ∀ x, EV.j x = x := fun x => by rw [hEV.j_eq, embed_self]
  set Y₀ : Ω → NegSobolev d (S.γ : ℝ) := fun ω => AN S N • η₀ ω with hY₀def
  have hY₀m : Measurable Y₀ := hη.const_smul (AN S N)
  have hY₀ : ∀ ω, Y₀ ω = EV.j (AN S N • η₀ ω) := fun ω => by rw [hj]
  -- finiteness of the energy integral
  obtain ⟨-, hmeasE, -⟩ := gfwp_energy_aux_proof S (-1) hMF N hN P X₀ W X hX hF
  have hEfin := wp5b_ae_lt_top P _ hmeasE p hp0 hEn
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, π₁, hπ₁, ℱ₁, η', Mart, Z, Bm, hS1, hX₁, hF₁, hlaw, hinit, hBmp⟩ :=
    hs1' S hS hMF N hN (S.γ : ℝ) hm EV hEV P X₀ W X hX hF hEfin η₀ hη hind Y₀ hY₀m hY₀ Y hY
  set X₁ : ℝ≥0 → Ω₁ → Config d N := fun t ω => X t (π₁ ω) with hX₁def
  have hq0 := qN_nonneg S N
  have hγS : (d : ℝ) / 2 + 2 < (S.γ : ℝ) := by
    have h1 : 2 * d + 10 < S.γ := S.hγ
    have h3 : ((2 * d + 10 : ℕ) : ℝ) < (S.γ : ℝ) := by exact_mod_cast h1
    push_cast at h3
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hCtS : Ctr (S.γ : ℝ) = Ctr (b.γ : ℝ) := by rw [hS.2.2.1]
  have hCtSpos : 0 < Ctr (S.γ : ℝ) := (hCtr (S.γ : ℝ) hγS).1
  have hdens : ∀ r ∈ Set.Icc (0 : ℝ) S.T, IsProbDensity (S.ρ N r) :=
    fun r hr => (hMF N).1.density r hr
  have hcplT := (hCtr (S.γ : ℝ) hγS).2 P₁ ℱ₁ ⟨ℱ₁ 0, le_rfl⟩ N (by omega) (qN S N) hq0 S.T hT'
    (fun r => X₁ (Real.toNNReal r)) (S.ρ N) hdens hS1.det Mart hS1.mart
  -- measurability of the transport cost
  obtain ⟨hwm1, -⟩ := gfwp_transport_cost_meas_proof S (-1) hMF N hN P₁ (fun ω => X₀ (π₁ ω))
    (fun t ω => W t (π₁ ω)) X₁ hX₁ hF₁
  obtain ⟨hwmP, -⟩ := gfwp_transport_cost_meas_proof S (-1) hMF N hN P X₀ W X hX hF
  set wI : Ω₁ → ℝ≥0∞ := fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
    ((torusWassersteinE 2 (empirical (X₁ (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r))).toReal ^ 2)
    with hwI
  set wP : Ω → ℝ≥0∞ := fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
    ((torusWassersteinE 2 (empirical (X (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r))).toReal ^ 2)
    with hwP
  set cT : ℝ := Ctr (S.γ : ℝ) * qN S N with hcT
  have hcT0 : 0 ≤ cT := mul_nonneg hCtSpos.le hq0
  have hcostE : ∀ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (Ctr (S.γ : ℝ) * qN S N *
      (torusWassersteinE 2 (empirical (X₁ (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r))).toReal ^ 2)) =
      ENNReal.ofReal cT * wI ω := by
    intro ω
    simp only [hwI]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun r => ?_
    rw [hcT, ENNReal.ofReal_mul hcT0] <;> rfl
  have hcostm : AEMeasurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (Ctr (S.γ : ℝ) * qN S N *
      (torusWassersteinE 2 (empirical (X₁ (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r))).toReal ^ 2)) P₁ := by
    have : (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (Ctr (S.γ : ℝ) * qN S N *
      (torusWassersteinE 2 (empirical (X₁ (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r))).toReal ^ 2)) =
        fun ω => ENNReal.ofReal cT * wI ω := funext hcostE
    rw [this]; exact (hwm1.const_mul _).aemeasurable
  have hW0 := hs2 S hST (-1) hMF N hN (S.γ : ℝ) hm EV hEV P P₁ ℱ₁ X₁ η' Mart Z Bm Y₀ Y hS1
    (fun r ω => Ctr (S.γ : ℝ) * qN S N *
      (torusWassersteinE 2 (empirical (X₁ (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r))).toReal ^ 2)
    hcplT hcostm
  rw [hlaw] at hW0
  -- the cost term
  have hcostB : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (Ctr (S.γ : ℝ) * qN S N *
      (torusWassersteinE 2 (empirical (X₁ (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r))).toReal ^ 2)) ^
        (p / 2) ∂P₁) ^ (1 / p) ≤
      ENNReal.ofReal (Real.sqrt (Ctr (b.γ : ℝ)) * Real.sqrt (qN S N)) * Wt := by
    have e1 : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (Ctr (S.γ : ℝ) * qN S N *
      (torusWassersteinE 2 (empirical (X₁ (Real.toNNReal r) ω)) (withDensityReal (S.ρ N r))).toReal ^ 2)) ^
        (p / 2) ∂P₁) = ∫⁻ ω, (ENNReal.ofReal cT * wI ω) ^ (p / 2) ∂P₁ :=
      lintegral_congr fun ω => congrArg (· ^ (p / 2)) (hcostE ω)
    rw [e1, wp5b_cost_term P₁ cT hcT0 p hp0 wI]
    have e2 : Real.sqrt cT = Real.sqrt (Ctr (b.γ : ℝ)) * Real.sqrt (qN S N) := by
      rw [hcT, hCtS, Real.sqrt_mul hCtrb.le]
    rw [e2]
    refine mul_le_mul' le_rfl ?_
    have e3 : (∫⁻ ω, wI ω ^ (p / 2) ∂P₁) = ∫⁻ ω, wP ω ^ (p / 2) ∂P :=
      lintegral_comp_mp hπ₁ (f := fun ω => wP ω ^ (p / 2)) (hwmP.pow_const _).aemeasurable
    rw [e3]
    refine ENNReal.rpow_le_rpow (lintegral_mono fun ω => ?_) (by positivity)
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    refine lintegral_mono fun r => ?_
    exact wp5b_ofReal_toReal_sq_le _
  -- assembly
  have e4 : ENNReal.ofReal (Cr * sigN S N) = ENNReal.ofReal Cr * ENNReal.ofReal σ :=
    ENNReal.ofReal_mul hCr.le
  have e5 : ENNReal.ofReal C2 * ENNReal.ofReal (Real.sqrt (Ctr (b.γ : ℝ)) * Real.sqrt (qN S N)) =
      ENNReal.ofReal (C2 * Real.sqrt (Ctr (b.γ : ℝ))) * ENNReal.ofReal (Real.sqrt q) := by
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), ENNReal.ofReal_mul hC20, ← mul_assoc]
  have hsq := mul_nonneg hC20 (Real.sqrt_nonneg (Ctr (b.γ : ℝ)))
  have hs0 := Real.sqrt_nonneg (Ctr (b.γ : ℝ))
  have hCa : ENNReal.ofReal C2 ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal (by rw [hCdef]; linarith)
  have hCb : ENNReal.ofReal Cr ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal (by rw [hCdef]; linarith)
  have hCc : ENNReal.ofReal (C2 * Real.sqrt (Ctr (b.γ : ℝ))) ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal (by rw [hCdef]; linarith)
  calc wassersteinE p Ξ YN ≤ _ := hW0
    _ ≤ ENNReal.ofReal C2 * (ENNReal.ofReal A * ε) + ENNReal.ofReal Cr * ENNReal.ofReal σ * En +
        ENNReal.ofReal C2 * (ENNReal.ofReal (Real.sqrt (Ctr (b.γ : ℝ)) * Real.sqrt (qN S N)) * Wt) := by
        refine add_le_add (add_le_add (le_of_eq ?_) ?_) (mul_le_mul' le_rfl hcostB)
        · rw [hinit]
        · rw [← e4]; exact hBmp
    _ = ENNReal.ofReal C2 * (ENNReal.ofReal A * ε) + ENNReal.ofReal Cr * (ENNReal.ofReal σ * En) +
        ENNReal.ofReal (C2 * Real.sqrt (Ctr (b.γ : ℝ))) * (ENNReal.ofReal (Real.sqrt q) * Wt) := by
        rw [← mul_assoc (ENNReal.ofReal C2) (ENNReal.ofReal (Real.sqrt (Ctr (b.γ : ℝ)) * Real.sqrt (qN S N))) Wt, e5]
        ring
    _ ≤ _ := wp5b_combine _ _ _ _ _ _ _ hCa hCb hCc

end HRS.MH.WpP
