import HRS.MS.R2WinOrbTRD12

/-!
# S10.3 packet [C], part 13: the second-level layer

Prefix `s103c_`, namespace `HRS.MS.R2WinOrbNL`.

`s103c_layer2`: let `ψ_l = L_lφ` (the datum of the first-level solutions `fam2 l`).  Then
`(fam2 l e - ψ_e)/(l-e) → L_t L_t φ + Q_{ρ'_t} φ` in `Bd N0` as `e ≤ t ≤ l`, `l-e → 0`.  The proof splits
`Λ - χ = [(fam2 l e - ψ_l)/(l-e) - L_tψ_l] (s103c_layer1) + L_t(ψ_l - ψ_t) + Q_δ φ`, `δ = (ρ_l-ρ_e)/(l-e) - ρ'_t`.
The only input on the time regularity of `ρ'` beyond the Schwartz-time bounds is the weighted continuity hypothesis `hUC`
(`t ↦ ρ'_t` continuous into the weighted `C^{N0+1}` norm), together with the pointwise continuity of `ρ'` (for the fundamental theorem of calculus).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul HRS.MS.Who HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.R2WinOrb

variable {d : ℕ}

theorem s103c_U2Dec_smul {K : ℕ} {L A : ℝ} {h : Euc d → ℝ} (hh : U2Dec K L A h) (c : ℝ) :
    U2Dec K L (|c| * A) (fun y => c * h y) := by
  refine ⟨contDiff_const.mul hh.1, fun m hm y => ?_⟩
  have e : (fun y => c * h y) = c • h := by funext y; simp
  rw [e, iteratedFDeriv_const_smul_apply (hh.1.of_le (by exact_mod_cast hm)).contDiffAt, norm_smul,
    Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hh.2 m hm y) (abs_nonneg _)

set_option maxHeartbeats 2000000 in
theorem s103c_layer2 {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (N0 Lnat : ℕ) (hL : (d : ℝ) + ((N0 + 4 : ℕ) : ℝ) + s + 3 < (Lnat : ℝ)) (T : ℝ) (hT : 0 ≤ T)
    (ρ ρ' : ℝ → Euc d → ℝ) (Aρ Ad : ℝ) (hAρ : 0 ≤ Aρ) (hAd : 0 ≤ Ad)
    (hU : ∀ τ, 0 ≤ τ → U2Dec (N0 + 5) (Lnat : ℝ) Aρ (ρ τ))
    (hD : ∀ τ, 0 ≤ τ → U2Dec (N0 + 3) (Lnat : ℝ) Ad (ρ' τ))
    (hder : ∀ τ, 0 ≤ τ → ∀ x, HasDerivWithinAt (fun σ => ρ σ x) (ρ' τ x) (Set.Ici τ) τ)
    (hcont : ∀ x, ContinuousOn (fun σ => ρ σ x) (Set.Ici 0))
    (hρ'c : ∀ x, ContinuousOn (fun σ => ρ' σ x) (Set.Ici 0))
    (hUC : ∀ t, 0 ≤ t → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ σ, 0 ≤ σ → |σ - t| < η →
      U2Dec (N0 + 1) (Lnat : ℝ) ε (fun y => ρ' σ y - ρ' t y))
    (φ : Euc d → ℝ) (Aφ : ℝ) (hAφ : 0 ≤ Aφ) (hφ : SyN 3 (N0 + 6) Aφ φ) (G : ℝ) (hG : 0 ≤ G)
    (fam2 : ℝ → ℝ → Euc d → ℝ)
    (hfam2 : ∀ l ∈ Set.Icc (0 : ℝ) T, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) l
      (fun y => generatorW ((quadraticGradientDyn d s a β).coeff ρ) l φ y) (fam2 l))
    (hjets : ∀ l ∈ Set.Icc (0 : ℝ) T, ∀ τ ∈ Set.Icc (0 : ℝ) l,
      ContDiff ℝ ((N0 + 4 : ℕ) : WithTop ℕ∞) (fam2 l τ) ∧
        ∀ i, 1 ≤ i → i ≤ N0 + 4 → ∀ y, ‖iteratedFDeriv ℝ i (fam2 l τ) y‖ ≤ G) :
    ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ e l : ℝ, 0 ≤ e → e < l → l ≤ T → e ≤ t → t ≤ l →
      l - e < δ →
      Bd N0 ε (fun y => (fam2 l e y - fam2 e e y) / (l - e) -
        (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t
          (fun x => generatorW ((quadraticGradientDyn d s a β).coeff ρ) t φ x) y + s103nQ d s (ρ' t) φ y)) := by
  set Cf := (quadraticGradientDyn d s a β).coeff ρ with hCf
  have hdL : (d : ℝ) < (Lnat : ℝ) := by
    have : (0 : ℝ) ≤ ((N0 + 4 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hL0 : (d : ℝ) + N0 + s + 3 < (Lnat : ℝ) := by
    have : (N0 : ℝ) ≤ ((N0 + 4 : ℕ) : ℝ) := by push_cast; linarith
    linarith
  have hL1 : (d : ℝ) + ((N0 + 2 : ℕ) : ℝ) + s + 3 < (Lnat : ℝ) := by
    have : ((N0 + 2 : ℕ) : ℝ) ≤ ((N0 + 4 : ℕ) : ℝ) := by push_cast; linarith
    linarith
  have hL2 : (d : ℝ) + ((N0 + 2 : ℕ) : ℝ) + s + 3 < (Lnat : ℝ) := hL1
  obtain ⟨Cl, hCl0, hCl⟩ := s103c_layer1 hd hs0 hsd a β ha hβ N0 Lnat hL1 T hT
  obtain ⟨Cg1, hCg10, hCg1⟩ := s103c_g1_datd hd hs0 hsd a β (N0 + 4) hL
  obtain ⟨KB, hKB0, hKB⟩ := s103c_gen_bd_dec hd hs0 hsd a β ha N0 hL0
  obtain ⟨Cq, hCq0, hCq⟩ := s103b_q_sy hd hs0 hsd N0 hL0
  obtain ⟨Cq2, hCq20, hCq2⟩ := s103b_q_sy hd hs0 hsd (N0 + 2) hL2
  set Crl3 : ℝ := (max 1 (d : ℝ)) ^ (N0 + 3) * ((5 / 4 : ℝ) ^ Lnat) ^ (N0 + 3) with hCrl3
  set cavg : ℝ := (max 1 (d : ℝ)) ^ (N0 + 1) * ((5 / 4 : ℝ) ^ Lnat) ^ (N0 + 1) with hcavg
  have hCrl30 : 0 ≤ Crl3 := by positivity
  have hcavg0 : 0 ≤ cavg := by positivity
  set A1 : ℝ := Cg1 * ((1 + Aρ) * Aφ) with hA1
  have hA10 : 0 ≤ A1 := by positivity
  -- the data `ψ_l = L_lφ`
  set ψ : ℝ → Euc d → ℝ := fun l y => generatorW Cf l φ y with hψdef
  have hψ : ∀ l, 0 ≤ l → DatD (N0 + 4) A1 (ψ l) := by
    intro l hl
    have := hCg1 Aρ Aφ (ρ l) φ hAρ hAφ (hU l hl) hφ
    have e : (ψ l) = fun x => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ l)) 0 φ x := by
      funext x; exact s103n_gen_frozen ρ l φ x
    rw [e]; exact this
  have hφC : ContDiff ℝ ((N0 + 4 : ℕ) : WithTop ℕ∞) φ := hφ.1.of_le (by exact_mod_cast (by omega : N0 + 4 ≤ N0 + 6))
  have hφC2 : ContDiff ℝ 2 φ := by
    have := hφ.1.of_le (show ((2 : ℕ) : WithTop ℕ∞) ≤ ((N0 + 6 : ℕ) : WithTop ℕ∞) by exact_mod_cast (by omega))
    exact_mod_cast this
  have hφb : ∀ i, 1 ≤ i → i ≤ N0 + 4 → ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ Aφ := fun i h1 h2 y =>
    hφ.bd.2 i (by omega) y
  have hU1 : ∀ τ, 0 ≤ τ → U2Dec 1 (Lnat : ℝ) Aρ (ρ τ) := fun τ hτ => ult_U2Dec_mono (hU τ hτ) (by omega)
  have hUm : ∀ τ, 0 ≤ τ → U2Dec (N0 + 1) (Lnat : ℝ) Aρ (ρ τ) := fun τ hτ => ult_U2Dec_mono (hU τ hτ) (by omega)
  -- the identity `ψ_b - ψ_a = Q_{ρ_b - ρ_a} φ`
  have hψdiff : ∀ a' b' : ℝ, 0 ≤ a' → 0 ≤ b' → ∀ y, ψ b' y - ψ a' y =
      s103bQ d s (fun y => ρ b' y - ρ a' y) φ y := by
    intro a' b' ha' hb' y
    simp only [hψdef]
    rw [s103b_gen_split, s103b_gen_split, s103c_Q_sub hd hs0 hsd hdL (hU1 b' hb') (hU1 a' ha') hφC2 (fun i h1 h2 y => hφb i h1 (by omega) y) y]
    ring
  have hlip := fun (a' b' : ℝ) (ha' : 0 ≤ a') (hb' : 0 ≤ b') => s103c_rho_lip' (K := N0 + 3) (L := Lnat) hAd hder hcont
    (fun τ hτ => (hU τ hτ).1.of_le (by exact_mod_cast (by omega : N0 + 3 ≤ N0 + 5))) hD (a := a') (b := b') ha' hb'
  intro t ht0 htT ε hε
  -- constants
  set K1 : ℝ := Cl * (Ad * G + (1 + Aρ) * (A1 + Aρ * G)) with hK1
  set K2 : ℝ := KB * (1 + (1 + Aρ)) * (Cq2 * Crl3 * Ad * Aφ) with hK2
  have hK10 : 0 ≤ K1 := by positivity
  have hK20 : 0 ≤ K2 := by positivity
  set ε₃ : ℝ := ε / (3 * (Cq * cavg * Aφ + 1)) with hε₃
  have hε₃0 : 0 < ε₃ := by positivity
  obtain ⟨η, hη, hUCη⟩ := hUC t ht0 ε₃ hε₃0
  refine ⟨min (ε / (3 * (K1 + K2 + 1))) η, lt_min (by positivity) hη, fun e l he hel hlT het htl hlδ => ?_⟩
  have hlδ1 : l - e < ε / (3 * (K1 + K2 + 1)) := hlδ.trans_le (min_le_left _ _)
  have hlη : l - e < η := hlδ.trans_le (min_le_right _ _)
  have hl0 : 0 ≤ l := he.trans hel.le
  have hle : 0 < l - e := sub_pos.2 hel
  have hlI : l ∈ Set.Icc (0 : ℝ) T := ⟨hl0, hlT⟩
  have heI : e ∈ Set.Icc (0 : ℝ) T := ⟨he, hel.le.trans hlT⟩
  have htl0 : |l - t| ≤ l - e := by rw [abs_le]; constructor <;> linarith
  -- P1: the first-level layer for the datum `ψ_l`
  have P1 := hCl ρ ρ' Aρ Ad hAρ hAd (fun τ hτ => ult_U2Dec_mono (hU τ hτ) (by omega))
    (fun τ hτ => ult_U2Dec_mono (hD τ hτ) (by omega)) hder hcont (ψ l) A1 (hψ l hl0) G l (fam2 l) hlI
    (hfam2 l hlI) (hjets l hlI) e t he hel het htl
  -- P2: `L_t (ψ_l - ψ_t)`
  have hδρ := hlip t l ht0 hl0
  have hδρ' : U2Dec (N0 + 2 + 1) (Lnat : ℝ) (Crl3 * Ad * |l - t|) (fun y => ρ l y - ρ t y) := hδρ
  have hQ2 := hCq2 (Crl3 * Ad * |l - t|) (fun y => ρ l y - ρ t y) (by positivity) hδρ' Aφ φ hφC hφb
  set Ae : ℝ := Cq2 * (Crl3 * Ad * |l - t|) * Aφ with hAe
  have hAe0 : 0 ≤ Ae := by positivity
  have hedef : (fun y => ψ l y - ψ t y) = s103bQ d s (fun y => ρ l y - ρ t y) φ :=
    funext fun y => hψdiff t l ht0 hl0 y
  have hT2 := hKB ρ Aρ t hAρ (hUm t ht0) (fun y => ψ l y - ψ t y) Ae Ae
    (by rw [hedef]; exact hQ2.1)
    (fun i h1 h2 y => by rw [hedef]; exact hQ2.2 i (by omega) y)
    (fun i h1 h2 y => by rw [hedef]; exact hQ2.bd.2 i (by omega) y)
  have hψj : ∀ l', 0 ≤ l' → ContDiff ℝ 2 (ψ l') ∧ ∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i (ψ l') y‖ ≤ A1 := by
    intro l' hl'
    refine ⟨?_, fun i h1 h2 y => (hψ l' hl').2.1 i (by omega) y⟩
    have := (hψ l' hl').1.of_le (show ((2 : ℕ) : WithTop ℕ∞) ≤ ((N0 + 4 : ℕ) : WithTop ℕ∞) by exact_mod_cast (by omega))
    exact_mod_cast this
  have hP2id : ∀ y, generatorW Cf t (ψ l) y - generatorW Cf t (ψ t) y =
      generatorW Cf t (fun y => ψ l y - ψ t y) y := fun y =>
    (s103c_gen_sub hd hs0 hsd hdL ρ t (hU1 t ht0) (hψj l hl0).1 (hψj l hl0).2 (hψj t ht0).1 (hψj t ht0).2 y).symm
  have hP2b : KB * (Ae + (1 + Aρ) * Ae) ≤ K2 * (l - e) := by
    have hAe' : Ae ≤ Cq2 * Crl3 * Ad * Aφ * (l - e) := by
      rw [hAe]
      calc Cq2 * (Crl3 * Ad * |l - t|) * Aφ ≤ Cq2 * (Crl3 * Ad * (l - e)) * Aφ := by gcongr
        _ = _ := by ring
    calc KB * (Ae + (1 + Aρ) * Ae) = KB * (1 + (1 + Aρ)) * Ae := by ring
      _ ≤ KB * (1 + (1 + Aρ)) * (Cq2 * Crl3 * Ad * Aφ * (l - e)) := by gcongr
      _ = _ := by rw [hK2]; ring
  -- P3: the density derivative
  set δh : Euc d → ℝ := fun y => (l - e)⁻¹ * (ρ l y - ρ e y) - ρ' t y with hδh
  have hδU : U2Dec (N0 + 1) (Lnat : ℝ) (cavg * ε₃) δh := by
    have hint0 : ∀ y, IntervalIntegrable (fun σ => ρ' σ y) volume e l := fun y =>
      ((hρ'c y).mono (fun σ hσ => he.trans hσ.1 : Set.Icc e l ⊆ Set.Ici 0)).intervalIntegrable_of_Icc hel.le
    have hint : ∀ y, IntervalIntegrable (fun σ => (l - e)⁻¹ * (ρ' σ y - ρ' t y)) volume e l := fun y =>
      ((hint0 y).sub intervalIntegrable_const).const_mul _
    have hg : ∀ σ ∈ Set.Icc e l, U2Dec (N0 + 1) (Lnat : ℝ) ((l - e)⁻¹ * ε₃)
        (fun y => (l - e)⁻¹ * (ρ' σ y - ρ' t y)) := by
      intro σ hσ
      have hσ0 : 0 ≤ σ := he.trans hσ.1
      have := s103c_U2Dec_smul (hUCη σ hσ0 (by rw [abs_lt]; constructor <;> linarith [hσ.1, hσ.2])) ((l - e)⁻¹)
      rwa [abs_of_pos (inv_pos.2 hle)] at this
    have hGc : ContDiff ℝ ((N0 + 1 : ℕ) : WithTop ℕ∞) δh := by
      have h1 : ContDiff ℝ ((N0 + 1 : ℕ) : WithTop ℕ∞) (ρ l) :=
        (hU l hl0).1.of_le (by exact_mod_cast (by omega : N0 + 1 ≤ N0 + 5))
      have h2 : ContDiff ℝ ((N0 + 1 : ℕ) : WithTop ℕ∞) (ρ e) :=
        (hU e he).1.of_le (by exact_mod_cast (by omega : N0 + 1 ≤ N0 + 5))
      have h3 : ContDiff ℝ ((N0 + 1 : ℕ) : WithTop ℕ∞) (ρ' t) :=
        (hD t ht0).1.of_le (by exact_mod_cast (by omega : N0 + 1 ≤ N0 + 3))
      exact (contDiff_const.mul (h1.sub h2)).sub h3
    have hGeq : ∀ y, δh y = ∫ σ in e..l, (l - e)⁻¹ * (ρ' σ y - ρ' t y) := by
      intro y
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hint0 y) intervalIntegrable_const,
        ← s103c_rho_ftc hder hcont hρ'c he hel.le y]
      simp only [intervalIntegral.integral_const, smul_eq_mul, hδh]
      field_simp
    have := s103c_avg_u2dec hel.le (by positivity : 0 ≤ (l - e)⁻¹ * ε₃) hint hg hGc hGeq
    have ec : (max 1 (d : ℝ)) ^ (N0 + 1) * ((5 / 4 : ℝ) ^ Lnat) ^ (N0 + 1) * ((l - e)⁻¹ * ε₃) * (l - e) =
        cavg * ε₃ := by rw [hcavg]; field_simp
    rwa [ec] at this
  have hφC2' : ContDiff ℝ ((N0 + 2 : ℕ) : WithTop ℕ∞) φ := hφ.1.of_le (by exact_mod_cast (by omega : N0 + 2 ≤ N0 + 6))
  have hQ3 := hCq (cavg * ε₃) δh (by positivity) hδU Aφ φ hφC2' (fun i h1 h2 y => hφb i h1 (by omega) y)
  have hP3id : ∀ y, (ψ l y - ψ e y) / (l - e) - s103nQ d s (ρ' t) φ y = s103bQ d s δh φ y := by
    intro y
    rw [hψdiff e l he hl0 y, s103c_nQ_eq]
    have hq := s103c_Q_smul (s := s) ((l - e)⁻¹) (fun y => ρ l y - ρ e y) φ y
    have hU1h : U2Dec 1 (Lnat : ℝ) (|(l - e)⁻¹| * (Crl3 * Ad * |l - e|))
        (fun y => (l - e)⁻¹ * (ρ l y - ρ e y)) :=
      ult_U2Dec_mono (s103c_U2Dec_smul (hlip e l he hl0) ((l - e)⁻¹)) (by omega)
    have hsubQ := s103c_Q_sub (s := s) hd hs0 hsd hdL (h1 := fun y => (l - e)⁻¹ * (ρ l y - ρ e y))
      (h2 := ρ' t) hU1h (ult_U2Dec_mono (hD t ht0) (by omega)) hφC2 (fun i h1 h2 y => hφb i h1 (by omega) y) y
    have e : δh = fun y => (l - e)⁻¹ * (ρ l y - ρ e y) - ρ' t y := rfl
    rw [e, hsubQ, hq, div_eq_inv_mul]
  have hfinal : (fun y => (fam2 l e y - fam2 e e y) / (l - e) -
      (generatorW Cf t (fun x => generatorW Cf t φ x) y + s103nQ d s (ρ' t) φ y)) =
      fun y => ((fam2 l e y - ψ l y) / (l - e) - generatorW Cf t (ψ l) y +
        generatorW Cf t (fun y => ψ l y - ψ t y) y) + s103bQ d s δh φ y := by
    funext y
    have h1 : fam2 e e y = ψ e y := by
      have := (hfam2 e heI).terminal
      exact congrFun this y
    rw [h1, ← hP3id y, ← hP2id y]
    have e2 : generatorW Cf t (ψ t) y = generatorW Cf t (fun x => generatorW Cf t φ x) y := rfl
    rw [e2]
    field_simp
    ring
  rw [hfinal]
  have hsum := (P1.add hT2).add hQ3.bd
  refine hsum.mono_A ?_
  have hlt : (K1 + K2 + 1) * (l - e) < ε / 3 := by
    calc (K1 + K2 + 1) * (l - e) < (K1 + K2 + 1) * (ε / (3 * (K1 + K2 + 1))) :=
          mul_lt_mul_of_pos_left hlδ1 (by positivity)
      _ = ε / 3 := by field_simp
  have hP3b : Cq * (cavg * ε₃) * Aφ ≤ ε / 3 := by
    have : Cq * (cavg * ε₃) * Aφ = (Cq * cavg * Aφ) * ε₃ := by ring
    rw [this, hε₃]
    have hpos : 0 < Cq * cavg * Aφ + 1 := by positivity
    calc (Cq * cavg * Aφ) * (ε / (3 * (Cq * cavg * Aφ + 1))) ≤ (Cq * cavg * Aφ + 1) * (ε / (3 * (Cq * cavg * Aφ + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = ε / 3 := by field_simp
  nlinarith [hP2b, mul_nonneg hK10 hle.le, mul_nonneg hK20 hle.le]

end HRS.MS.R2WinOrbNL

end
