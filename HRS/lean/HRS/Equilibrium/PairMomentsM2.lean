/-
# HRS.Equilibrium.PairMomentsM2 -- two-pin means of the triple kernel (EQ-01b)
-/
import HRS.Equilibrium.PairMomentsL1

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}

section RealMean2

theorem real_mean2 {k Λ B Ctp C2 Cp δC Cb Cu w ℓ L m δ lam : ℝ} (hk : 0 ≤ k) (hΛ : 0 ≤ Λ) (hB : 0 ≤ B)
    (hCt : 0 ≤ Ctp) (hC2 : 0 ≤ C2) (hCp : 0 ≤ Cp) (hδC : 0 ≤ δC) (hCb : 0 ≤ Cb) (hCu : 0 ≤ Cu)
    (hm : 0 ≤ m) (hδ : 0 ≤ δ) (hlam : 0 ≤ lam)
    (hmδ : m * δ ≤ δC * L) (hml : m * (lam * (1 + |Real.log lam|)) ≤ Cb * L) (hmlam : m * lam ≤ 1 + Cu)
    (hw : 1 ≤ w) (hℓ : ℓ ≤ 5 * w) (hℓ1 : 1 ≤ ℓ) (hL : 1 ≤ L) :
    m * (k * (δ * (Λ * (2 * B * w + Ctp * ℓ))) + k * C2 * (Λ * (Cp * lam * w * (1 + |Real.log lam| + ℓ)))) ≤
      k * (Λ * (δC * (2 * B + 5 * Ctp) + C2 * Cp * max Cb (1 + Cu))) * (w * (L + ℓ)) := by
  have hw0 : 0 ≤ w := by linarith
  have hbnd : 2 * B * w + Ctp * ℓ ≤ (2 * B + 5 * Ctp) * w := by nlinarith
  have hbnd0 : 0 ≤ 2 * B * w + Ctp * ℓ := by positivity
  have t1 : m * δ * (2 * B * w + Ctp * ℓ) ≤ δC * L * ((2 * B + 5 * Ctp) * w) :=
    mul_le_mul hmδ hbnd hbnd0 (by positivity)
  have t2 : m * (lam * w * (1 + |Real.log lam| + ℓ)) ≤ w * (max Cb (1 + Cu) * (L + ℓ)) := by
    have e : m * (lam * w * (1 + |Real.log lam| + ℓ)) =
        w * (m * (lam * (1 + |Real.log lam|)) + (m * lam) * ℓ) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hw0
    have h1 : (m * lam) * ℓ ≤ (1 + Cu) * ℓ := mul_le_mul_of_nonneg_right hmlam (by linarith)
    have h2 : Cb * L ≤ max Cb (1 + Cu) * L := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    have h3 : (1 + Cu) * ℓ ≤ max Cb (1 + Cu) * ℓ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    nlinarith
  have hLw : L * w ≤ w * (L + ℓ) := by nlinarith
  have hkΛ : 0 ≤ k * Λ := mul_nonneg hk hΛ
  calc m * (k * (δ * (Λ * (2 * B * w + Ctp * ℓ))) + k * C2 * (Λ * (Cp * lam * w * (1 + |Real.log lam| + ℓ))))
      = k * Λ * (m * δ * (2 * B * w + Ctp * ℓ)) + k * Λ * (C2 * Cp) * (m * (lam * w * (1 + |Real.log lam| + ℓ))) := by ring
    _ ≤ k * Λ * (δC * L * ((2 * B + 5 * Ctp) * w)) + k * Λ * (C2 * Cp) * (w * (max Cb (1 + Cu) * (L + ℓ))) := by
        gcongr
    _ ≤ k * Λ * (δC * (2 * B + 5 * Ctp) * (w * (L + ℓ))) + k * Λ * (C2 * Cp) * (max Cb (1 + Cu) * (w * (L + ℓ))) := by
        have h1 : δC * L * ((2 * B + 5 * Ctp) * w) = δC * (2 * B + 5 * Ctp) * (L * w) := by ring
        have h2 : w * (max Cb (1 + Cu) * (L + ℓ)) = max Cb (1 + Cu) * (w * (L + ℓ)) := by ring
        rw [h1, h2]
        gcongr
    _ = _ := by ring

end RealMean2

section Mean2Large

theorem mean2_large (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) (Cu : ℝ) (hCu : 0 ≤ Cu) (δC : ℝ) (hδC : 0 ≤ δC)
    (C2 : ℝ) (hC2 : 0 ≤ C2) :
    ∃ Cμ : ℝ, 0 ≤ Cμ ∧ ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V →
      (∀ x y : Torus d, x ≠ y → V.q x y ≤ Cu * wEnv s x y) → ∀ m : ℕ, 1 ≤ m → ∀ C1 : ℝ,
      RefDens V β (m + 1) (δC * deltaN d s (m + 2)) C1 → RefDens2 V β m C2 →
      ∀ (K : ℝ) (g3 : Torus d → Torus d → Torus d → ℝ),
      Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) →
      IsCanonicalTriple (withDensityReal ρ) g3 →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤ K * tEnv s x y z) →
      ∀ x u : Torus d, x ≠ u →
        |∑ k : Fin m, ∫ z, g3 x u z ∂((pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) m
          (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k))| ≤
          (|K| * Cμ) * (wEnv s x u * (logEN (m + 2) + ellEnv x u)) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨B, Ctp, hB0, hCt0, hT⟩ := lintegral_mu_tEnv (s := s) hd hcrit
  obtain ⟨Cp, hCp0, hCpF⟩ := lintegral_mu_tEnv_cap (s := s) hd hcrit
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  set Cb : ℝ := (1 + Cu) * (1 + |Real.log (1 + Cu)|) with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  refine ⟨Λ * (δC * (2 * B + 5 * Ctp) + C2 * Cp * max Cb (1 + Cu)), by positivity, ?_⟩
  intro V hV hVu m hm1 C1 RD1 RD2 K g3 hgm hcan hg3 x u hxu
  have hN2 : 2 ≤ m + 2 := by omega
  have hNp : (0 : ℝ) < ((m + 1 + 1 : ℕ) : ℝ) := by positivity
  set Nr : ℝ := ((m + 1 + 1 : ℕ) : ℝ) with hNr
  have hNm : (m : ℝ) ≤ Nr := by simp only [hNr]; push_cast; linarith
  have hlam0 : 0 ≤ β / Nr := by positivity
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  set δ : ℝ := δC * deltaN d s (m + 2) with hδ
  have hδ0 : 0 ≤ δ := mul_nonneg hδC (by rw [deltaN_crit hcrit]; have := logEN_pos' (N := m + 2) (by omega); positivity)
  set lam : ℝ := (1 + Cu) / Nr with hlamdef
  have hlam : 0 < lam := by positivity
  set W : ℝ := |K| * (δ * (Λ * (2 * B * wEnv s x u + Ctp * ellEnv x u))) +
    |K| * C2 * (Λ * (Cp * lam * wEnv s x u * (1 + |Real.log lam| + ellEnv x u))) with hW
  have hw1 := PairCorrAux.one_le_wEnv s x u
  have hℓ1 := one_le_ellEnv x u
  have hW0 : 0 ≤ W := by positivity
  have hmt : Measurable fun z : Torus d => ENNReal.ofReal (tEnv s x u z) := by
    have h1 := PairCorrAux.measurable_wEnv s x
    have h2 := PairCorrAux.measurable_wEnv s u
    refine ENNReal.measurable_ofReal.comp ?_
    unfold tEnv
    exact (measurable_const.mul h1).add (measurable_const.mul h2) |>.add (h1.mul h2)
  have hmc : Measurable fun z : Torus d =>
      ENNReal.ofReal (tEnv s x u z * min 1 (lam * (1 + wEnv s x z + wEnv s u z))) := by
    have h1 := PairCorrAux.measurable_wEnv s x
    have h2 := PairCorrAux.measurable_wEnv s u
    refine ENNReal.measurable_ofReal.comp ?_
    unfold tEnv
    exact (((measurable_const.mul h1).add (measurable_const.mul h2)).add (h1.mul h2)).mul
      (measurable_const.min (measurable_const.mul ((measurable_const.add h1).add h2)))
  have hae : ∀ᵐ z ∂(withDensityReal ρ), z ≠ x ∧ z ≠ u :=
    (HRS.External.PoleVar.ae_ne_pt hatom x).and (HRS.External.PoleVar.ae_ne_pt hatom u)
  have hWint : ∫⁻ z, ENNReal.ofReal (|g3 x u z| * (δ + C2 * min 1 ((1 / Nr) * (1 + V.q z x + V.q z u))))
      ∂(withDensityReal ρ) ≤ ENNReal.ofReal W := by
    have hpt : ∀ᵐ z ∂(withDensityReal ρ), ENNReal.ofReal (|g3 x u z| * (δ + C2 * min 1 ((1 / Nr) *
        (1 + V.q z x + V.q z u)))) ≤ ENNReal.ofReal (|K| * δ) * ENNReal.ofReal (tEnv s x u z) +
          ENNReal.ofReal (|K| * C2) * ENNReal.ofReal (tEnv s x u z *
            min 1 (lam * (1 + wEnv s x z + wEnv s u z))) := by
      filter_upwards [hae] with z hz
      have hzx : x ≠ z := Ne.symm hz.1
      have hzu : u ≠ z := Ne.symm hz.2
      have hf : |g3 x u z| ≤ |K| * tEnv s x u z :=
        (hg3 x u z hxu hzx hzu).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (tEnv_nonneg s x u z))
      have hq1 : V.q z x ≤ Cu * wEnv s x z := by
        have := hVu z x hz.1
        rwa [PairCorrAux.wEnv_symm s z x] at this
      have hq2 : V.q z u ≤ Cu * wEnv s u z := by
        have := hVu z u hz.2
        rwa [PairCorrAux.wEnv_symm s z u] at this
      have hwxz := PairCorrAux.one_le_wEnv s x z
      have hwuz := PairCorrAux.one_le_wEnv s u z
      have hmn : min 1 ((1 / Nr) * (1 + V.q z x + V.q z u)) ≤ min 1 (lam * (1 + wEnv s x z + wEnv s u z)) := by
        refine min_le_min le_rfl ?_
        have h1 : 1 + V.q z x + V.q z u ≤ (1 + Cu) * (1 + wEnv s x z + wEnv s u z) := by nlinarith
        calc (1 / Nr) * (1 + V.q z x + V.q z u) ≤ (1 / Nr) * ((1 + Cu) * (1 + wEnv s x z + wEnv s u z)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = lam * (1 + wEnv s x z + wEnv s u z) := by rw [hlamdef]; ring
      have hq0 := V.q_nonneg z x
      have hq0' := V.q_nonneg z u
      have ht0 := tEnv_nonneg s x u z
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hmn0 : 0 ≤ min 1 ((1 / Nr) * (1 + V.q z x + V.q z u)) := le_min zero_le_one (by positivity)
      calc |g3 x u z| * (δ + C2 * min 1 ((1 / Nr) * (1 + V.q z x + V.q z u)))
          ≤ (|K| * tEnv s x u z) * (δ + C2 * min 1 (lam * (1 + wEnv s x z + wEnv s u z))) := by
            refine mul_le_mul hf ?_ (by positivity) (by positivity)
            have := mul_le_mul_of_nonneg_left hmn hC2
            linarith
        _ = _ := by ring
    calc _ ≤ ∫⁻ z, (ENNReal.ofReal (|K| * δ) * ENNReal.ofReal (tEnv s x u z) +
          ENNReal.ofReal (|K| * C2) * ENNReal.ofReal (tEnv s x u z *
            min 1 (lam * (1 + wEnv s x z + wEnv s u z)))) ∂(withDensityReal ρ) := lintegral_mono_ae hpt
      _ = ENNReal.ofReal (|K| * δ) * ∫⁻ z, ENNReal.ofReal (tEnv s x u z) ∂(withDensityReal ρ) +
          ENNReal.ofReal (|K| * C2) * ∫⁻ z, ENNReal.ofReal (tEnv s x u z *
            min 1 (lam * (1 + wEnv s x z + wEnv s u z))) ∂(withDensityReal ρ) := by
          rw [lintegral_add_left (hmt.const_mul _), lintegral_const_mul _ hmt, lintegral_const_mul _ hmc]
      _ ≤ ENNReal.ofReal (|K| * δ) * ENNReal.ofReal (Λ * (2 * B * wEnv s x u + Ctp * ellEnv x u)) +
          ENNReal.ofReal (|K| * C2) * ENNReal.ofReal (Λ * (Cp * lam * wEnv s x u *
            (1 + |Real.log lam| + ellEnv x u))) := by
          gcongr
          · exact hT hΛ hΛ0.le x u hxu
          · exact hCpF hΛ hΛ0.le lam hlam x u hxu
      _ = ENNReal.ofReal W := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; rw [hW]; ring
  have hfπ : ∀ k : Fin m, Integrable (g3 x u) ((pinnedLaw V (β / Nr) m
      (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k)) :=
    fun k => g3_marg_integrable hd hcrit hρ hV hβ.le (by omega) (by omega : m + 2 ≤ m + 1 + 1) K hgm hg3 hxu k
  have hmain := mean_two_pins_le hβ.le RD1 RD2 (f := g3 x u) x u (hcan x u hxu).1 (hcan x u hxu).2 hfπ hW0 hWint
  refine hmain.trans ?_
  have hL1 := logEN_pos' (N := m + 2) (by omega)
  have hNd : ((m + 2 : ℕ) : ℝ) * deltaN d s (m + 2) = logEN (m + 2) := N_mul_deltaN hcrit (by omega)
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmδ : (m : ℝ) * δ ≤ δC * logEN (m + 2) := by
    have hd0 : 0 ≤ deltaN d s (m + 2) := by rw [deltaN_crit hcrit]; positivity
    calc (m : ℝ) * δ = δC * ((m : ℝ) * deltaN d s (m + 2)) := by rw [hδ]; ring
      _ ≤ δC * (((m + 2 : ℕ) : ℝ) * deltaN d s (m + 2)) := by
          gcongr
      _ = δC * logEN (m + 2) := by rw [hNd]
  have hml : (m : ℝ) * (lam * (1 + |Real.log lam|)) ≤ Cb * logEN (m + 2) := by
    have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have h := lam_log_bound (N := Nr) (n := (m : ℝ)) (Cu := Cu) (by linarith) hmR hNm hCu
    rw [← hlamdef] at h
    have hLeq : logEN (m + 2) = 1 + Real.log ((m + 2 : ℕ) : ℝ) := PairCorrAux.logEN_eq (m + 2) (by omega)
    have : Real.log Nr = Real.log ((m + 2 : ℕ) : ℝ) := rfl
    rw [hLeq, hCb, ← this]
    linarith
  have hmlam : (m : ℝ) * lam ≤ 1 + Cu := by
    rw [hlamdef, ← mul_div_assoc, div_le_iff₀ hNp]
    nlinarith
  have hℓ5 := ellEnv_le_wEnv hxu hs1
  have hfin := real_mean2 (k := |K|) (Λ := Λ) (B := B) (Ctp := Ctp) (C2 := C2) (Cp := Cp) (δC := δC)
    (Cb := Cb) (Cu := Cu) (w := wEnv s x u) (ℓ := ellEnv x u) (L := logEN (m + 2)) (m := m) (δ := δ)
    (lam := lam) (abs_nonneg K) hΛ0.le hB0 hCt0 hC2 hCp0 hδC hCb0 hCu hmR hδ0 hlam.le hmδ hml hmlam hw1 hℓ5 hℓ1 hL1
  rw [hW]
  exact hfin

end Mean2Large

section Mean2Crude

/-- The crude two-pin mean bound (valid for every `N`, no reference density input). -/
theorem mean2_crude (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (Mmax M'max γmax Cq : ℝ) :
    ∃ Ac : ℝ, 0 ≤ Ac ∧ ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V → ∀ m : ℕ, 1 ≤ m →
      ∀ (K : ℝ) (g3 : Torus d → Torus d → Torus d → ℝ),
      Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤ K * tEnv s x y z) →
      ∀ x u : Torus d, x ≠ u →
        |∑ k : Fin m, ∫ z, g3 x u z ∂((pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) m
          (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k))| ≤
          ((m : ℝ) * |K| * Ac) * (wEnv s x u * (logEN (m + 2) + ellEnv x u)) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨B, Ctp, hB0, hCt0, hT⟩ := g3_pole2_le (s := s) hd hcrit
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  set E0 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  refine ⟨E0 * Λ * (2 * B + Ctp), by positivity, ?_⟩
  intro V hV m hm1 K g3 hgm hg3 x u hxu
  have hgx : Measurable (g3 x u) :=
    Measurable.comp (g := fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) hgm
      (f := fun z : Torus d => (x, u, z)) (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hcard : m + Fintype.card (Option (Option Empty)) ≤ m + 2 := by simp
  have hw1 := PairCorrAux.one_le_wEnv s x u
  have hℓ1 := one_le_ellEnv x u
  have hL1 := logEN_pos' (N := m + 2) (by omega)
  have hW0 : 0 ≤ |K| * E0 * (Λ * (2 * B * wEnv s x u + Ctp * ellEnv x u)) := by positivity
  have hmain := abs_sum_marg_le V hβ.le (N := m + 2) (n := m) (by omega) hcard
    (pinsWith (pinsWith (fun e : Empty => e.elim) x) u) hgx hW0 (by
      refine (hT hΛ hΛ0.le hρ hV hβ.le K hg3 hxu).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul (by positivity)])
  refine hmain.trans ?_
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hX1 : wEnv s x u ≤ wEnv s x u * (logEN (m + 2) + ellEnv x u) := by nlinarith
  have hX2 : ellEnv x u ≤ wEnv s x u * (logEN (m + 2) + ellEnv x u) := by nlinarith
  have h1 : 2 * B * wEnv s x u + Ctp * ellEnv x u ≤ (2 * B + Ctp) * (wEnv s x u * (logEN (m + 2) + ellEnv x u)) := by
    nlinarith [mul_le_mul_of_nonneg_left hX1 hB0, mul_le_mul_of_nonneg_left hX2 hCt0]
  have h0 : 0 ≤ (m : ℝ) * (|K| * E0 * Λ) := by positivity
  calc (m : ℝ) * (|K| * E0 * (Λ * (2 * B * wEnv s x u + Ctp * ellEnv x u)))
      = ((m : ℝ) * (|K| * E0 * Λ)) * (2 * B * wEnv s x u + Ctp * ellEnv x u) := by ring
    _ ≤ ((m : ℝ) * (|K| * E0 * Λ)) * ((2 * B + Ctp) * (wEnv s x u * (logEN (m + 2) + ellEnv x u))) :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = _ := by ring

end Mean2Crude

end HRS.PairMom

end
