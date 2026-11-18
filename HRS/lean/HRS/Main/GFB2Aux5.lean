import HRS.Main.GFB2Aux4

/-!
# Packet GFB2, part 5: transport moment (`gf_transport_moment`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

theorem gfb2_jensen_rpow {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : Ω → ℝ) (hGm : Measurable G) (hG0 : ∀ᵐ ω ∂P, 0 ≤ G ω) (hGi : Integrable G P) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Integrable (fun ω => G ω ^ p) P ∧ ∫ ω, G ω ^ p ∂P ≤ (∫ ω, G ω ∂P) ^ p := by
  have hint : Integrable (fun ω => G ω ^ p) P := by
    refine Integrable.mono' (hGi.add (integrable_const (1 : ℝ)))
      (hGm.pow_const p).aestronglyMeasurable ?_
    filter_upwards [hG0] with ω hω
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hω p)]
    by_cases h1 : G ω ≤ 1
    · have := Real.rpow_le_one hω h1 hp0
      simp only [Pi.add_apply]; linarith
    · push_neg at h1
      have := Real.rpow_le_rpow_of_exponent_le h1.le hp1
      rw [Real.rpow_one] at this
      simp only [Pi.add_apply]; linarith
  refine ⟨hint, ?_⟩
  exact (Real.concaveOn_rpow hp0 hp1).le_map_integral (Real.continuous_rpow_const hp0).continuousOn
    isClosed_Ici (by filter_upwards [hG0] with ω hω using hω) hGi hint

theorem gfb2_sup_le_cbNorm {K : ℕ} {φ : Torus d → ℝ} (hφ : Torus.IsCk K φ) (x : Torus d) :
    |φ x| ≤ Torus.cbNorm K φ := by
  have h0 : Torus.IsCk 0 φ := by
    unfold Torus.IsCk at hφ ⊢
    exact ContDiff.of_le hφ (by exact_mod_cast Nat.zero_le K)
  have h1 := Q54c.norm_le_cbNorm_zero h0 x
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  unfold Torus.cbNorm
  have hnn : ∀ j ∈ Finset.range (K + 1), 0 ≤ ⨆ y : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift φ) y‖ :=
    fun j _ => Real.iSup_nonneg fun y => norm_nonneg _
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun j hj _ => hnn j hj


theorem gfb2_transport_core (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
    (hF : ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
    (hE : S.EnergyMomentFinite P N X) (C a n1 : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (ha1 : 2 * a ≤ 1) (hn : 0 ≤ n1)
    (hpt : ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∀ x : Config d N, x ∉ collisionSet d N →
      torusWassersteinE 2 (empirical x) (withDensityReal (S.ρ N r)) ≤
        ENNReal.ofReal (C * (n1 + S.energyCompletion N x r ^ a))) :
    AEMeasurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
      ((torusWassersteinE 2 (empirical (X (Real.toNNReal r) ω))
        (withDensityReal (S.ρ N r))).toReal ^ 2)) P ∧
    ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
      ((torusWassersteinE 2 (empirical (X (Real.toNNReal r) ω))
        (withDensityReal (S.ρ N r))).toReal ^ 2)) ∂P ≤
      ENNReal.ofReal (S.T * (2 * C ^ 2 * (S.energyMoment P N X ^ (2 * a) + n1 ^ 2))) := by
  have hnn := (gf_energy_integral_moment_proof S M hMF N hN P X₀ W X hX hF hE).1
  obtain ⟨ℱ, W', hFil⟩ := hF
  have hT : 0 ≤ S.T := S.hT.le
  have hGm := gfb2_G_meas S M hMF N ℱ X hFil.progressive
  have hnnG : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) S.T, 0 ≤ gfb2_G S N X r ω := by
    filter_upwards [hnn] with ω hω r hr
    rw [← gfb2_G_eq S N X hr ω]; exact hω r hr
  have hZ := gfb2_progressive_meas ℱ X hFil.progressive hT
  have hWm : Measurable fun p : ℝ × Ω => torusWassersteinE 2 (empirical (X (Real.toNNReal (Q54c.clampT S.T p.1)) p.2))
      (withDensityReal (S.ρ N (Q54c.clampT S.T p.1))) := by
    have h := (gfb2_W_meas S M hMF N (by omega)).comp (hZ.prodMk measurable_fst)
    exact h
  have hfm : Measurable fun p : ℝ × Ω => ENNReal.ofReal ((torusWassersteinE 2
      (empirical (X (Real.toNNReal (Q54c.clampT S.T p.1)) p.2))
      (withDensityReal (S.ρ N (Q54c.clampT S.T p.1)))).toReal ^ 2) :=
    ENNReal.measurable_ofReal.comp (hWm.ennreal_toReal.pow_const 2)
  have hcongr : ∀ ω, ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
      ((torusWassersteinE 2 (empirical (X (Real.toNNReal r) ω))
        (withDensityReal (S.ρ N r))).toReal ^ 2) =
      ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal ((torusWassersteinE 2
      (empirical (X (Real.toNNReal (Q54c.clampT S.T r)) ω))
      (withDensityReal (S.ρ N (Q54c.clampT S.T r)))).toReal ^ 2) := fun ω =>
    setLIntegral_congr_fun measurableSet_Icc fun r hr => by simp only [Q54c.clampT_of_mem hr]
  refine ⟨?_, ?_⟩
  · simp only [hcongr]
    exact ((hfm.comp measurable_swap).lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) S.T))).aemeasurable
  simp only [hcongr]
  have hjm : Measurable fun p : ℝ × Ω =>
      ENNReal.ofReal (2 * C ^ 2 * (gfb2_G S N X p.1 p.2 ^ (2 * a) + n1 ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul ((hGm.pow_const (2 * a)).add_const _))
  have step1 : ∀ᵐ ω ∂P, ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal ((torusWassersteinE 2
      (empirical (X (Real.toNNReal (Q54c.clampT S.T r)) ω))
      (withDensityReal (S.ρ N (Q54c.clampT S.T r)))).toReal ^ 2) ≤
      ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (2 * C ^ 2 * (gfb2_G S N X r ω ^ (2 * a) + n1 ^ 2)) := by
    filter_upwards [hX.no_collision, hnnG] with ω hω hGω
    refine setLIntegral_mono' measurableSet_Icc fun r hr => ENNReal.ofReal_le_ofReal ?_
    simp only [Q54c.clampT_of_mem hr]
    have hcol : X (Real.toNNReal r) ω ∉ collisionSet d N := by
      refine hω (Real.toNNReal r) ?_
      rw [Real.coe_toNNReal r hr.1]; exact hr.2
    have h1 := hpt r hr _ hcol
    rw [← gfb2_G_eq S N X hr ω]
    have hG0 := hGω r hr
    rw [← gfb2_G_eq S N X hr ω] at hG0
    have hy : 0 ≤ C * (n1 + S.energyCompletion N (X (Real.toNNReal r) ω) r ^ a) :=
      mul_nonneg hC (add_nonneg hn (Real.rpow_nonneg hG0 a))
    have h2 := ENNReal.toReal_le_of_le_ofReal hy h1
    have h3 : (torusWassersteinE 2 (empirical (X (Real.toNNReal r) ω))
        (withDensityReal (S.ρ N r))).toReal ^ 2 ≤
        (C * (n1 + S.energyCompletion N (X (Real.toNNReal r) ω) r ^ a)) ^ 2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg h2 2
    refine h3.trans ?_
    have h4 : (S.energyCompletion N (X (Real.toNNReal r) ω) r ^ a) ^ 2 =
        S.energyCompletion N (X (Real.toNNReal r) ω) r ^ (2 * a) := by
      rw [mul_comm, Real.rpow_mul hG0, Real.rpow_two]
    nlinarith [sq_nonneg (n1 - S.energyCompletion N (X (Real.toNNReal r) ω) r ^ a), sq_nonneg C, h4]
  have hswap : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
      ENNReal.ofReal (2 * C ^ 2 * (gfb2_G S N X r ω ^ (2 * a) + n1 ^ 2))) ∂P =
      ∫⁻ r in Set.Icc (0 : ℝ) S.T, (∫⁻ ω,
        ENNReal.ofReal (2 * C ^ 2 * (gfb2_G S N X r ω ^ (2 * a) + n1 ^ 2)) ∂P) := by
    rw [lintegral_lintegral_swap]
    exact (hjm.comp measurable_swap).aemeasurable
  have hper : ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∫⁻ ω,
      ENNReal.ofReal (2 * C ^ 2 * (gfb2_G S N X r ω ^ (2 * a) + n1 ^ 2)) ∂P ≤
        ENNReal.ofReal (2 * C ^ 2 * (S.energyMoment P N X ^ (2 * a) + n1 ^ 2)) := by
    intro r hr
    have hGr : Measurable (gfb2_G S N X r) := Measurable.of_uncurry_left hGm
    have hfun : (fun ω => S.energyCompletion N (X (Real.toNNReal r) ω) r) = gfb2_G S N X r :=
      funext fun ω => gfb2_G_eq S N X hr ω
    have hGi : Integrable (gfb2_G S N X r) P := by rw [← hfun]; exact hE.1 r hr
    have hG0 : ∀ᵐ ω ∂P, 0 ≤ gfb2_G S N X r ω := by
      filter_upwards [hnnG] with ω hω using hω r hr
    have hjs := gfb2_jensen_rpow P _ hGr hG0 hGi (p := 2 * a) (by linarith) ha1
    have hui := hjs.1
    have hJ := hjs.2
    have hint : Integrable (fun ω => 2 * C ^ 2 * (gfb2_G S N X r ω ^ (2 * a) + n1 ^ 2)) P :=
      (hui.add (integrable_const _)).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hint (by
      filter_upwards [hG0] with ω hω
      exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C))
        (add_nonneg (Real.rpow_nonneg hω _) (sq_nonneg n1)))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_const_mul, integral_add hui (integrable_const _)]
    rw [integral_const]
    simp only [probReal_univ, one_smul, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one]
    have hsq : (∫ ω, gfb2_G S N X r ω ∂P) ^ (2 * a) ≤ S.energyMoment P N X ^ (2 * a) := by
      refine Real.rpow_le_rpow (integral_nonneg_of_ae hG0) ?_ (by linarith)
      have := le_ciSup hE.2 (⟨r, hr⟩ : Set.Icc (0 : ℝ) S.T)
      rw [← hfun]
      exact this
    have h2C : 0 ≤ 2 * C ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h2C
  calc ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal ((torusWassersteinE 2
      (empirical (X (Real.toNNReal (Q54c.clampT S.T r)) ω))
      (withDensityReal (S.ρ N (Q54c.clampT S.T r)))).toReal ^ 2)) ∂P
      ≤ ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
          ENNReal.ofReal (2 * C ^ 2 * (gfb2_G S N X r ω ^ (2 * a) + n1 ^ 2))) ∂P := lintegral_mono_ae step1
    _ = ∫⁻ r in Set.Icc (0 : ℝ) S.T, (∫⁻ ω,
        ENNReal.ofReal (2 * C ^ 2 * (gfb2_G S N X r ω ^ (2 * a) + n1 ^ 2)) ∂P) := hswap
    _ ≤ ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (2 * C ^ 2 * (S.energyMoment P N X ^ (2 * a) + n1 ^ 2)) :=
        setLIntegral_mono' measurableSet_Icc hper
    _ = ENNReal.ofReal (S.T * (2 * C ^ 2 * (S.energyMoment P N X ^ (2 * a) + n1 ^ 2))) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_mul hT, mul_comm]


theorem gf_transport_moment_proof (b : GeneralBounds d) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHyp → S.PosDensityWith b.c →
      ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P (S.dyn N) S.T X₀ W X →
        (∃ (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        S.EnergyMomentFinite P N X →
        AEMeasurable (fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
          ((torusWassersteinE 2 (empirical (X (Real.toNNReal r) ω))
            (withDensityReal (S.ρ N r))).toReal ^ 2)) P ∧
        ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
          ((torusWassersteinE 2 (empirical (X (Real.toNNReal r) ω))
            (withDensityReal (S.ρ N r))).toReal ^ 2)) ∂P ≤
          ENNReal.ofReal (C * (S.energyMoment P N X ^ ((2 : ℝ) / max 2 ((d : ℝ) - S.s)) +
            (N : ℝ) ^ (-(2 : ℝ) / d))) := by
  classical
  by_cases hex : ∃ S₀ : GeneralSetup d, S₀.s = b.s ∧ S₀.PosDensityWith b.c
  · obtain ⟨S₀, hs₀, hPD₀⟩ := hex
    have hd1 : 1 ≤ d := by have := S₀.hd; omega
    have hs0 : 0 ≤ b.s := hs₀ ▸ S₀.hs0
    have hsd : b.s < d := hs₀ ▸ S₀.hsd
    have hm0 : 0 < b.c := hPD₀.1
    obtain ⟨C₀min, h⟩ := Uniform.Q12.energy_W2_proof hd1 b.s hs0 hsd b.Λ b.c hm0
    refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
    obtain ⟨C, hCpos, hpt⟩ := h C₀ hC₀
    refine ⟨2 * C ^ 2 * (|b.T| + 1), by positivity, ?_⟩
    intro S hS hMF hPD N hN Ω _ P _ X₀ W X hX hF hE
    unfold GeneralSetup.Within at hS
    obtain ⟨hs, hT, hγ', hΛ, hβ, hC0, hV⟩ := hS
    have hC0' : S.C₀ = C₀ := hC0
    have hMF' : S.MFHypM (-1) := hMF
    set a : ℝ := (1 : ℝ) / max 2 ((d : ℝ) - b.s) with ha
    have hmax : (2 : ℝ) ≤ max 2 ((d : ℝ) - b.s) := le_max_left _ _
    have ha0 : 0 ≤ a := by rw [ha]; positivity
    have ha1 : 2 * a ≤ 1 := by
      rw [ha, mul_one_div, div_le_one (by linarith)]; exact hmax
    have hn : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    obtain ⟨hMFN, hReg⟩ := hMF' N
    have hpt' : ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∀ x : Config d N, x ∉ collisionSet d N →
        torusWassersteinE 2 (empirical x) (withDensityReal (S.ρ N r)) ≤
          ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / d) + S.energyCompletion N x r ^ a)) := by
      intro r hr x hx
      have hup : ∀ y, S.ρ N r y ≤ b.Λ := fun y =>
        (le_abs_self _).trans ((gfb2_sup_le_cbNorm (hReg r hr).1 y).trans ((hReg r hr).2.trans hΛ.le))
      have hlow : ∀ y, b.c ≤ S.ρ N r y := fun y => hPD.2 N r hr y
      have h1 := (hpt N hN (S.ρ N r) (hMFN.density r hr) hup hlow x hx).2
      unfold GeneralSetup.energyCompletion
      rw [hs, hC0']
      exact h1
    have hcore := gfb2_transport_core S (-1) hMF' N hN P X₀ W X hX hF hE C a _ hCpos.le ha0 ha1 hn hpt'
    refine ⟨hcore.1, hcore.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hnn := (gf_energy_integral_moment_proof S (-1) hMF' N hN P X₀ W X hX hF hE).1
    have hEm : 0 ≤ S.energyMoment P N X := by
      unfold GeneralSetup.energyMoment
      refine Real.iSup_nonneg fun t => integral_nonneg_of_ae ?_
      filter_upwards [hnn] with ω hω using hω t.1 t.2
    have hexp : (2 : ℝ) / max 2 ((d : ℝ) - S.s) = 2 * a := by
      rw [hs, ha]; ring
    have hnsq : ((N : ℝ) ^ (-(1 : ℝ) / d)) ^ 2 = (N : ℝ) ^ (-(2 : ℝ) / d) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1; push_cast; ring
    rw [hexp, ← hnsq]
    have hB : 0 ≤ 2 * C ^ 2 * (S.energyMoment P N X ^ (2 * a) + ((N : ℝ) ^ (-(1 : ℝ) / d)) ^ 2) :=
      mul_nonneg (by positivity) (add_nonneg (Real.rpow_nonneg hEm _) (sq_nonneg _))
    have hTle : S.T ≤ |b.T| + 1 := by rw [hT]; linarith [le_abs_self b.T]
    calc S.T * (2 * C ^ 2 * (S.energyMoment P N X ^ (2 * a) + ((N : ℝ) ^ (-(1 : ℝ) / d)) ^ 2))
        ≤ (|b.T| + 1) * (2 * C ^ 2 * (S.energyMoment P N X ^ (2 * a) + ((N : ℝ) ^ (-(1 : ℝ) / d)) ^ 2)) :=
          mul_le_mul_of_nonneg_right hTle hB
      _ = 2 * C ^ 2 * (|b.T| + 1) * (S.energyMoment P N X ^ (2 * a) + ((N : ℝ) ^ (-(1 : ℝ) / d)) ^ 2) := by ring
  · refine ⟨0, fun C₀ _ => ⟨1, one_pos, ?_⟩⟩
    intro S hS _ hPD
    exact absurd ⟨S, hS.1, hPD⟩ hex

example := (@gf_transport_moment_proof : type_of% @HRS.GF.gf_transport_moment)

end HRS.GF
