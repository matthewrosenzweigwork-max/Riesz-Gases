import HRS.Sections.AllTimeAux1

/-!
# ALLTIME (part 2): items 2 and 3 of Lemma 7.8 (`alltime_Lp`), uniform in `t`

See the chain plan in `AllTimeAux1.lean`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Sec7

variable {d : ℕ}

/-- Two-sided bounds for the partition functions `K_{N,b}(ρ)`, `b ∈ [βm,βp]`, uniform over a `C²`-bounded
family of positive probability densities (`movT_pressure_two_sided_C2_proof` at `θ = 0`, `h = 0`). -/
theorem alltime_Z_bounds (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (Λ₂ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk 2 ρ → (∀ x, c₀ ≤ ρ x) →
      Torus.cbNorm 2 ρ ≤ Λ₂ → ∀ N : ℕ, 2 ≤ N → ∀ b ∈ Set.Icc βm βp,
      Real.exp (-(C * N * deltaN d s N)) ≤ gibbsNormalizer (periodicRiesz d s) N b (withDensityReal ρ) ∧
      gibbsNormalizer (periodicRiesz d s) N b (withDensityReal ρ) ≤ Real.exp (C * N * deltaN d s N) := by
  obtain ⟨B0, hB0⟩ := periodicRiesz_ge_of_one_le (d := d) hd hs0 hsd
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + (B0 + 1) := fun z _ => by
    have := hB0 z; linarith
  obtain ⟨θ₀, C, hθ₀, hC0, H⟩ := movT_pressure_two_sided_C2_proof hd s hs0 hsd (B0 + 1) hw βm βp hβm
    c₀ hc₀ Λ₂ 0
  refine ⟨C, hC0, fun μ hμ hck hlow hcb N hN b hb => ?_⟩
  have hc : Continuous μ := mova_continuous_of_isCk hck
  have hb0 : 0 ≤ b := (hβm.trans_le hb.1).le
  have hN0 : 0 < N := by omega
  obtain ⟨h1, h2⟩ := H μ hμ hck hlow hcb (fun _ _ => 0) measurable_const (fun _ _ => rfl)
    (fun x y => by simp) N hN b hb 0 (by simp [hθ₀.le])
  rw [← movf_ofReal_gibbsNormalizer hd hs0 hsd hμ hc hN0 hb0] at h1 h2
  have hK : 0 < gibbsNormalizer (periodicRiesz d s) N b (withDensityReal μ) := by
    haveI := isProb_withDensityReal hμ
    obtain ⟨hm, Cc, hCc⟩ := movf_energy_facts hd hs0 hsd hμ hc hN0 (N := N)
    have := integral_exp_pos (μ := Measure.pi fun _ : Fin N => withDensityReal μ)
      (f := fun X : Config d N => -b * N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal μ))
      (by
        have := movf_exp_integrable (Measure.pi fun _ : Fin N => withDensityReal μ)
          (F := fun X : Config d N => N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal μ))
          (measurable_const.mul hm) (c := N * Cc) (fun X => by
            have := hCc X
            have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
            nlinarith) hb0
        refine this.congr (Eventually.of_forall fun X => ?_)
        simp only; ring_nf)
    exact this
  constructor
  · exact (ENNReal.ofReal_le_ofReal_iff hK.le).1 h1
  · exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 h2

/-- `L^q` norm of `dQ_{N,β}/dπ` for `q > 1`, `π = ρ^{⊗N}`, with explicit exponent `2 C N δ_N`. -/
theorem alltime_Lq_family (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hsd2 : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {q : ℝ}
    (hq : 1 < q) {c₀ : ℝ} (hc₀ : 0 < c₀) (Λ₂ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk 2 ρ → (∀ x, c₀ ≤ ρ x) →
      Torus.cbNorm 2 ρ ≤ Λ₂ → ∀ N : ℕ, 2 ≤ N →
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) ≪
          Measure.pi (fun _ : Fin N => withDensityReal ρ) ∧
      eLpNorm ((modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)).rnDeriv
          (Measure.pi (fun _ : Fin N => withDensityReal ρ))) (ENNReal.ofReal q)
        (Measure.pi (fun _ : Fin N => withDensityReal ρ)) ≤
        ENNReal.ofReal (Real.exp (2 * C * N * deltaN d s N)) := by
  have hqβ : β ≤ q * β := by nlinarith
  obtain ⟨C, hC0, hZ⟩ := alltime_Z_bounds hd hs0 hsd (βm := β) (βp := q * β) hβ hc₀ Λ₂
  refine ⟨C, hC0, fun ρ hρ hck hlow hcb N hN => ?_⟩
  have hN0 : 0 < N := by omega
  have hc : Continuous ρ := mova_continuous_of_isCk hck
  haveI := isProb_withDensityReal hρ
  obtain ⟨hm, Cc, hCc⟩ := movf_energy_facts hd hs0 hsd hρ hc hN0 (N := N)
  set P : Measure (Config d N) := Measure.pi fun _ : Fin N => withDensityReal ρ with hP
  set F : Config d N → ℝ := fun X =>
    (N : ℝ) * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ) with hFdef
  have hF : Measurable F := measurable_const.mul hm
  have hcF : ∀ X : Config d N, -((N : ℝ) * Cc) ≤ F X := fun X => by
    have := hCc X
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    simp only [hFdef]
    nlinarith
  have hQ : modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) =
      P.tilted (fun X => -β * F X) := by
    rw [movf_modGibbs_eq_tilted hd hs0 hsd hρ hc hN0 hβ.le]
    congr 1
    funext X; simp only [hFdef]; ring
  have hP0 : P = P.tilted (fun X => -(0 : ℝ) * F X) := by
    have : (fun X => -(0 : ℝ) * F X) = 0 := by funext X; simp
    rw [this, tilted_zero]
  have hqβ0 : 0 < q * β - (q - 1) * 0 := by nlinarith
  obtain ⟨hac, hnorm⟩ := movf_lp_tilted P hF hcF (b₀ := β) (b := 0) (p := q) hβ.le le_rfl hq
    (movf_exp_integrable P hF hcF (by simpa using hqβ0.le))
  rw [hQ]
  rw [← hP0] at hac hnorm
  refine ⟨hac, ?_⟩
  rw [hnorm]
  refine ENNReal.ofReal_le_ofReal ?_
  have hZb := hZ ρ hρ hck hlow hcb N hN β ⟨le_rfl, hqβ⟩
  have hZg := hZ ρ hρ hck hlow hcb N hN (q * β) ⟨hqβ, le_rfl⟩
  rw [movf_gibbsNormalizer_eq] at hZb hZg
  set A := C * N * deltaN d s N with hA
  have hA0 : 0 ≤ A := by
    have : 0 ≤ (N : ℝ) * deltaN d s N := by rw [alltime_Ndelta hsd2 hN0]; norm_num
    have h2 : A = C * ((N : ℝ) * deltaN d s N) := by rw [hA]; ring
    rw [h2]; exact mul_nonneg hC0 this
  set Zb := ∫ X : Config d N, Real.exp (-β * F X) ∂P with hZb'
  set Zg := ∫ X : Config d N, Real.exp (-(q * β - (q - 1) * 0) * F X) ∂P with hZg'
  have hZbe : Real.exp (-A) ≤ Zb := hZb.1
  have hZge : Zg ≤ Real.exp A := by
    have : Zg = ∫ X : Config d N, Real.exp (-(q * β) * F X) ∂P := by
      simp only [hZg']; congr 1; funext X; congr 2; ring
    rw [this]; exact hZg.2
  have hZbp : 0 < Zb := lt_of_lt_of_le (Real.exp_pos _) hZbe
  have hZgp : 0 < Zg := integral_exp_pos (movf_exp_integrable P hF hcF (by simpa using hqβ0.le))
  have hq0 : 0 < q := by linarith
  have h0 : ∫ X : Config d N, Real.exp (-(0 : ℝ) * F X) ∂P = 1 := by simp
  rw [h0, Real.one_rpow, one_mul]
  have e2 : Zb ^ (-q) ≤ Real.exp (A * q) := by
    rw [Real.rpow_neg hZbp.le, ← Real.inv_rpow hZbp.le, Real.exp_mul]
    refine Real.rpow_le_rpow (inv_nonneg.2 hZbp.le) ?_ hq0.le
    rw [inv_le_comm₀ hZbp (Real.exp_pos _), ← Real.exp_neg]
    exact hZbe
  have e3 : Zb ^ (-q) * Zg ≤ Real.exp (A * (q + 1)) := by
    calc Zb ^ (-q) * Zg ≤ Real.exp (A * q) * Real.exp A := by gcongr
      _ = Real.exp (A * (q + 1)) := by rw [← Real.exp_add]; congr 1; ring
  calc (Zb ^ (-q) * Zg) ^ (1 / q) ≤ (Real.exp (A * (q + 1))) ^ (1 / q) :=
        Real.rpow_le_rpow (by positivity) e3 (by positivity)
    _ = Real.exp (A * (q + 1) / q) := by rw [← Real.exp_mul]; congr 1; ring
    _ ≤ Real.exp (2 * C * N * deltaN d s N) := by
        refine Real.exp_le_exp.2 ?_
        have : A * (q + 1) / q ≤ 2 * A := by
          rw [div_le_iff₀ hq0]; nlinarith
        have e : 2 * C * N * deltaN d s N = 2 * A := by rw [hA]; ring
        rw [e]; exact this

/-- Item 2 of Lemma 7.8. -/
theorem alltime_item2 (R : Regime d) :
    ∀ q : ℝ, 1 ≤ q → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
      modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t)) ≪
          Measure.pi (fun _ : Fin N => withDensityReal (R.ρ t)) ∧
        eLpNorm ((modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))).rnDeriv
            (Measure.pi (fun _ : Fin N => withDensityReal (R.ρ t)))) (ENNReal.ofReal q)
          (Measure.pi (fun _ : Fin N => withDensityReal (R.ρ t))) ≤ ENNReal.ofReal C := by
  intro q hq
  have hd1 : 1 ≤ d := by have := R.hd; omega
  have hs0 := alltime_hs0 R
  have hsd := alltime_hsd R
  have hsd2 : R.D.s < (d : ℝ) / 2 := R.hs
  obtain ⟨c₀, Λ₂, hc₀, hunif⟩ := movT_traj_uniform_proof R.D.s R.β R.D.V R.ρ₀ R.ρ hs0 hsd R.hβ R.hV
    R.hρ₀ (alltime_glob R)
  obtain ⟨C, hC0, hC⟩ := alltime_Lq_family hd1 hs0 hsd hsd2 R.hβ (q := q + 1) (by linarith) hc₀ Λ₂
  refine ⟨Real.exp (2 * C), fun N hN t ht => ?_⟩
  have hN0 : 0 < N := by omega
  have htr := alltime_traj R t
  obtain ⟨hac, hn⟩ := hC (R.ρ t) (htr.mf.density t ⟨ht, le_rfl⟩) (htr.ck t ⟨ht, le_rfl⟩)
    (hunif t ht).1 (hunif t ht).2 N hN
  refine ⟨hac, ?_⟩
  haveI := isProb_withDensityReal (htr.mf.density t ⟨ht, le_rfl⟩)
  refine (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))).trans (hn.trans ?_)
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  rw [mul_assoc, mul_assoc, alltime_Ndelta hsd2 hN0, mul_one]


/-- Item 3 of Lemma 7.8 (exponential pair estimate, uniform in `t`), with the diagonal repair. -/
theorem alltime_item3 (R : Regime d) (c : ℝ) (hc : EnvelopeConst (d := d) R.D.s c) :
    ∀ B : ℝ, ∃ cB CB : ℝ, 0 < cB ∧ ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
      ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
        (∀ x y, x ≠ y → |h x y| ≤ B * (periodicRiesz d R.D.s (x - y) + c)) →
        ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (cB * N *
            |modulatedEnergy h X (withDensityReal (R.ρ t))|))
          ∂(modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal (R.ρ t))) ≤
          ENNReal.ofReal CB := by
  intro B
  have hd1 : 1 ≤ d := by have := R.hd; omega
  have hs0 := alltime_hs0 R
  have hsd := alltime_hsd R
  have hsd2 : R.D.s < (d : ℝ) / 2 := R.hs
  obtain ⟨c₀, Λ₂, hc₀, hunif⟩ := movT_traj_uniform_proof R.D.s R.β R.D.V R.ρ₀ R.ρ hs0 hsd R.hβ R.hV
    R.hρ₀ (alltime_glob R)
  obtain ⟨m₀, M₀, hm₀, hbd⟩ := R.bounds
  set cs : ℝ := max c (1 - periodicRiesz d R.D.s 0) with hcs
  set B' : ℝ := max B 0 with hB'
  have hcsc : c ≤ cs := le_max_left _ _
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d R.D.s z + cs := fun z hz => by
    have := hc z hz; linarith
  have hw1 : ∀ z : Torus d, 1 ≤ periodicRiesz d R.D.s z + cs := fun z => by
    by_cases hz : z = 0
    · subst hz
      have : 1 - periodicRiesz d R.D.s 0 ≤ cs := le_max_right _ _
      linarith
    · exact hw z hz
  obtain ⟨θ₀, C, hθ₀, hC0, hP⟩ := movT_pressure_two_sided_C2_proof hd1 R.D.s hs0 hsd cs hw R.β R.β R.hβ
    c₀ hc₀ Λ₂ B'
  refine ⟨R.β * θ₀, Real.exp (2 * C + 1), mul_pos R.hβ hθ₀, fun N hN t ht h hm hsym hdom => ?_⟩
  have hN0 : 0 < N := by omega
  have htr := alltime_traj R t
  have hρd := htr.mf.density t ⟨ht, le_rfl⟩
  have hρck := htr.ck t ⟨ht, le_rfl⟩
  haveI := isProb_withDensityReal hρd
  set ρ := R.ρ t with hρ
  -- the diagonal-repaired kernel
  set h' : Torus d → Torus d → ℝ := fun x y => if x = y then 0 else h x y with hh'
  have hm' : Measurable (Function.uncurry h') := by
    have : Function.uncurry h' = fun p : Torus d × Torus d => if p.1 = p.2 then 0 else Function.uncurry h p := by
      funext p; rfl
    rw [this]
    exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const hm
  have hsym' : ∀ x y, h' x y = h' y x := fun x y => by
    by_cases hxy : x = y
    · subst hxy; rfl
    · simp only [hh', if_neg hxy, if_neg (Ne.symm hxy)]; exact hsym x y
  have hdom' : ∀ x y, |h' x y| ≤ B' * (periodicRiesz d R.D.s (x - y) + cs) := fun x y => by
    by_cases hxy : x = y
    · simp only [hh', if_pos hxy, abs_zero]
      have := hw1 (x - y)
      have hB'0 : 0 ≤ B' := le_max_right _ _
      nlinarith
    · simp only [hh', if_neg hxy]
      have h1 := hdom x y hxy
      have hwpos : 0 ≤ periodicRiesz d R.D.s (x - y) + c := by
        have := hc (x - y) (sub_ne_zero.2 hxy); linarith
      have hB1 : B ≤ B' := le_max_left _ _
      have hB'0 : 0 ≤ B' := le_max_right _ _
      calc |h x y| ≤ B * (periodicRiesz d R.D.s (x - y) + c) := h1
        _ ≤ B' * (periodicRiesz d R.D.s (x - y) + c) := mul_le_mul_of_nonneg_right hB1 hwpos
        _ ≤ B' * (periodicRiesz d R.D.s (x - y) + cs) :=
            mul_le_mul_of_nonneg_left (by linarith) hB'0
  have hρΛ : ∀ x, ρ x ≤ max M₀ 0 := fun x => ((hbd t ht x).2).trans (le_max_left _ _)
  obtain ⟨hgR, hhR⟩ := rowOK_g_h hd1 R.D.s hs0 hsd cs hw B' (le_max_right _ _) hρΛ hm' hdom'
  have hδ : 1 ≤ (N : ℝ) * deltaN d R.D.s N := by rw [alltime_Ndelta hsd2 hN0]
  have hP' := hP ρ hρd hρck (hunif t ht).1 (hunif t ht).2 h' hm' hsym' hdom' N hN R.β ⟨le_rfl, le_rfl⟩
  obtain ⟨hE, -⟩ := moments_of_pressure (N := N) (μ := withDensityReal ρ) (g := periodicRiesz d R.D.s)
    (h := h') hgR hhR (δ := deltaN d R.D.s N) (C := C) (θ₀ := θ₀) (βm := R.β) (β := R.β) hδ hC0 hθ₀ R.hβ
    le_rfl hP'
  -- a.e. equality of the two energies
  have hcont : Continuous ρ := mova_continuous_of_isCk hρck
  have hgibbs : modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal ρ) ≪
      Measure.pi (fun _ : Fin N => withDensityReal ρ) := by
    rw [movf_modGibbs_eq_tilted hd1 hs0 hsd hρd hcont hN0 R.hβ.le]
    exact tilted_absolutelyContinuous _ _
  have hae : ∀ᵐ X ∂(modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal ρ)),
      ∀ i j, i ≠ j → X i ≠ X j :=
    hgibbs.ae_le (ae_injective_pi (withDensityReal_singleton hd1 ρ))
  have heq : ∀ᵐ X ∂(modulatedGibbs (periodicRiesz d R.D.s) N R.β (withDensityReal ρ)),
      ENNReal.ofReal (Real.exp (R.β * θ₀ * N * |modulatedEnergy h X (withDensityReal ρ)|)) =
      ENNReal.ofReal (Real.exp (R.β * θ₀ * N * |modulatedEnergy h' X (withDensityReal ρ)|)) := by
    filter_upwards [hae] with X hX
    rw [modulatedEnergy_congr_offdiag (withDensityReal_singleton hd1 ρ)
      (k₁ := h) (k₂ := h') (fun x y hxy => by simp only [hh', if_neg hxy]) X hX]
  rw [lintegral_congr_ae heq]
  refine hE.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  rw [mul_assoc, alltime_Ndelta hsd2 hN0, mul_one]

end Sec7

end HRS

end
