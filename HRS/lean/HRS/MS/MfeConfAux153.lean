import HRS.MS.MfeConfAux152

/-!
# S.B.1 (SB5), packet R3c (part 3): Gronwall along one conditioned flow
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- `H(law X_t|Q_t)` (real part) -/
def sb1Hq {Ω : Type*} [MeasurableSpace Ω] (D : Whole.WholeDyn d) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (P : Measure Ω)
    (X : ℝ≥0 → Ω → Whole.EucConfig d N) (t : ℝ) : ℝ :=
  (relEntropy (P.map (X t.toNNReal)) (sb1Q D N ρ t)).toReal

def sb1logK (D : Whole.WholeDyn d) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (t : ℝ) : ℝ :=
  Real.log (Whole.gibbsNormalizer (Whole.rieszKernel d D.s) N D.invβ⁻¹ (Whole.withDensityReal (ρ t)))

/-- the Gronwall variable `u(t) = H - log K + βN C_E` -/
def sb1uu {Ω : Type*} [MeasurableSpace Ω] (D : Whole.WholeDyn d) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (P : Measure Ω)
    (X : ℝ≥0 → Ω → Whole.EucConfig d N) (CE t : ℝ) : ℝ :=
  sb1Hq D N ρ P X t - sb1logK D N ρ t + D.invβ⁻¹ * N * CE

section One

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)

include H

theorem sb1_pj_gronwall (hT : 0 ≤ T) (hN : 1 ≤ N) (hβ : 0 < D.invβ) (Kf : ℝ → ℝ) (hKi : IntegrableOn Kf (Set.Icc 0 T))
    (hLip : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (Kf t)) {a b : ℝ}
    (hco : Sb1Coarse D N T ρ a b) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X₀ : Ω → Whole.EucConfig d N} {X : ℝ≥0 → Ω → Whole.EucConfig d N} (hXm : ∀ t, Measurable (X t))
    (hx0 : P.map X₀ = P.map (X 0))
    (hnc : ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ζ ∉ eucCollisionSet d N)
    (hS : SbMovEnt D N T ρ P X₀ X) (hfin0 : relEntropy (P.map X₀) (sb1Q D N ρ 0) ≠ ⊤) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (sb1En (Whole.rieszKernel d D.s) (ρ t) : Whole.EucConfig d N → ℝ) (P.map (X t.toNNReal)) ∧
      D.invβ⁻¹ * N * ((∫ Z, sb1En (Whole.rieszKernel d D.s) (ρ t) Z ∂(P.map (X t.toNNReal))) +
        sb1CE d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)) ≤
        sb1uu D N ρ P X (sb1CE d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)) t ∧
      sb1uu D N ρ P X (sb1CE d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)) t + 1 ≤
        (sb1uu D N ρ P X (sb1CE d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)) 0 + 1) *
          Real.exp ((a + D.invβ⁻¹ * N * b) * ∫ r in Set.Icc (0 : ℝ) t, Kf r) ∧
      Integrable (sb1CN D N ρ t) (P.map (X t.toNNReal)) ∧
      |∫ Z, sb1CN D N ρ t Z ∂(P.map (X t.toNNReal))| ≤ Kf t * (a * (∫ Z, sb1En (Whole.rieszKernel d D.s) (ρ t) Z ∂(P.map (X t.toNNReal))) + b) := by
  obtain ⟨ha, hb, hcoar⟩ := hco
  have hd := H.tr.hd
  have hβ0 : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hκ : 0 < D.invβ⁻¹ * N := mul_pos hβ0 hn
  set κ : ℝ := D.invβ⁻¹ * N with hκdef
  set M1 : ℝ := C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y with hM1
  set CE : ℝ := sb1CE d D.s C3 M1 with hCE
  have hCE0 : 0 ≤ CE := sb1CE_nonneg (H.rho hd (r := 0) ⟨le_rfl, hT⟩)
  haveI hprob : ∀ r : ℝ, IsProbabilityMeasure (P.map (X r.toNNReal)) := fun r =>
    (Measure.isProbabilityMeasure_map_iff (hXm _).aemeasurable).2 inferInstance
  obtain ⟨hSM, hCQ⟩ := hS hfin0
  have hLogK := sb1_logK_main H hT hβ hN Kf hKi hLip
  have hLs : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ Kf s ∧
      ∀ x y, ‖Whole.mfeTransportW D (ρ s) x - Whole.mfeTransportW D (ρ s) y‖ ≤ Kf s * ‖x - y‖ :=
    fun s hs => sb1_lip_of_hasLip (hLip s hs)
  have hsub : ∀ t ∈ Set.Icc (0 : ℝ) T, Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := fun t ht => Set.Icc_subset_Icc le_rfl ht.2
  -- per-time facts
  have hTime : ∀ t ∈ Set.Icc (0 : ℝ) T, _ := fun t ht => sb1_pj_ent H hN hβ ht (hSM t ht).1
  have hCN : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (sb1CN D N ρ t) (P.map (X t.toNNReal)) := by
    intro t ht
    have hSrc := (hSM t ht).2.1 t ⟨ht.1, le_rfl⟩
    have e : sb1CN D N ρ t = fun Z => sb1EQ D N ρ t - κ⁻¹ * sb1Src D N ρ t Z := by
      funext Z; unfold sb1Src; rw [← hκdef]; field_simp; ring
    rw [e]
    exact (integrable_const _).sub (hSrc.const_mul _)
  set g : ℝ → ℝ := fun t => ∫ Z, sb1CN D N ρ t Z ∂(P.map (X t.toNNReal)) with hg
  set S : ℝ → ℝ := fun t => ∫ Z, sb1Src D N ρ t Z ∂(P.map (X t.toNNReal)) with hSdef
  set G : ℝ → ℝ := fun t => S t - κ * sb1EQ D N ρ t with hGdef
  have hGg : ∀ t ∈ Set.Icc (0 : ℝ) T, G t = -κ * g t := by
    intro t ht
    simp only [hGdef, hSdef, hg]
    unfold sb1Src
    rw [integral_const_mul, integral_sub (hCN t ht) (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
    ring
  have hLow : ∀ t ∈ Set.Icc (0 : ℝ) T, -CE ≤ ∫ Z, sb1En (Whole.rieszKernel d D.s) (ρ t) Z ∂(P.map (X t.toNNReal)) := by
    intro t ht
    have := integral_mono (integrable_const (-CE)) (hTime t ht).1 (fun Z => sb1_En_lower hd H.tr.hs0 H.tr.hsd hN (H.rho hd ht) Z)
    simpa using this
  have hu0 : ∀ t ∈ Set.Icc (0 : ℝ) T, κ * ((∫ Z, sb1En (Whole.rieszKernel d D.s) (ρ t) Z ∂(P.map (X t.toNNReal))) + CE) ≤
      sb1uu D N ρ P X CE t := by
    intro t ht
    have := (hTime t ht).2
    unfold sb1uu sb1Hq sb1logK
    nlinarith
  have hgb : ∀ t ∈ Set.Icc (0 : ℝ) T, |g t| ≤ Kf t * (a * (∫ Z, sb1En (Whole.rieszKernel d D.s) (ρ t) Z ∂(P.map (X t.toNNReal))) + b) := by
    intro t ht
    have hEn := (hTime t ht).1
    have hint : Integrable (fun Z => Kf t * (a * sb1En (Whole.rieszKernel d D.s) (ρ t) Z + b)) (P.map (X t.toNNReal)) :=
      ((hEn.const_mul a).add (integrable_const b)).const_mul _
    have h1 := abs_integral_le_integral_abs (μ := P.map (X t.toNNReal)) (f := sb1CN D N ρ t)
    have h2 : ∫ Z, |sb1CN D N ρ t Z| ∂(P.map (X t.toNNReal)) ≤
        ∫ Z, Kf t * (a * sb1En (Whole.rieszKernel d D.s) (ρ t) Z + b) ∂(P.map (X t.toNNReal)) := by
      refine integral_mono_ae (hCN t ht).abs hint ?_
      filter_upwards [sb1_coll_ae hXm hnc ht] with Z hZ
      exact hcoar t ht (Kf t) (hLs t ht).1 (hLs t ht).2 Z hZ
    rw [integral_const_mul, integral_add (hEn.const_mul a) (integrable_const b), integral_const_mul] at h2
    simp only [integral_const, probReal_univ, one_smul] at h2
    exact h1.trans h2
  have hSi : ∀ t ∈ Set.Icc (0 : ℝ) T, IntegrableOn S (Set.Icc 0 t) := fun t ht => (hSM t ht).2.2.1
  have hEQi : IntegrableOn (sb1EQ D N ρ) (Set.Icc 0 T) := hLogK.1
  have hGi : IntegrableOn G (Set.Icc 0 T) := (hSi T ⟨hT, le_rfl⟩).sub (hEQi.const_mul κ)
  have hHq0 : sb1Hq D N ρ P X 0 = (relEntropy (P.map X₀) (sb1Q D N ρ 0)).toReal := by
    simp only [sb1Hq, Real.toNNReal_zero, hx0]
  have hu : ∀ t ∈ Set.Icc (0 : ℝ) T, sb1uu D N ρ P X CE t + 1 ≤
      (sb1uu D N ρ P X CE 0 + 1) + ∫ r in Set.Icc (0 : ℝ) t, G r := by
    intro t ht
    have hle := (hSM t ht).2.2.2
    have hl := hLogK.2 t ht
    have hEQt : IntegrableOn (sb1EQ D N ρ) (Set.Icc 0 t) := hEQi.mono_set (hsub t ht)
    have hI : ∫ r in Set.Icc (0 : ℝ) t, G r = (∫ r in Set.Icc (0 : ℝ) t, S r) - κ * ∫ r in Set.Icc (0 : ℝ) t, sb1EQ D N ρ r := by
      simp only [hGdef]
      rw [integral_sub (hSi t ht) (hEQt.const_mul κ), integral_const_mul]
    rw [hI]
    have h0 : sb1uu D N ρ P X CE 0 = sb1Hq D N ρ P X 0 - sb1logK D N ρ 0 + κ * CE := rfl
    have h1 : sb1uu D N ρ P X CE t = sb1Hq D N ρ P X t - sb1logK D N ρ t + κ * CE := rfl
    have h2 : sb1Hq D N ρ P X t ≤ sb1Hq D N ρ P X 0 + ∫ r in Set.Icc (0 : ℝ) t, S r := by
      rw [hHq0]; exact hle
    have h3 : sb1logK D N ρ t - sb1logK D N ρ 0 = κ * ∫ r in Set.Icc (0 : ℝ) t, sb1EQ D N ρ r := hl
    linarith
  have hnn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ sb1uu D N ρ P X CE t := by
    intro t ht
    have h1 := hu0 t ht
    have h2 := hLow t ht
    nlinarith
  have hGu : ∀ r ∈ Set.Icc (0 : ℝ) T, G r ≤ ((a + κ * b) * Kf r) * (sb1uu D N ρ P X CE r + 1) := by
    intro r hr
    rw [hGg r hr]
    have h1 := hgb r hr
    have h2 := (hTime r hr).2
    have hK0 := (hLs r hr).1
    have hu1 := hnn r hr
    have h3 : sb1uu D N ρ P X CE r = sb1Hq D N ρ P X r - sb1logK D N ρ r + κ * CE := rfl
    have h4 : -g r ≤ |g r| := neg_le_abs _
    have h5 : κ * (-g r) ≤ κ * (Kf r * (a * (∫ Z, sb1En (Whole.rieszKernel d D.s) (ρ r) Z ∂(P.map (X r.toNNReal))) + b)) :=
      mul_le_mul_of_nonneg_left (h4.trans h1) hκ.le
    set I := ∫ Z, sb1En (Whole.rieszKernel d D.s) (ρ r) Z ∂(P.map (X r.toNNReal)) with hI
    have h6 : κ * (Kf r * (a * I + b)) = Kf r * (a * (κ * I) + κ * b) := by ring
    have h7 : a * (κ * I) ≤ a * (sb1uu D N ρ P X CE r) := by
      refine mul_le_mul_of_nonneg_left ?_ ha.le
      have : 0 ≤ κ * CE := mul_nonneg hκ.le hCE0
      unfold sb1Hq sb1logK at h3
      linarith
    have h8 : Kf r * (a * (κ * I) + κ * b) ≤ Kf r * (a * sb1uu D N ρ P X CE r + κ * b) :=
      mul_le_mul_of_nonneg_left (by linarith) hK0
    have h9 : a * sb1uu D N ρ P X CE r + κ * b ≤ (a + κ * b) * (sb1uu D N ρ P X CE r + 1) := by
      nlinarith [mul_nonneg (mul_nonneg hκ.le hb) hu1]
    have h10 := mul_le_mul_of_nonneg_left h9 hK0
    nlinarith
  have hgr := movspec_gronwall_var (T := T) (u0 := sb1uu D N ρ P X CE 0 + 1) (a := fun r => (a + κ * b) * Kf r)
    (G := G) (u := fun t => sb1uu D N ρ P X CE t + 1)
    (fun r hr => mul_nonneg (by have := mul_nonneg hκ.le hb; linarith) (hLs r hr).1) (hKi.const_mul _) hGi hu hGu
  intro t ht
  refine ⟨(hTime t ht).1, hu0 t ht, ?_, hCN t ht, ?_⟩
  · have := hgr t ht
    rwa [integral_const_mul] at this
  · exact (hgb t ht)

end One

end HRS.MS.MfeConf
