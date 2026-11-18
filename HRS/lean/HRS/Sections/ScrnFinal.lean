import HRS.Sections.ScrnAux45

/-!
# Packet SCRN: Proposition 6.1 (final, statements verbatim)

`screening_comparison_proof` : `HRS.screening_comparison` (Sec6.lean) via `scrn_instance` (`ℓ ≤ 1`) and the trivial bound
`smoothDist ≤ 2` (`ℓ > 1`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal FourierTransform

noncomputable section

namespace HRS

variable {d : ℕ}

open HRS.Main.A8P

theorem screening_comparison_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hsd : s < d) (p : ℕ) (φ : Fin p → Euc d → ℝ)
    (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a)) (x₀ : Euc d)
    (bm bp : ℝ) (hbm : 0 < bm) (hbmp : bm ≤ bp) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 ≤ C ∧
      (∀ N : ℕ, 2 ≤ N → ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (volume : Measure (Torus d)) + oN d s C₀ N) ∧
      ∀ (N : ℕ), 2 ≤ N → ∀ (βN : ℝ) (hβN : 0 < βN) (ℓ b : ℝ), 0 < ℓ →
        βN * ℓ ^ ((d : ℝ) - s) ∈ Set.Icc bm bp → b ∈ Set.Icc bm bp →
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
          IsVectorBrownian P W →
          ProbabilityTheory.IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P →
          P.map X₀ = Measure.pi (fun _ : Fin N => (volume : Measure (Torus d))) →
          (∀ T' : ℝ, 0 ≤ T' →
            IsStrongSolution P (PDE.mfData d s hs0 hsd (fun _ => 0) βN hβN) T' X₀ W X) →
          (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
            (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
          ∀ t : Fin p → ℝ, (∀ a, 0 ≤ t a) →
            smoothDist 3
                (law P fun ω => (WithLp.toLp 2 fun a =>
                  linCoord (volume : Measure (Torus d)) (mesoTest d ℓ x₀ (φ a))
                    (X (ℓ ^ (2 - ((d : ℝ) - s)) * t a).toNNReal ω) : EuclideanSpace ℝ (Fin p)))
                (ProbabilityTheory.multivariateGaussian 0 (mesoCovMatrix d s b t φ)) ≤
              C * ((N : ℝ) ^ (-(1 : ℝ) / 2) * ℓ ^ (-(d : ℝ) / 2) +
                Real.sqrt N * oN d s C₀ N * ℓ ^ (-(d : ℝ) / 2 - max ((d : ℝ) - s) 2) +
                (N : ℝ) ^ (-(1 : ℝ) / d) * ℓ ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2) +
                Real.sqrt (oN d s C₀ N) *
                  ℓ ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 + min ((d : ℝ) - s) 2) +
                ℓ + |βN * ℓ ^ ((d : ℝ) - s) - b|) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₀, Cq, hC₀, hCq, hcom⟩ := HRS.Main.A8P.a8p_commSpec hd1 hs0 hsd
  obtain ⟨C1, hC1, hinst⟩ := scrn_instance hd hs0 hsd φ hφ x₀ hbm hbmp hC₀ hcom hCq.le
  refine ⟨C₀, max C1 2, hC₀, le_max_of_le_right (by norm_num), ?_, ?_⟩
  · intro N hN X hX
    have h := (hcom 1 le_rfl N hN (fun _ => (1 : ℝ)) scrn_isProbDensity_one (fun _ => le_rfl) X hX).1
    rw [scrn_withDensityReal_one, scrn_oNΛ_one] at h
    exact h
  · intro N hN βN hβN ℓ b hℓ hβb hb Ω _ P _ X₀ W X hW hI hlaw hsol hfilt t ht
    have hflow : ScrnFlow d hs0 hsd βN hβN N P X₀ W X := ⟨hW, hI, hlaw, hsol, hfilt⟩
    have hN1 : 1 ≤ N := by omega
    have hoN : 0 ≤ oN d s C₀ N := scrn_oN_nonneg hC₀ hN1
    have hP1 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) * ℓ ^ (-(d : ℝ) / 2) := by positivity
    have hP2 : 0 ≤ Real.sqrt N * oN d s C₀ N * ℓ ^ (-(d : ℝ) / 2 - max ((d : ℝ) - s) 2) := by
      positivity
    have hP3 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) * ℓ ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2) := by
      positivity
    have hP4 : 0 ≤ Real.sqrt (oN d s C₀ N) *
        ℓ ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 + min ((d : ℝ) - s) 2) := by positivity
    have hP5 : 0 ≤ |βN * ℓ ^ ((d : ℝ) - s) - b| := abs_nonneg _
    by_cases hℓ1 : ℓ ≤ 1
    · refine (hinst hN hβN hℓ hℓ1 hβb hb hflow t ht).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
      linarith
    · push_neg at hℓ1
      have h2 : smoothDist 3
          (law P fun ω => (WithLp.toLp 2 fun a =>
            linCoord (volume : Measure (Torus d)) (mesoTest d ℓ x₀ (φ a))
              (X (ℓ ^ (2 - ((d : ℝ) - s)) * t a).toNNReal ω) : EuclideanSpace ℝ (Fin p)))
          (ProbabilityTheory.multivariateGaussian 0 (mesoCovMatrix d s b t φ)) ≤ 2 := by
        refine (smoothDist_le 3 _ _).trans ?_
        have h1 : ((law P fun ω => (WithLp.toLp 2 fun a =>
            linCoord (volume : Measure (Torus d)) (mesoTest d ℓ x₀ (φ a))
              (X (ℓ ^ (2 - ((d : ℝ) - s)) * t a).toNNReal ω) : EuclideanSpace ℝ (Fin p)))
                Set.univ).toReal ≤ 1 := by
          unfold law
          by_cases hm : AEMeasurable (fun ω => (WithLp.toLp 2 fun a =>
            linCoord (volume : Measure (Torus d)) (mesoTest d ℓ x₀ (φ a))
              (X (ℓ ^ (2 - ((d : ℝ) - s)) * t a).toNNReal ω) : EuclideanSpace ℝ (Fin p))) P
          · rw [Measure.map_apply_of_aemeasurable hm MeasurableSet.univ]
            simp
          · rw [Measure.map_of_not_aemeasurable_of_ne_zero hm (IsProbabilityMeasure.ne_zero P)]
            simp
        have h3 : ((ProbabilityTheory.multivariateGaussian 0 (mesoCovMatrix d s b t φ) :
            Measure (EuclideanSpace ℝ (Fin p))) Set.univ).toReal = 1 := by simp
        linarith
      refine h2.trans ?_
      have hC2 : (2 : ℝ) ≤ max C1 2 := le_max_right _ _
      set E : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 2) * ℓ ^ (-(d : ℝ) / 2) +
                Real.sqrt N * oN d s C₀ N * ℓ ^ (-(d : ℝ) / 2 - max ((d : ℝ) - s) 2) +
                (N : ℝ) ^ (-(1 : ℝ) / d) * ℓ ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2) +
                Real.sqrt (oN d s C₀ N) *
                  ℓ ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 + min ((d : ℝ) - s) 2) +
                ℓ + |βN * ℓ ^ ((d : ℝ) - s) - b| with hE
      have hE1 : 1 ≤ E := by simp only [hE]; linarith
      nlinarith

example := (@screening_comparison_proof : type_of% @screening_comparison)

theorem screening_stationary_limit_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hsd : s < d) (p : ℕ) (φ : Fin p → Euc d → ℝ)
    (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a)) (x₀ : Euc d)
    (κ : ℝ) (hκ : 0 < κ) (hκm : κ < kappaMax d s) (b : ℝ) (hb : 0 < b) (βN : ℕ → ℝ)
    (hβN : ∀ n, 0 < βN n)
    (hbN : Tendsto (fun n : ℕ => βN n * (((n + 2 : ℕ) : ℝ) ^ (-κ)) ^ ((d : ℝ) - s)) atTop (𝓝 b))
    (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (X₀ : ∀ n, Ω n → Config d (n + 2))
    (W : ∀ n, ℝ≥0 → Ω n → (Fin (n + 2) → Euc d)) (X : ∀ n, ℝ≥0 → Ω n → Config d (n + 2))
    (hW : ∀ n, IsVectorBrownian (P n) (W n))
    (hI : ∀ n, ProbabilityTheory.IndepFun (X₀ n) (fun ω => fun t : ℝ≥0 => W n t ω) (P n))
    (hX₀ : ∀ n, (P n).map (X₀ n) = Measure.pi (fun _ : Fin (n + 2) => (volume : Measure (Torus d))))
    (hsol : ∀ n, ∀ T' : ℝ, 0 ≤ T' →
      IsStrongSolution (P n) (PDE.mfData d s hs0 hsd (fun _ => 0) (βN n) (hβN n)) T' (X₀ n) (W n)
        (X n))
    (hfilt : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (inferInstance : MeasurableSpace (Ω n)))
      (W' : ℝ≥0 → Ω n → (Fin (n + 2) × Fin d) → ℝ), IsFilteredSolution (P n) ℱ W' (W n) (X n))
    (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hu : Tendsto u atTop atTop) (t : Fin p → ℝ)
    (ht : ∀ a, 0 ≤ t a) :
    Tendsto (fun n : ℕ => smoothDist 3
      (law (P n) fun ω => (WithLp.toLp 2 fun a =>
        linCoord (volume : Measure (Torus d))
          (mesoTest d (((n + 2 : ℕ) : ℝ) ^ (-κ)) x₀ (φ a))
          (X n ((((n + 2 : ℕ) : ℝ) ^ (-κ)) ^ (2 - ((d : ℝ) - s)) * (u n + t a)).toNNReal ω) :
            EuclideanSpace ℝ (Fin p)))
      (ProbabilityTheory.multivariateGaussian 0 (mesoStatCovMatrix d s b t φ))) atTop (𝓝 0) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₀, Cq, hC₀, hCq, hcom⟩ := HRS.Main.A8P.a8p_commSpec hd1 hs0 hsd
  have hb2 : 0 < b / 2 := by positivity
  obtain ⟨C1, hC1, hinst⟩ := scrn_instance hd hs0 hsd φ hφ x₀ (bm := b / 2) (bp := 2 * b) hb2
    (by linarith) hC₀ hcom hCq.le
  have hNpos : ∀ n : ℕ, (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := fun n => by positivity
  have hℓpos : ∀ n : ℕ, 0 < (((n + 2 : ℕ) : ℝ)) ^ (-κ) := fun n => Real.rpow_pos_of_pos (hNpos n) _
  have hℓle : ∀ n : ℕ, (((n + 2 : ℕ) : ℝ)) ^ (-κ) ≤ 1 := fun n =>
    Real.rpow_le_one_of_one_le_of_nonpos (by
      have : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 2)
      exact this) (by linarith)
  have hbev : ∀ᶠ n : ℕ in atTop, βN n * ((((n + 2 : ℕ) : ℝ)) ^ (-κ)) ^ ((d : ℝ) - s) ∈
      Set.Icc (b / 2) (2 * b) :=
    hbN.eventually (Icc_mem_nhds (by linarith) (by linarith))
  have hErr := (screening_error_tendsto hd hs0 hs C₀ hC₀ κ hκ hκm).comp (tendsto_add_atTop_nat 2)
  have hAbs : Tendsto (fun n : ℕ => |βN n * ((((n + 2 : ℕ) : ℝ)) ^ (-κ)) ^ ((d : ℝ) - s) - b|)
      atTop (𝓝 0) := by
    have := (hbN.sub_const b).abs
    simpa using this
  have hG := scrn_stat_gauss_tendsto hd hs0 hsd φ hφ hb t ht hu0 hu
  have hlim := ((hErr.add hAbs).const_mul C1).add hG
  rw [show C1 * (0 + 0) + 0 = (0 : ℝ) by ring] at hlim
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => smoothDist_nonneg 3 _ _) ?_ hlim
  filter_upwards [hbev] with n hn
  have hflow : ScrnFlow d hs0 hsd (βN n) (hβN n) (n + 2) (P n) (X₀ n) (W n) (X n) :=
    ⟨hW n, hI n, hX₀ n, hsol n, hfilt n⟩
  have h := hinst (N := n + 2) (by omega) (hβN n) (b := b) (hℓpos n) (hℓle n) hn ⟨by linarith, by linarith⟩
    hflow (fun a => u n + t a) (fun a => by have := hu0 n; have := ht a; linarith)
  beta_reduce at h
  refine (smoothDist_triangle 3 _ (ProbabilityTheory.multivariateGaussian 0
    (mesoCovMatrix d s b (fun a => u n + t a) φ)) _).trans ?_
  exact add_le_add h le_rfl

example := (@screening_stationary_limit_proof : type_of% @screening_stationary_limit)

end HRS
