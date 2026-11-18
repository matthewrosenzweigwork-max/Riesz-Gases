import HRS.Main.A9Aux32

/-!
# Packet A9, part 33: Proposition A.9, convergence in law of the field (`main_torus_field_limit`)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.A9

open HRS HRS.PDE HRS.A33 HRS.Main HRS.A34

variable {d : ℕ}

theorem a9_smoothDist_embed_le {m m' : ℝ} (hmm' : m ≤ m') (P Q : Measure (NegSobolev d m))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    smoothDist 2 (P.map (NegSobolev.embed m')) (Q.map (NegSobolev.embed m')) ≤ smoothDist 2 P Q :=
  a9_smoothDist_map_le (a9EmbCLM hmm') (a9EmbCLM_norm_le hmm') P Q

theorem a9_law_eq {S : MainData d} {R : ∀ N, Realization d N} {Cin : ℝ} {εf : ℕ → ℝ}
    {ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ)}
    {νin : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin) {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (htm : Measurable fun F : NegSobolev d (gammaIdx d : ℝ) =>
      S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F) :
    law (R N).P (fun ω => S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) (ηF N ω)) =
      law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
        S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F) := by
  rw [← hfield.law_eq N hN]
  unfold law
  rw [Measure.map_map htm (hfield.ηF_meas N)]
  rfl

theorem a9_particle_prob {S : MainData d} {R : ∀ N, Realization d N} {N : ℕ} (γ t : ℝ) :
    IsProbabilityMeasure (particleFieldLaw (R N).P (S.sigma N) γ (R N).X (S.ρ N) t) := by
  unfold particleFieldLaw
  infer_instance

theorem a9_linear_prob {S : MainData d} {N : ℕ} (γ t : ℝ) (νin : Measure (NegSobolev d γ))
    [IsProbabilityMeasure νin] (νG : Measure (NegSobolev d γ)) [IsProbabilityMeasure νG] :
    IsProbabilityMeasure (linearFieldLaw νin (S.dyn N) (S.ρ N) (S.AN N) t γ id νG) := by
  haveI := InitialDataAux.negSobolev_secondCountable d γ
  unfold linearFieldLaw
  infer_instance

theorem a9_field_limit (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∀ (S : MainData d) (hs : S.s = s) (hT : S.T = T)
    (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ)
    (hstand : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈)
    (m₀ : ℕ) (ε : ℕ → ℝ) (hinit : InitialFluctuation S R m₀ Cin ε (fun _ => ∅))
    (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ))
    (νin : Measure (NegSobolev d (gammaIdx d : ℝ)))
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin)
    (L : LimitCoeffs d) (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d) (gammaIdx d))
    (hεf : Tendsto εf atTop (𝓝 0))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (νG : ℕ → Measure (NegSobolev d (gammaIdx d : ℝ)))
    (hνG : ∀ N : ℕ, 1 ≤ N →
      IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) (νG N))
    (νGlim : Measure (NegSobolev d (gammaIdx d : ℝ)))
    (hνGlim : IsLinearFieldNoise (L.dyn S) L.ρ L.invβstar t (gammaIdx d : ℝ) νGlim),
    (∀ γ' : ℝ, (gammaIdx d : ℝ) < γ' →
      ConvergesInLaw
        (fun N => particleFieldLaw (R N).P (S.sigma N) γ' (R N).X (S.ρ N) t)
        ((limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim).map (NegSobolev.embed γ'))) ∧
    (((ConvergesInLaw
          (fun N => law (R N).P (fun ω => S.AN N •
            transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) (ηF N ω)))
          (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
            L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F))) ∨
      (∃ Cs : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ t' ∈ Set.Icc (0 : ℝ) T,
        smoothDist 2
          (law (R N).P (fun ω => S.AN N •
            transportField (S.dyn N) (S.ρ N) t' (gammaIdx d : ℝ) (ηF N ω)))
          (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
            L.A • transportField (L.dyn S) L.ρ t' (gammaIdx d : ℝ) F)) ≤
          Cs * S.coeffDiscrepancy L (gammaIdx d) N)) →
      ConvergesInLaw
        (fun N => particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
        (limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim)) := by
  obtain ⟨C₀min, hmain⟩ := a9_field_main (d := d) s
  refine ⟨C₀min, ?_⟩
  intro Rg ν₀ MB Λ T VB Cin C₀ Cc hC₀ S hs hT R 𝔈 hstand m₀ ε hinit εf ηF νin hfield L hcoef hεf t ht
    νG hνG νGlim hνGlim
  obtain ⟨C, ΛT, hC, hΛ, hmain'⟩ := hmain Rg ν₀ MB Λ T VB Cin C₀ Cc hC₀
  obtain ⟨hbound, -⟩ := hmain' S hs hT R 𝔈 hstand m₀ ε hinit εf ηF νin hfield t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) S.T := by rw [hT]; exact ht
  haveI hνin : IsProbabilityMeasure νin := by
    rw [← hfield.law_eq 1 le_rfl]; infer_instance
  haveI : IsProbabilityMeasure νGlim := hνGlim.1
  have htm : ∀ N, 1 ≤ N → Measurable fun F : NegSobolev d (gammaIdx d : ℝ) =>
      S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F := fun N hN =>
    (a9_tmeas S L Rg ν₀ MB Λ VB hcoef N hN ht').1.const_smul (S.AN N)
  haveI hνGp : ∀ N, 1 ≤ N → IsProbabilityMeasure (νG N) := fun N hN => (hνG N hN).1
  -- the index shift
  set N₁ : ℕ := max 1 ⌈C⌉₊ with hN₁
  have hN₁1 : 1 ≤ N₁ := le_max_left _ _
  have hN₁C : C ≤ (N₁ : ℝ) := (Nat.le_ceil C).trans (by exact_mod_cast le_max_right _ _)
  have hn1 : ∀ n, 1 ≤ n + N₁ := fun n => by omega
  have hnC : ∀ n, C ≤ ((n + N₁ : ℕ) : ℝ) := fun n =>
    hN₁C.trans (by exact_mod_cast Nat.le_add_left N₁ n)
  -- the rate tends to zero
  have hfr : Tendsto (fun N : ℕ => C * Real.exp (ΛT * t) *
      fieldRate d (εf N) (S.qN N) (S.sigma N) (𝔈 N) N) atTop (𝓝 0) := by
    have := (a9_fieldRate_tendsto S hstand.energy.pos hstand.energy.small hεf).const_mul
      (C * Real.exp (ΛT * t))
    simpa using this
  -- `d_{C²}` closeness at the level `γ`
  have hsd0 : Tendsto (fun n : ℕ => smoothDist 2
      (particleFieldLaw (R (n + N₁)).P (S.sigma (n + N₁)) (gammaIdx d : ℝ) (R (n + N₁)).X
        (S.ρ (n + N₁)) t)
      (linearFieldLaw νin (S.dyn (n + N₁)) (S.ρ (n + N₁)) (S.AN (n + N₁)) t (gammaIdx d : ℝ) id
        (νG (n + N₁)))) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => smoothDist_nonneg 2 _ _) (fun n => ?_)
      (hfr.comp (tendsto_add_atTop_nat N₁))
    have h := hbound (n + N₁) (hnC n) (νG (n + N₁)) (hνG _ (hn1 n))
    rw [a9_linear_eq hfield (hn1 n) (htm _ (hn1 n)) (νG _)] at h
    exact h
  refine ⟨fun γ' hγ' => ?_, fun hAB => ?_⟩
  · -- the convergence in `E_{γ'}`
    have hγle : (gammaIdx d : ℝ) ≤ γ' := hγ'.le
    have qual := a9_qual_one s Rg ν₀ MB Λ T VB S hs hT L hcoef νin hνin t ht νG hνG νGlim hνGlim hγ'
    haveI hlinp : ∀ n, IsProbabilityMeasure
        ((linearFieldLaw νin (S.dyn (n + N₁)) (S.ρ (n + N₁)) (S.AN (n + N₁)) t (gammaIdx d : ℝ) id
          (νG (n + N₁))).map (NegSobolev.embed γ')) := fun n => by
      haveI := hνGp _ (hn1 n)
      haveI := a9_linear_prob (S := S) (N := n + N₁) (gammaIdx d : ℝ) t νin (νG (n + N₁))
      infer_instance
    haveI hpp : ∀ n, IsProbabilityMeasure
        (particleFieldLaw (R (n + N₁)).P (S.sigma (n + N₁)) γ' (R (n + N₁)).X (S.ρ (n + N₁)) t) :=
      fun n => a9_particle_prob γ' t
    haveI : IsProbabilityMeasure ((limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim).map
        (NegSobolev.embed γ')) := by
      haveI := InitialDataAux.negSobolev_secondCountable d (gammaIdx d : ℝ)
      unfold limitFieldLaw linearFieldLaw
      infer_instance
    have hdc : Tendsto (fun n : ℕ => smoothDist 2
        (particleFieldLaw (R (n + N₁)).P (S.sigma (n + N₁)) γ' (R (n + N₁)).X (S.ρ (n + N₁)) t)
        ((linearFieldLaw νin (S.dyn (n + N₁)) (S.ρ (n + N₁)) (S.AN (n + N₁)) t (gammaIdx d : ℝ) id
          (νG (n + N₁))).map (NegSobolev.embed γ'))) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => smoothDist_nonneg 2 _ _) (fun n => ?_) hsd0
      haveI := hνGp _ (hn1 n)
      haveI := a9_linear_prob (S := S) (N := n + N₁) (gammaIdx d : ℝ) t νin (νG (n + N₁))
      haveI := a9_particle_prob (S := S) (R := R) (N := n + N₁) (gammaIdx d : ℝ) t
      rw [a9_particle_embed hstand (hn1 n) ht' hγle]
      exact a9_smoothDist_embed_le hγle _ _
    have key := a9_weak_of_dc2
      (fun n => particleFieldLaw (R (n + N₁)).P (S.sigma (n + N₁)) γ' (R (n + N₁)).X (S.ρ (n + N₁)) t)
      (fun n => (linearFieldLaw νin (S.dyn (n + N₁)) (S.ρ (n + N₁)) (S.AN (n + N₁)) t
        (gammaIdx d : ℝ) id (νG (n + N₁))).map (NegSobolev.embed γ'))
      ((limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim).map (NegSobolev.embed γ'))
      ((a9_conv_shift N₁).1 qual) hdc
    exact (a9_conv_shift N₁).2 key
  · -- the base topology
    haveI hlinp : ∀ n, IsProbabilityMeasure
        (linearFieldLaw νin (S.dyn (n + N₁)) (S.ρ (n + N₁)) (S.AN (n + N₁)) t (gammaIdx d : ℝ) id
          (νG (n + N₁))) := fun n => by
      haveI := hνGp _ (hn1 n)
      exact a9_linear_prob (S := S) (N := n + N₁) (gammaIdx d : ℝ) t νin (νG (n + N₁))
    haveI hpp : ∀ n, IsProbabilityMeasure
        (particleFieldLaw (R (n + N₁)).P (S.sigma (n + N₁)) (gammaIdx d : ℝ) (R (n + N₁)).X
          (S.ρ (n + N₁)) t) := fun n => a9_particle_prob (gammaIdx d : ℝ) t
    haveI : IsProbabilityMeasure (limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim) := by
      haveI := InitialDataAux.negSobolev_secondCountable d (gammaIdx d : ℝ)
      unfold limitFieldLaw linearFieldLaw
      infer_instance
    -- convergence of the first factor
    have hμc : ConvergesInLaw
        (fun N => law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
          S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F))
        (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
          L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F)) := by
      rcases hAB with hA | ⟨Cs, hCs⟩
      · refine a34_converges_congr ?_ hA
        filter_upwards [eventually_ge_atTop 1] with N hN
        exact a9_law_eq hfield hN (htm N hN)
      · have hu₀ : Measurable fun F : NegSobolev d (gammaIdx d : ℝ) =>
            L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F := by
          have := (a9_tmeas S L Rg ν₀ MB Λ VB hcoef 1 le_rfl ht').2.const_smul L.A
          exact this
        haveI : ∀ n : ℕ, IsProbabilityMeasure
            (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
              S.AN (n + 1) • transportField (S.dyn (n + 1)) (S.ρ (n + 1)) t (gammaIdx d : ℝ) F)) :=
          fun n => by unfold law; infer_instance
        haveI : IsProbabilityMeasure (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
            L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F)) := by unfold law; infer_instance
        have hdc : Tendsto (fun n : ℕ => smoothDist 2
            (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
              S.AN (n + 1) • transportField (S.dyn (n + 1)) (S.ρ (n + 1)) t (gammaIdx d : ℝ) F))
            (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
              L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F))) atTop (𝓝 0) := by
          have hΔ : Tendsto (fun n : ℕ => Cs * S.coeffDiscrepancy L (gammaIdx d) (n + 1)) atTop (𝓝 0) := by
            have := (hcoef.tendsto.comp (tendsto_add_atTop_nat 1)).const_mul Cs
            simpa using this
          refine squeeze_zero (fun n => smoothDist_nonneg 2 _ _) (fun n => ?_) hΔ
          have h := hCs (n + 1) (by omega) t ht
          rw [a9_law_eq hfield (by omega) (htm (n + 1) (by omega))] at h
          exact h
        have key := a9_weak_of_dc2
          (fun n : ℕ => law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
            S.AN (n + 1) • transportField (S.dyn (n + 1)) (S.ρ (n + 1)) t (gammaIdx d : ℝ) F))
          (fun _ : ℕ => law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
            L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F))
          (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
            L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F))
          (fun f => tendsto_const_nhds) hdc
        exact (a9_conv_shift 1).2 key
    have qual := a9_qual_two s Rg ν₀ MB Λ T VB S hs hT L hcoef νin hνin t ht νG hνG νGlim hνGlim hμc
    have key := a9_weak_of_dc2
      (fun n => particleFieldLaw (R (n + N₁)).P (S.sigma (n + N₁)) (gammaIdx d : ℝ) (R (n + N₁)).X
        (S.ρ (n + N₁)) t)
      (fun n => linearFieldLaw νin (S.dyn (n + N₁)) (S.ρ (n + N₁)) (S.AN (n + N₁)) t
        (gammaIdx d : ℝ) id (νG (n + N₁)))
      (limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim) ((a9_conv_shift N₁).1 qual) hsd0
    exact (a9_conv_shift N₁).2 key

end HRS.Main.A9
