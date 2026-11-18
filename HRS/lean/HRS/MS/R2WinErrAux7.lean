import HRS.MS.R2WinErrAux6

/-!
# S10.4 packet E3b0: the pathwise Duhamel decomposition between `b` and `b+u`

`s104_duhamel_path`: if `|Fm(t,r)| ≤ |Fm(t₀,r)| + ∫_{(t₀,t]} |F2(s,r)| ds` for `0 ≤ r ≤ t₀ ≤ t ≤ b+T` (the integrated form of
`∂_tFm = F2`, e.g. from the evolution identity `∂_tU(r,t)φ = U(r,t)L_tφ`), then for every `u ∈ [0,T]`
`|∫_0^{b+u} Fm(b+u,r) dr| ≤ ∫_0^b |Fm(b,r)| dr + ∫_b^{b+T} |Fm(r,r)| dr + ∬_{[b,b+T]×[0,b+T]} |F2(s,r)|`
(all in `ℝ≥0∞`; no differentiation of the parametric integral and no integrability needed).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.R2WinErr

theorem s104_duhamel_path {b T : ℝ} (hb : 0 ≤ b) (hT : 0 ≤ T) (Fm : ℝ → ℝ → ℝ) (F2 : ℝ × ℝ → ℝ)
    (hrep : ∀ r t0 t : ℝ, 0 ≤ r → r ≤ t0 → t0 ≤ t → t ≤ b + T →
      ENNReal.ofReal |Fm t r| ≤ ENNReal.ofReal |Fm t0 r| +
        ∫⁻ s in Set.Ioc t0 t, ENNReal.ofReal |F2 (s, r)|)
    (hm0 : AEMeasurable (fun r => ENNReal.ofReal |Fm b r|) (volume.restrict (Set.Icc (0 : ℝ) b)))
    (hm1 : AEMeasurable (fun r => ENNReal.ofReal |Fm r r|) (volume.restrict (Set.Icc b (b + T))))
    (hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal |F2 p|)
      (volume.restrict ((Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T)))))
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) :
    ENNReal.ofReal |∫ r in Set.Icc (0 : ℝ) (b + u), Fm (b + u) r| ≤
      (∫⁻ r in Set.Icc (0 : ℝ) b, ENNReal.ofReal |Fm b r|) +
      (∫⁻ r in Set.Icc b (b + T), ENNReal.ofReal |Fm r r|) +
      ∫⁻ p in (Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T)), ENNReal.ofReal |F2 p| := by
  set t : ℝ := b + u with ht
  have htb : b ≤ t := by linarith [hu.1]
  have htT : t ≤ b + T := by linarith [hu.2]
  have ht0 : 0 ≤ t := by linarith
  set g : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal |F2 p| with hg
  -- step 1: absolute value of the integral
  have h1 : ENNReal.ofReal |∫ r in Set.Icc (0 : ℝ) t, Fm t r| ≤
      ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal |Fm t r| := by
    have := enorm_integral_le_lintegral_enorm (μ := volume.restrict (Set.Icc (0 : ℝ) t)) (fun r => Fm t r)
    simpa [Real.enorm_eq_ofReal_abs] using this
  refine h1.trans ?_
  -- step 2: split the domain
  have hsplit : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) b ∪ Set.Ioc b t := by
    intro r hr
    by_cases h : r ≤ b
    · exact Or.inl ⟨hr.1, h⟩
    · exact Or.inr ⟨not_le.1 h, hr.2⟩
  have h2 : ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal |Fm t r| ≤
      (∫⁻ r in Set.Icc (0 : ℝ) b, ENNReal.ofReal |Fm t r|) +
      ∫⁻ r in Set.Ioc b t, ENNReal.ofReal |Fm t r| :=
    (lintegral_mono_set hsplit).trans (lintegral_union_le _ _ _)
  refine h2.trans ?_
  -- step 3: Duhamel inequalities
  set G : ℝ → ℝ≥0∞ := fun r => ∫⁻ s in Set.Ioc b t, ENNReal.ofReal |F2 (s, r)| with hG
  have hA : ∫⁻ r in Set.Icc (0 : ℝ) b, ENNReal.ofReal |Fm t r| ≤
      (∫⁻ r in Set.Icc (0 : ℝ) b, ENNReal.ofReal |Fm b r|) + ∫⁻ r in Set.Icc (0 : ℝ) b, G r := by
    rw [← lintegral_add_left' hm0]
    exact setLIntegral_mono' measurableSet_Icc fun r hr => hrep r b t hr.1 hr.2 htb htT
  have hm1' : AEMeasurable (fun r => ENNReal.ofReal |Fm r r|) (volume.restrict (Set.Ioc b t)) :=
    hm1.mono_measure (Measure.restrict_mono (fun r (hr : r ∈ Set.Ioc b t) =>
      (⟨hr.1.le, hr.2.trans htT⟩ : r ∈ Set.Icc b (b + T))) le_rfl)
  have hB : ∫⁻ r in Set.Ioc b t, ENNReal.ofReal |Fm t r| ≤
      (∫⁻ r in Set.Ioc b t, ENNReal.ofReal |Fm r r|) + ∫⁻ r in Set.Ioc b t, G r := by
    rw [← lintegral_add_left' hm1']
    refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
    refine (hrep r r t (hb.trans hr.1.le) le_rfl hr.2 htT).trans ?_
    refine add_le_add le_rfl ?_
    exact lintegral_mono_set (Set.Ioc_subset_Ioc_left hr.1.le)
  -- step 4: glue the two double integrals
  have hdisj : Disjoint (Set.Icc (0 : ℝ) b) (Set.Ioc b t) :=
    Set.disjoint_left.2 fun r h1 h2 => absurd h1.2 (not_le.2 h2.1)
  have hunion : (∫⁻ r in Set.Icc (0 : ℝ) b, G r) + (∫⁻ r in Set.Ioc b t, G r) =
      ∫⁻ r in Set.Icc (0 : ℝ) b ∪ Set.Ioc b t, G r :=
    (lintegral_union measurableSet_Ioc hdisj).symm
  have hsub : Set.Icc (0 : ℝ) b ∪ Set.Ioc b t ⊆ Set.Icc (0 : ℝ) (b + T) := by
    intro r hr
    rcases hr with hr | hr
    · exact ⟨hr.1, hr.2.trans (by linarith)⟩
    · exact ⟨(hb.trans hr.1.le), hr.2.trans htT⟩
  have hprod : (volume : Measure (ℝ × ℝ)).restrict ((Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T))) =
      (volume.restrict (Set.Icc b (b + T))).prod (volume.restrict (Set.Icc (0 : ℝ) (b + T))) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have hrect : ∫⁻ r in Set.Icc (0 : ℝ) (b + T), (∫⁻ s in Set.Icc b (b + T), ENNReal.ofReal |F2 (s, r)|) =
      ∫⁻ p in (Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T)), ENNReal.ofReal |F2 p| := by
    rw [hprod] at hmeas ⊢
    rw [lintegral_prod_symm _ hmeas]
  have hGle : ∫⁻ r in Set.Icc (0 : ℝ) b ∪ Set.Ioc b t, G r ≤
      ∫⁻ p in (Set.Icc b (b + T)) ×ˢ (Set.Icc (0 : ℝ) (b + T)), ENNReal.ofReal |F2 p| := by
    rw [← hrect]
    refine (lintegral_mono_set hsub).trans (lintegral_mono fun r => ?_)
    exact lintegral_mono_set (fun s (hs : s ∈ Set.Ioc b t) =>
      (⟨hs.1.le, hs.2.trans htT⟩ : s ∈ Set.Icc b (b + T)))
  have hI1 : ∫⁻ r in Set.Ioc b t, ENNReal.ofReal |Fm r r| ≤ ∫⁻ r in Set.Icc b (b + T), ENNReal.ofReal |Fm r r| :=
    lintegral_mono_set (fun r (hr : r ∈ Set.Ioc b t) => (⟨hr.1.le, hr.2.trans htT⟩ : r ∈ Set.Icc b (b + T)))
  calc _ ≤ ((∫⁻ r in Set.Icc (0 : ℝ) b, ENNReal.ofReal |Fm b r|) + ∫⁻ r in Set.Icc (0 : ℝ) b, G r) +
        ((∫⁻ r in Set.Ioc b t, ENNReal.ofReal |Fm r r|) + ∫⁻ r in Set.Ioc b t, G r) := add_le_add hA hB
    _ = (∫⁻ r in Set.Icc (0 : ℝ) b, ENNReal.ofReal |Fm b r|) + (∫⁻ r in Set.Ioc b t, ENNReal.ofReal |Fm r r|) +
        ((∫⁻ r in Set.Icc (0 : ℝ) b, G r) + (∫⁻ r in Set.Ioc b t, G r)) := by ring
    _ ≤ _ := by
        rw [hunion]
        gcongr

end HRS.MS.R2WinErr
