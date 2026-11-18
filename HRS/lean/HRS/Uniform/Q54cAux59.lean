import HRS.Uniform.Q54cAux58

/-!
# Q54c, part 59: Corollary 3.26 `coefficient_comparison`, relocated proof

`HRS/Uniform/Comparison.lean` cannot import this proof (the PDE/Hilbert-martingale stack it needs lies downstream),
so the proof is stated here as `coefficient_comparison_proof` for the frozen statement of
`HRS.Uniform.coefficient_comparison`, and the file ends with the type-checking `example`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform

open HRS HRS.PDE HRS.Uniform.Q54c

variable {d : ℕ}

theorem coefficient_comparison_proof (b : GeneralBounds d) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : GeneralSetup d, S.Within b → S.MFHyp → S.PosDensityWith b.c →
      ∀ (Dlim : DynData d), Dlim.s = S.s → Dlim.M = -1 → Dlim.V = S.V → Dlim.invβ ≤ b.Bβ →
      ∀ (qlim Alim : ℝ), 0 ≤ qlim → ∀ ρlim : ℝ → Torus d → ℝ,
        (∀ t ∈ Set.Icc (0 : ℝ) S.T, IsProbDensity (ρlim t)) →
        IsRegularMF (S.γ + 2 * d + 12) S.Λ S.T ρlim → (∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ x, b.c ≤ ρlim t x) →
        (∀ ψ : Torus d → ℝ, Continuous ψ →
          ContinuousOn (fun r => ∫ x, ψ x * ρlim r x) (Set.Icc (0 : ℝ) S.T)) →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η₀ : Ω → NegSobolev d S.γ) (_ : Measurable η₀)
        (Y Ylim : ℝ → Ω → NegSobolev d ((S.γ : ℝ) + 2)),
        IsLinearFluctuationSolution P (S.dyn N) (S.ρ N) ((S.γ : ℝ) + 2)
          (qScale N (S.κ N) (S.invβ N)) S.T
          (fun ω => Ascale N (S.κ N) (S.invβ N) • NegSobolev.embed ((S.γ : ℝ) + 2) (η₀ ω)) Y →
        IsLinearFluctuationSolution P Dlim ρlim ((S.γ : ℝ) + 2) qlim S.T
          (fun ω => Alim • NegSobolev.embed ((S.γ : ℝ) + 2) (η₀ ω)) Ylim →
        let Δ : ℝ := |S.invβ N - Dlim.invβ| + |qScale N (S.κ N) (S.invβ N) - qlim| +
          |Ascale N (S.κ N) (S.invβ N) - Alim| +
          ⨆ t : Set.Icc (0 : ℝ) S.T, Torus.cbNorm (S.γ + 2 * d + 12) (fun x => S.ρ N t x - ρlim t x)
        let B : ℝ≥0∞ := ENNReal.ofReal C * (1 + eLpNorm η₀ 2 P) * ENNReal.ofReal (Δ + Real.sqrt Δ)
        let LN := law P (toPath ((S.γ : ℝ) + 2) S.T Y)
        let Llim := law P (toPath ((S.γ : ℝ) + 2) S.T Ylim)
        wassersteinE 1 LN Llim ≤ B ∧ wassersteinE 2 LN Llim ≤ B ∧
          ENNReal.ofReal (smoothDist 2 LN Llim) ≤ B := by
  by_cases hex : ∃ S₀ : GeneralSetup d, S₀.Within b
  swap
  · exact ⟨1, one_pos, fun S hS => absurd ⟨S, hS⟩ hex⟩
  obtain ⟨S₀, hS₀⟩ := hex
  have hH : SetupHyp b := by
    refine ⟨by have := S₀.hd; omega, ?_, ?_, ?_⟩
    · rw [← hS₀.1]; exact S₀.hs0
    · rw [← hS₀.1]; exact S₀.hsd
    · rw [← hS₀.2.2.1]; exact S₀.hγ
  obtain ⟨cc⟩ := (mkSetup b hH).exists_cmpConst
  refine ⟨(mkSetup b hH).Ccore cc, (mkSetup b hH).Ccore_pos cc, ?_⟩
  intro S hS hMF hPos Dlim hDs hDM hDV hDβ qlim Alim hq0 ρlim hρp hρreg hρlow hρcont N hN Ω _ P _ η₀ hη Y Ylim hY hYlim
  obtain ⟨hSs, hST, hSγ, hSΛ, hSβ, hSC, hSV⟩ := hS
  have hT : 0 < b.T := hST ▸ S.hT
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hγ2 := hH.hγ
  have hKle : b.γ - 2 + 4 + 3 ≤ b.γ + 2 * d + 12 := by omega
  have hVreg : Torus.IsCk (b.γ + 2 * d + 12) b.V := by
    have := S.V_reg
    rwa [hSV, hSγ] at this
  have hle : ((b.γ - 2 + 4 + 3 : ℕ) : WithTop ℕ∞) ≤ ((b.γ + 2 * d + 12 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast hKle
  have hVreg' : Torus.IsCk (b.γ - 2 + 4 + 3) b.V := ContDiff.of_le hVreg hle
  have hMFN := hMF N
  have hregN : IsRegularMF (b.γ + 2 * d + 12) b.Λ b.T (S.ρ N) := by
    have := hMFN.2
    rwa [hSγ, hSΛ, hST] at this
  have hprobN : ∀ t ∈ Set.Icc (0 : ℝ) b.T, IsProbDensity (S.ρ N t) := fun t ht =>
    hMFN.1.density t (by rw [hST]; exact ht)
  have hV1 : Torus.IsCk 1 (S.dyn N).V := by
    show Torus.IsCk 1 S.V
    rw [hSV]
    exact ContDiff.of_le hVreg (by exact_mod_cast (by omega : 1 ≤ b.γ + 2 * d + 12))
  have hcontN : ∀ ψ : Torus d → ℝ, Continuous ψ →
      ContinuousOn (fun r => ∫ x, ψ x * S.ρ N r x) (Set.Icc 0 b.T) := by
    have := weak_continuity (S.dyn N) hd1 S.T S.Λ S.hT.le (S.γ + 2 * d + 12) (by omega) (S.ρ N)
      hMFN.1 hMFN.2 hV1
    rwa [hST] at this
  have hlowN : ¬ b.s ≤ (d : ℝ) - 2 → 0 < b.c ∧ ∀ t ∈ Set.Icc (0 : ℝ) b.T, ∀ x, b.c ≤ S.ρ N t x :=
    fun _ => ⟨hPos.1, fun t ht x => hPos.2 N t (by rw [hST]; exact ht) x⟩
  have h₁ := mkData b hH hT (S.dyn N) (S.ρ N) hSs rfl hSV hVreg' (hSβ N) hprobN hregN hcontN hlowN
  have hprobL : ∀ t ∈ Set.Icc (0 : ℝ) b.T, IsProbDensity (ρlim t) := fun t ht =>
    hρp t (by rw [hST]; exact ht)
  have hregL : IsRegularMF (b.γ + 2 * d + 12) b.Λ b.T ρlim := by
    have := hρreg
    rwa [hSγ, hSΛ, hST] at this
  have hcontL : ∀ ψ : Torus d → ℝ, Continuous ψ →
      ContinuousOn (fun r => ∫ x, ψ x * ρlim r x) (Set.Icc 0 b.T) := by
    have := hρcont
    rwa [hST] at this
  have hlowL : ¬ b.s ≤ (d : ℝ) - 2 → 0 < b.c ∧ ∀ t ∈ Set.Icc (0 : ℝ) b.T, ∀ x, b.c ≤ ρlim t x :=
    fun _ => ⟨hPos.1, fun t ht x => hρlow t (by rw [hST]; exact ht) x⟩
  have h₂ := mkData b hH hT Dlim ρlim (hDs.trans hSs) hDM (hDV.trans hSV) hVreg' hDβ hprobL hregL hcontL hlowL
  have hbdd : BddAbove (Set.range fun t : Set.Icc (0 : ℝ) S.T =>
      Torus.cbNorm (S.γ + 2 * d + 12) (fun x => S.ρ N t x - ρlim t x)) := by
    refine ⟨S.Λ + S.Λ, ?_⟩
    rintro _ ⟨t, rfl⟩
    have h1 := hMFN.2 t t.2
    have h2 := hρreg t t.2
    exact (cbNorm_sub_le' (S.γ + 2 * d + 12) (S.ρ N t) (ρlim t) h1.1 h2.1).trans (add_le_add h1.2 h2.2)
  have hδ : ∀ r ∈ Set.Icc (0 : ℝ) (mkSetup b hH).T, Torus.cbNorm ((mkSetup b hH).n + 4)
      (S.ρ N r - ρlim r) ≤ ⨆ t : Set.Icc (0 : ℝ) S.T,
        Torus.cbNorm (S.γ + 2 * d + 12) (fun x => S.ρ N t x - ρlim t x) := by
    intro r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) S.T := by rw [hST]; exact hr
    refine le_trans ?_ (le_ciSup hbdd ⟨r, hr'⟩)
    exact cbNorm_mono' (by show b.γ - 2 + 4 ≤ S.γ + 2 * d + 12; rw [hSγ]; omega) _
  have hq := qScale_bounds (N := N) (by omega) (S.hκ N) (S.hinvβ N)
  have hg2 : (S.γ : ℝ) = (((mkSetup b hH).n : ℕ) : ℝ) + 2 := by
    show (S.γ : ℝ) = ((b.γ - 2 : ℕ) : ℝ) + 2
    rw [hSγ, Nat.cast_sub (by omega : 2 ≤ b.γ)]
    push_cast; ring
  have hg4 : (S.γ : ℝ) + 2 = (((mkSetup b hH).n : ℕ) : ℝ) + 4 := by
    rw [← sub_eq_zero] at hg2 ⊢
    linarith
  exact PdeSetup.core_comparison_all' (mkSetup b hH) cc hH.hn2 0 (S.dyn N) Dlim (S.ρ N) ρlim h₁ h₂
    (by rw [hDM]; rfl) (by rw [hDV]; rfl) (qScale N (S.κ N) (S.invβ N)) qlim (Ascale N (S.κ N) (S.invβ N)) Alim
    _ hq.1 hq.2 hq0 (Ascale_abs_le (S.hκ N)) hδ P (S.γ : ℝ) ((S.γ : ℝ) + 2) S.T hg2 hg4 hST η₀ hη Y Ylim hY hYlim

end HRS.Uniform

example := (@HRS.Uniform.coefficient_comparison_proof : type_of% @HRS.Uniform.coefficient_comparison)
