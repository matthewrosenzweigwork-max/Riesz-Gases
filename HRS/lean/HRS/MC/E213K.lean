import HRS.Uniform.Q48aAux6
import HRS.Uniform.Q54cAux36
import HRS.Main.GFSpec3
import HRS.Sections.AdjKDAux1

/-!
# E213K: the global Gaussian Hilbert martingale and the global covariance density

`exists_gaussian_martingale_top`: `⊤`-copy of `HRS.Uniform.Q45.exists_gaussian_martingale`: for a density `Db`
that is a deterministic covariance density on every window `[0,t]`, one continuous Gaussian Hilbert martingale
`G` (on a probability space in `Type`) has covariation `Db` on every window.
-/

noncomputable section

open HRS HRS.MRep HRS.Uniform.Q07c HRS.Uniform.Q48a
open MeasureTheory Filter Topology HRS.HilbertCLTAux ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213K

open Classical

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem exists_gaussian_martingale_top (Db : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (hDb : ∀ t : ℝ, 0 ≤ t → IsDetCovDensity t Db) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ℱ : Filtration ℝ mΩ) (G : ℝ → Ω → H),
      (∀ ω, Continuous fun τ => G τ ω) ∧ (∀ ω, G 0 ω = 0) ∧
      ∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P ℱ S G (fun r _ => Db r) := by
  obtain ⟨ιe, hι, e, -⟩ := exists_hilbertBasis_ulift.{_, 0} (H := H)
  haveI := hι
  obtain ⟨Sb, hSbm, hSb0, hSb⟩ := exists_sqrt_densityT e Db hDb
  obtain ⟨Tf, hD⟩ := pc_detDataT e Db hDb hSbm hSb0 hSb
  have hSbHS := hD.summable_sb
  set P : Measure (ιe → WienerSeq) := wMeasure ιe with hPdef
  set ℱ := wFiltration ιe with hℱdef
  have hB : IsCylindricalBrownian P ℱ (fun t (ω : ιe → WienerSeq) (i : ιe) => wienerPath t (ω i)) :=
    fun F => isBrownianFiltration_wFiltration F
  obtain ⟨Gb, hGI, hGJ⟩ := pc_exists_GT hD hB
  have hZG : ∀ S, IsHSIntegrand P ℱ S
      (fun r (_ : ιe → WienerSeq) (j : ιe) => Sb r (e j)) :=
    fun S => hD.hsInt P ℱ S
  have hNJG : ∀ x : H, ∃ J : ℝ → (ιe → WienerSeq) → ℝ,
      IsItoC P ℱ (fun t ω j => wienerPath t (ω j))
        (fun r (_ : ιe → WienerSeq) (j : ιe) => inner ℝ (Sb r (e j)) x) J ∧
      ∀ τ, 0 ≤ τ → (fun ω => inner ℝ (Gb τ ω) x) =ᵐ[P] J τ := by
    intro x
    obtain ⟨J, hJ, hae⟩ := hGJ x
    exact ⟨J, hJ, hae⟩
  have hGHM := fun S => isHM_of_ito hB hZG hGI.cont hGI.adapted hGI.zero hNJG S
  have hcovG : ∀ r : ℝ, 0 ≤ r → hsCovForm (fun j => Sb r (e j)) = Db r :=
    fun r hr => hsCovForm_sqrt_cols e (hSb r hr) (hSbHS r)
  have hGfinal : ∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P ℱ S Gb
      (fun r _ => Db r) := by
    intro S hS
    refine (hGHM S).mono_congr hS le_rfl (fun x y => ?_) (fun σ x y => measurable_const) ?_
    · exact ((hDb 0 le_rfl).meas x y).comp measurable_fst
    · intro r hr ω
      exact (hcovG r hr).symm
  haveI : IsProbabilityMeasure P := inferInstance
  exact ⟨ιe → WienerSeq, inferInstance, P, inferInstance, ℱ, Gb, hGI.cont,
    fun ω => hGI.zero 0 le_rfl ω, hGfinal⟩

end HRS.MC.E213K

namespace HRS.MC.E213K

open HRS.Uniform HRS.Uniform.Q54c HRS.Torus

variable {d : ℕ}

/-- `ContinuousOn` on `[0,∞)` from `ContinuousOn` on every `[0,n]`. -/
theorem e213k_continuousOn_Ici {f : ℝ → ℝ} (h : ∀ n : ℕ, ContinuousOn f (Set.Icc 0 (n : ℝ))) :
    ContinuousOn f (Set.Ici 0) := by
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_gt x
  have hmem : Set.Icc (0 : ℝ) n ∈ nhdsWithin x (Set.Ici 0) := by
    have : Set.Icc (0 : ℝ) n = Set.Ici (0 : ℝ) ∩ Set.Iic (n : ℝ) := by
      ext y; simp [and_comm]
    rw [this]
    exact inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset (Iio_mem_nhds hn) Set.Iio_subset_Iic_self))
  exact (h n x ⟨hx, hn.le⟩).mono_of_mem_nhdsWithin hmem

/-- The global covariance density `σ ↦ 1_{σ ≥ 0} covForm n q (ρ_σ)` is a deterministic covariance density
on every window `[0,t]`, `t ≥ 0`. -/
theorem e213k_isDetCovDensity_global {n : ℝ} (hn : (d : ℝ) / 2 + 2 < n) {q : ℝ} (hq : 0 ≤ q)
    {ρ : ℝ → Torus d → ℝ} (hprob : ∀ σ : ℝ, 0 ≤ σ → IsProbDensity (ρ σ))
    (hweak : ∀ ψ : Torus d → ℝ, Continuous ψ →
      ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Set.Ici 0))
    (hcts : ∀ σ : ℝ, 0 ≤ σ → Continuous (ρ σ)) :
    ∀ t : ℝ, 0 ≤ t → IsDetCovDensity t
      (fun σ : ℝ => if 0 ≤ σ then covForm n q (withDensityReal (ρ σ)) else 0) := by
  intro t ht
  have hIcc : ∀ T : ℝ, ∀ σ ∈ Set.Icc 0 T, IsProbDensity (ρ σ) := fun T σ hσ => hprob σ hσ.1
  have hDt := isDetCovDensity_covDens hn hq (hIcc t)
    (fun ψ hψ => (hweak ψ hψ).mono Set.Icc_subset_Ici_self) (fun σ hσ => hcts σ hσ.1)
  have hagree : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      (if 0 ≤ σ then covForm n q (withDensityReal (ρ σ)) else 0) = covDens n q t ρ σ := by
    intro σ hσ
    rw [covDens_of_mem hσ]; simp [hσ.1]
  refine ⟨fun x y => ?_, fun σ hσ => ?_, ?_⟩
  · have hpw : (fun σ : ℝ => (if 0 ≤ σ then covForm n q (withDensityReal (ρ σ)) else 0) x y) =
        (Set.Ici (0 : ℝ)).piecewise (fun σ => covForm n q (withDensityReal (ρ σ)) x y)
          (fun _ => 0) := by
      funext σ
      by_cases h : 0 ≤ σ <;> simp [Set.piecewise, h]
    rw [hpw]
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_Ici
    refine e213k_continuousOn_Ici fun N => ?_
    exact covDens_continuousOn hn hq (hIcc N)
      (fun ψ hψ => (hweak ψ hψ).mono Set.Icc_subset_Ici_self) (fun σ hσ => hcts σ hσ.1) x y
  · rw [hagree σ hσ]; exact hDt.traceClass σ hσ
  · exact hDt.int.congr_fun (fun σ hσ => by rw [hagree σ hσ]) measurableSet_Icc

/-- Agreement of the horizon-`t` density `covDensT` with the global density on `[0,t]`. -/
theorem e213k_covDensT_eq (m q t : ℝ) (ρ : ℝ → Torus d → ℝ) {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t) :
    HRS.GF.covDensT m q t ρ σ =
      (fun σ : ℝ => if 0 ≤ σ then covForm m q (withDensityReal (ρ σ)) else 0) σ := by
  simp [HRS.GF.covDensT, hσ, hσ.1]

/-- The same global density, under the hypotheses of `HRS.ThermLin.thermlin_detCov`
(a smooth positive trajectory), is a deterministic covariance density on every window `[0,t]`, `t ≥ 0`. -/
theorem e213k_isDetCovDensity_global_traj {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) :
    ∀ t : ℝ, 0 ≤ t → IsDetCovDensity t
      (fun σ : ℝ => if 0 ≤ σ then covForm m β⁻¹ (withDensityReal (ρ σ)) else 0) := by
  have hd1 : 1 ≤ d := by omega
  have hprobT : ∀ σ : ℝ, 0 ≤ σ → IsProbDensity (ρ σ) := fun σ hσ =>
    (HRS.Q40b.q40b_meanField hd1 htr (T := σ + 1) (by linarith)).density σ ⟨hσ, by linarith⟩
  refine e213k_isDetCovDensity_global hm (inv_nonneg.2 htr.hβ.le) hprobT ?_ ?_
  · intro ψ hψ
    refine e213k_continuousOn_Ici fun N => ?_
    exact HRS.AdjK.adjkd_weak_cont hd htr N ψ hψ
  · intro σ hσ
    have hjc := HRS.Q40b.q40b_jointCont hd1 htr (σ + 1)
    exact hjc.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨⟨hσ, by linarith⟩, Set.mem_univ _⟩)

end HRS.MC.E213K
