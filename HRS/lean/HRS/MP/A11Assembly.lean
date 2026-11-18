import HRS.MP.FidiAssembly
import HRS.MP.FlucPath
import HRS.MP.FixedTimeTight
import HRS.MP.KolmChentsov
import HRS.MP.RemainderSup
import HRS.MP.DualDecomp
import HRS.MP.InitModulus
import HRS.Main.GFB1Aux1
import HRS.MP.TightAssemble
import HRS.MP.GlueFidi
import HRS.MP.InitAssemble
import HRS.MP.MartModulus
import HRS.MP.MartExist

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

/-! ### assembly -/
namespace HRS.MP.A11
open HRS HRS.Main HRS.Whole.AppendixALemmas HRS.MP.FidiAssembly
variable {d : ℕ}

local notation "q₀" => ((qT d : ℕ) : ℝ)


/-- The propagators of the Fourier modes lie in `H^{q_T}` for `t ∈ [0,T]`. -/
theorem a11_hU {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ} {𝔈 : ℕ → ℝ} (S : MainData d)
    (R : ∀ N, Realization d N)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d + 2) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S.T) (k : NonzeroLattice d) :
    HRS.MemSobolev ((qT d : ℕ) : ℝ) (propagator (S.dyn N) (S.ρ N) 0 t (Torus.realMode k)) := by
  have hA := HRS.Main.A9.a9_adjointData (show PDE.mStar d ≤ gammaIdx d + 2 by unfold gammaIdx; omega)
    hS hN
  exact HRS.MP.InitAsm.mia_memq S.hd S.hs0 S.hsd (S.dyn N) (S.ρ N) hA ht
    (HRS.StaticLimitAux.isSmooth_realMode' k)

/-- The remainder `ℝ_N = σ_NΞ_N - 𝓘_{N,emp} - 𝕄_N` (set to `0` off `[0,T]`) is a representative of the
remainder functional. -/
theorem a11_remT {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ} {𝔈 : ℕ → ℝ} (S : MainData d)
    (R : ∀ N, Realization d N)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d + 2) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    (ℱ : Filtration ℝ (R N).mΩ) (W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ)
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    (Mq : ℝ → (R N).Ω → NegSobolev d ((qT d : ℕ) : ℝ))
    (hMq : IsStochConvT (R N).P ℱ W' (S.dyn N) (S.ρ N) (S.sigma N) ((qT d : ℕ) : ℝ) S.T (R N).X Mq) :
    IsRemainderT (R N).P (S.dyn N) (S.ρ N) (S.sigma N) ((qT d : ℕ) : ℝ) S.T (R N).X
      (fun t ζ => if t ∈ Set.Icc (0 : ℝ) S.T then S.sigma N • NegSobolev.ofMeasureDiff ((qT d : ℕ) : ℝ)
          (empirical ((R N).X (Real.toNNReal t) ζ)) (withDensityReal (S.ρ N t)) -
        transportedEmpT S R (qT d) N t ζ - Mq t ζ else 0) := by
  have hSm : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 :=
    A9.a9_standing_mono (by unfold gammaIdx; omega) hS
  obtain ⟨-, hq2⟩ := HRS.MP.InitMod.mim_gamma_bounds (d := d)
  refine ⟨fun t => ?_, fun t ht φ hφ hφ0 => ?_⟩
  · by_cases ht : t ∈ Set.Icc (0 : ℝ) S.T
    · simp only [if_pos ht]
      exact (((HRS.MP.FixedTimeTight.mpt_fluc_measurable hSm (by omega) _ (by linarith) t)).sub
        (HRS.MP.InitAsm.mia_emp_measurable S R N t (hS.flow N (by omega)).init_meas
          (fun k => a11_hU S R hS (by omega) ht k))).sub (hMq.1 t)
    · simp only [if_neg ht]
      exact measurable_const
  · simp only [if_pos ht]
    filter_upwards [HRS.MP.DualDec.mdd_eval_decomp S R hS hN ℱ W' hF ht φ hφ hφ0,
      hMq.2 t ht φ hφ hφ0] with ζ h1 h2
    rw [HRS.GF.gf_eval_sub_proof _ _ hφ, HRS.GF.gf_eval_sub_proof _ _ hφ, h1, h2]
    ring

theorem main_torus_path_proof (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∀ (S : MainData d) (hs : S.s = s) (hT : S.T = T)
    (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ)
    (hstand : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d + 2) C₀ Cc 𝔈)
    (m₀ : ℕ) (ε : ℕ → ℝ) (hinit : InitialFluctuation S R m₀ Cin ε (fun _ => ∅))
    (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ))
    (νin : Measure (NegSobolev d (gammaIdx d : ℝ)))
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin)
    (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d))
    (hεf : Tendsto εf atTop (𝓝 0)),
    (∀ N : ℕ, 1 ≤ N → ∀ᵐ ω ∂(R N).P,
      Continuous fun t : Set.Icc (0 : ℝ) T =>
        S.sigma N • NegSobolev.ofMeasureDiff ((gammaIdx d + 2 : ℕ) : ℝ)
          (empirical ((R N).X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t))) ∧
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Y₀ : Ω' → NegSobolev d ((gammaIdx d + 2 : ℕ) : ℝ))
      (Y : ℝ → Ω' → NegSobolev d ((gammaIdx d + 2 : ℕ) : ℝ)),
      Measurable Y₀ →
      law P' Y₀ = νin.map (NegSobolev.embed ((gammaIdx d + 2 : ℕ) : ℝ)) →
      IsLinearFluctuationSolution P' (L.dyn S) L.ρ ((gammaIdx d + 2 : ℕ) : ℝ) L.invβstar T
        (fun ω => L.A • Y₀ ω) Y →
      ConvergesInLaw
        (fun N => law (R N).P
          (flucPath ((gammaIdx d + 2 : ℕ) : ℝ) T (S.sigma N) (R N).X (S.ρ N)))
        (law P' (toPath ((gammaIdx d + 2 : ℕ) : ℝ) T Y)) := by
  classical
  obtain ⟨C1, hfix⟩ := HRS.MP.FixedTimeTight.mpt_fixed_time_tight_torus (d := d) s
  obtain ⟨C2, hfid⟩ := HRS.MP.FidiAssembly.path_fidi_smooth_proof (d := d) s
  obtain ⟨C3, hrem⟩ := HRS.MP.RemSup.path_remainder_torus_perN (d := d) s
  refine ⟨max C1 (max C2 C3), ?_⟩
  intro Rg ν₀ MB Λ T VB Cin C₀ Cc hC S hs hT R 𝔈 hstand m₀ ε hinit εf ηF νin hfield L hcoef hεf
  have hC1 : C1 ≤ C₀ := le_trans (le_max_left _ _) hC
  have hC2 : C2 ≤ C₀ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hC3 : C3 ≤ C₀ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hSγ : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈 :=
    A9.a9_standing_mono (by omega) hstand
  have hSm : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 :=
    A9.a9_standing_mono (by unfold gammaIdx; omega) hstand
  obtain ⟨-, hq2⟩ := HRS.MP.InitMod.mim_gamma_bounds (d := d)
  subst hs hT
  have hq2' : (d : ℝ) < 2 * ((gammaIdx d + 2 : ℕ) : ℝ) := hq2
  refine ⟨fun N hN => (HRS.MP.FlucPath.mpf_fluc_cont_meas hSm hN _ hq2').1, ?_⟩
  intro Ω' _ P' _ Y₀ Y hY₀ hlawY hY
  obtain ⟨νbar, hνb⟩ := S.invβ_bdd
  have hT0 : 0 < S.T := S.hT
  -- the Brownian filtrations
  have hFex : ∀ N : ℕ, ∃ (ℱ : Filtration ℝ (R N).mΩ)
      (W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ),
      1 ≤ N → IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X := by
    intro N
    by_cases hN : 1 ≤ N
    · obtain ⟨ℱ, W', h⟩ := hstand.filtered N hN
      exact ⟨ℱ, W', fun _ => h⟩
    · exact ⟨{ seq := fun _ => (R N).mΩ, mono' := fun _ _ _ => le_rfl, le' := fun _ => le_rfl },
        fun _ _ _ => 0, fun h => absurd h hN⟩
  choose ℱ W' hF using hFex
  -- the thermal stochastic convolution and its continuous version
  obtain ⟨Mq, hMq⟩ := HRS.MP.MartExist.mex_Mq_exists S R hstand ℱ W' hF
  obtain ⟨CM, hCM⟩ := HRS.MP.MartMod.path_martingale_modulus_torus_moment (d := d) S.s Rg ν₀ MB Λ
    S.T VB C₀ Cc νbar
  have hmomM := hCM S rfl rfl hνb R 𝔈 hstand ℱ W' hF Mq hMq
  obtain ⟨Mc, hMc⟩ := HRS.MP.KC.kolmogorov_modulus_tightness_proof
    (E := NegSobolev d ((qT d : ℕ) : ℝ)) S.T hT0 (fun N => (R N).P) Mq
    (fun N hN t => (hMq N hN).1 t) 4 1 CM (by norm_num) (by norm_num)
    (fun N hN s' hs' t ht => by
      have h := hmomM N hN s' hs' t ht
      have e1 : ∀ x : ℝ≥0∞, x ^ (4 : ℝ) = x ^ 4 := fun x => by
        simpa using ENNReal.rpow_natCast x 4
      have e2 : |t - s'| ^ ((1 : ℝ) + 1) = |t - s'| ^ 2 := by
        rw [show ((1 : ℝ) + 1) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      simp only [e1, e2]
      exact h)
  -- the transported empirical initial field and its continuous version
  obtain ⟨CI, hCI⟩ := HRS.MP.InitAsm.path_initial_modulus_torus_proof (d := d) S.s Rg ν₀ MB Λ S.T VB Cin C₀ Cc νbar
  obtain ⟨Ic, hIc⟩ := (hCI S rfl rfl hνb R 𝔈 hstand m₀ ε (fun _ => ∅) hinit εf ηF νin hfield).2.2.1
  -- the three-term decomposition
  let Zf : ∀ N, ℝ → (R N).Ω → NegSobolev d q₀ := fun N t ζ => S.sigma N •
    NegSobolev.ofMeasureDiff q₀ (empirical ((R N).X (Real.toNNReal t) ζ)) (withDensityReal (S.ρ N t))
  have hZmeas : ∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Zf N t) := fun N hN t =>
    HRS.MP.FixedTimeTight.mpt_fluc_measurable hSm hN q₀ (by linarith) t
  have hZcont : ∀ N : ℕ, 1 ≤ N → ∀ᵐ ζ ∂(R N).P, Continuous fun t : Set.Icc (0 : ℝ) S.T => Zf N t ζ :=
    fun N hN => (HRS.MP.FlucPath.mpf_fluc_cont_meas hSm hN q₀ hq2).1
  have hZpath : ∀ N : ℕ, 1 ≤ N → AEMeasurable (fun ζ => contPathOf S.T (fun t => Zf N t ζ)) (R N).P :=
    fun N hN => (HRS.MP.FlucPath.mpf_fluc_cont_meas hSm hN q₀ hq2).2
  let Rm : ∀ N, ℝ → (R N).Ω → NegSobolev d q₀ := fun N t ζ =>
    if t ∈ Set.Icc (0 : ℝ) S.T then Zf N t ζ - transportedEmpT S R (qT d) N t ζ - Mq N t ζ else 0
  let Rc : ∀ N, ℝ → (R N).Ω → NegSobolev d q₀ := fun N t ζ => Zf N t ζ - Ic N t ζ - Mc N t ζ
  have hHas : ∀ N : ℕ, 1 ≤ N → HasContVersion S.T (R N).P (Rm N) (Rc N) := by
    intro N hN
    refine ⟨fun t ht => ?_, ?_⟩
    · filter_upwards [hIc.1 N hN t ht, hMc.1 N hN t ht] with ζ h1 h2
      simp only [Rc, Rm, if_pos ht, h1, h2]
    · filter_upwards [hZcont N hN, hIc.2.1 N hN, hMc.2.1 N hN] with ζ h1 h2 h3
      exact (continuousOn_iff_continuous_restrict.2 ((h1.sub h2).sub h3))
  obtain ⟨C, hCrem⟩ := hrem Rg ν₀ MB Λ S.T VB C₀ Cc hC3
  have hsup : ∀ N : ℕ, 2 ≤ N → ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) S.T, ‖Zf N t ζ - Ic N t ζ - Mc N t ζ‖ₑ ∂(R N).P ≤
      ENNReal.ofReal (C * S.T * S.sigma N * 𝔈 N) := fun N hN =>
    hCrem S rfl rfl R 𝔈 hSγ N hN (Rm N) (Rc N)
      (a11_remT S R hstand hN (ℱ N) (W' N) (hF N (by omega)) (Mq N) (hMq N (by omega)))
      (hHas N (by omega))
  -- tightness of the path laws (shifted by one: `N = n + 1 ≥ 2`)
  have hc : Tendsto (fun n : ℕ => C * S.T * S.sigma (n + 1) * 𝔈 (n + 1)) atTop (𝓝 0) := by
    have h := (hstand.energy.small.comp (tendsto_add_atTop_nat 1)).const_mul (C * S.T)
    simp only [mul_zero] at h
    refine h.congr fun n => ?_
    simp [mul_assoc]
  have hshift : ∀ (F : ℕ → (ℝ → ℝ≥0∞)), True := fun _ => trivial
  have hItight : ∀ ε : ℝ, 0 < ε → Tendsto (fun δ : ℝ =>
      ⨆ n : ℕ, ⨆ (_ : 1 ≤ n), (R (n + 1)).P {ζ | ENNReal.ofReal ε <
        omegaE (fun t => Ic (n + 1) t ζ) S.T δ}) (𝓝[>] 0) (𝓝 0) := fun ε hε =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hIc.2.2.2.1 ε hε)
      (fun δ => zero_le) (fun δ => iSup_le fun n => iSup_le fun hn =>
        le_iSup₂_of_le (n + 1) (by omega) le_rfl)
  have hMtight : ∀ ε : ℝ, 0 < ε → Tendsto (fun δ : ℝ =>
      ⨆ n : ℕ, ⨆ (_ : 1 ≤ n), (R (n + 1)).P {ζ | ENNReal.ofReal ε <
        omegaE (fun t => Mc (n + 1) t ζ) S.T δ}) (𝓝[>] 0) (𝓝 0) := fun ε hε =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hMc.2.2.2.1 ε hε)
      (fun δ => zero_le) (fun δ => iSup_le fun n => iSup_le fun hn =>
        le_iSup₂_of_le (n + 1) (by omega) le_rfl)
  have hfixN := fun t (ht : t ∈ Set.Icc (0 : ℝ) S.T) =>
    hfix Rg ν₀ MB Λ S.T VB Cin C₀ Cc hC1 S rfl rfl R 𝔈 hstand m₀ ε hinit εf ηF νin hfield t ht
  have htightc := HRS.MP.TightAsm.mta_tight (E := NegSobolev d q₀) S.T hT0
    (Ω := fun n => (R (n + 1)).Ω) (fun n => (R (n + 1)).P) (fun n t ζ => Zf (n + 1) t ζ)
    (fun n => Ic (n + 1)) (fun n => Mc (n + 1))
    (fun n hn t => hZmeas (n + 1) (by omega) t) (fun n hn => hZcont (n + 1) (by omega))
    (fun n hn => hZpath (n + 1) (by omega)) hItight hMtight
    (fun n => C * S.T * S.sigma (n + 1) * 𝔈 (n + 1)) hc
    (fun n hn => hsup (n + 1) (by omega))
    (fun t ht => (hfixN t ht).subset (by rintro _ ⟨n, hn, rfl⟩; exact ⟨n + 1, by omega, rfl⟩))
  have htight : IsTightMeasureSet (Set.range fun n : ℕ => (R (n + 2)).P.map
      (flucPath q₀ S.T (S.sigma (n + 2)) (R (n + 2)).X (S.ρ (n + 2)))) :=
    htightc.subset (by rintro _ ⟨n, rfl⟩; exact ⟨n + 1, by omega, rfl⟩)
  -- finite-dimensional convergence and conclusion
  have hΦ : ∀ n : ℕ, AEMeasurable (fun ζ => flucPath q₀ S.T (S.sigma (n + 2)) (R (n + 2)).X
      (S.ρ (n + 2)) ζ) (R (n + 2)).P := fun n =>
    (HRS.MP.FlucPath.mpf_fluc_cont_meas hSm (by omega) q₀ hq2).2
  have hΨ := HRS.MP.FlucPath.mpf_toPath_aemeasurable hY
  have hfidi := HRS.MP.GlueFidi.mgf_fidi S R hstand P' _ _ _ _ Y hY (fun p ts hts φ hφ =>
    hfid Rg ν₀ MB Λ S.T VB Cin C₀ Cc hC2 S rfl rfl R 𝔈 hstand p ts φ hts hφ m₀ ε hinit εf ηF νin
      hfield L hcoef hεf P' Y₀ Y hY₀ hlawY hY)
  have hconv := HRS.AdjK.adjk_convergence_of_tight_fidi_proof q₀ S.T hT0.le
    (fun n => (R (n + 2)).P)
    (fun n ζ => flucPath q₀ S.T (S.sigma (n + 2)) (R (n + 2)).X (S.ρ (n + 2)) ζ) P'
    (toPath q₀ S.T Y) hΦ hΨ htight hfidi
  exact HRS.MP.GlueFidi.mgf_final (fun N => (R N).P) P'
    (fun N ζ => flucPath q₀ S.T (S.sigma N) (R N).X (S.ρ N) ζ) (toPath q₀ S.T Y) hconv

end HRS.MP.A11

/-- Relocation check: the proof above proves the frozen statement of Theorem A.11 verbatim. -/
example := (@HRS.MP.A11.main_torus_path_proof : type_of% @HRS.Main.main_torus_path)
