import HRS.MP.FidiF1
import HRS.MP.FidiCov
import HRS.MP.FidiLaw

/-!
# Chunk F (`MP:`), Lemma S.A.26 (torus): finite-dimensional convergence for Theorem A.11

Assembly of the packets F1 (coupling of the particle statistics to the surrogate built from the A.5 field),
F2 (transfer of convergence in law along a vanishing smooth-test distance), F3 (convergence in law of the
surrogates on the field space), and F4 (the law of the statistics of a linear fluctuation solution).
The statement is the frozen `HRS.Whole.AppendixALemmas.path_fidi_torus`, copied verbatim, with the
relocation check `example := (@path_fidi_torus_proof : type_of% @path_fidi_torus)` at the end.
-/

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Main HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.FidiDefs HRS.MP.FidiF1
  HRS.MP.FidiCov HRS.MP.FidiLaw
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.MP.FidiAssembly

variable {d : ℕ}

open HRS.PDE HRS.A34 in
/-- membership of the limit propagator of a smooth test in `H^{γ+2}` (level `q_T`). -/
theorem fa_memq {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {Rg : PDE.Regime}
    {MB Λ VB ν₀ T : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (hA : AdjointData s (gammaIdx d + 2) Rg MB Λ VB D ν₀ T ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    MemSobolev ((gammaIdx d + 2 : ℕ) : ℝ) (propagator D ρ 0 t φ) := by
  have hJ : mStar d ≤ gammaIdx d + 2 := by unfold gammaIdx; omega
  have hφc : Continuous φ := HRS.A33.a33_cont hφ
  have hφm : MemSobolev ((gammaIdx d + 2 : ℕ) : ℝ) φ := HRS.A33.a33_memSob _ hφ
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [a34_prop_zero hd (gammaIdx d + 2) hJ Rg s MB Λ VB ν₀ T D ρ hA hφc hφm]
    exact hφm
  · obtain ⟨K, K₂, -, -, hu⟩ := a34_unif hd s hs0 hsd (gammaIdx d + 2) hJ Rg MB Λ VB ν₀ T
    obtain ⟨-, hr⟩ := hu D ρ hA ⟨hpos, ht.2⟩ hφc hφm
    obtain ⟨h1, -, -⟩ := hr 0 ⟨le_rfl, hpos.le⟩
    exact (h1 (gammaIdx d + 2) (by unfold gammaIdx; omega) le_rfl).1

open HRS.Main.A8P in
theorem path_fidi_smooth_proof (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∀ (S : Main.MainData d) (hs : S.s = s) (hT : S.T = T)
    (R : ∀ N, Main.Realization d N) (𝔈 : ℕ → ℝ)
    (hstand : Main.TorusStanding S R Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) C₀ Cc 𝔈)
    (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (hφ : ∀ a, Torus.IsSmooth (φ a))
    (m₀ : ℕ) (ε : ℕ → ℝ) (hinit : Main.InitialFluctuation S R m₀ Cin ε (fun _ => ∅))
    (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (Main.gammaIdx d : ℝ))
    (νin : Measure (NegSobolev d (Main.gammaIdx d : ℝ)))
    (hfield : Main.InitialFluctuationField S R (Main.gammaIdx d) Cin εf ηF νin)
    (L : Main.LimitCoeffs d)
    (hcoef : Main.CoeffConvergence S L Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) (Main.gammaIdx d))
    (hεf : Tendsto εf atTop (𝓝 0)),
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Y₀ : Ω' → NegSobolev d ((qT d : ℕ) : ℝ)) (Y : ℝ → Ω' → NegSobolev d ((qT d : ℕ) : ℝ)),
      Measurable Y₀ → law P' Y₀ = νin.map (NegSobolev.embed ((qT d : ℕ) : ℝ)) →
      HRS.IsLinearFluctuationSolution P' (L.dyn S) L.ρ ((qT d : ℕ) : ℝ) L.invβstar T
        (fun ζ => L.A • Y₀ ζ) Y →
      Main.ConvergesInLaw
        (fun N => Main.fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (law P' (fun ζ => (WithLp.toLp 2 fun a => NegSobolev.eval (Y (ts a) ζ) (φ a) :
          EuclideanSpace ℝ (Fin p)))) := by
  by_cases hok : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  swap
  · refine ⟨0, fun Rg ν₀ MB Λ T VB Cin C₀ Cc _ S hs => ?_⟩
    exact absurd ⟨S.hd, hs ▸ S.hs0, hs ▸ S.hsd⟩ hok
  obtain ⟨hd, hs0, hsd⟩ := hok
  obtain ⟨C₀', Cq, hC₀', hCq, hcom⟩ := a8p_commSpec hd hs0 hsd
  refine ⟨C₀', fun Rg ν₀ MB Λ T VB Cin C₀ Cc hC S hs hT R 𝔈 hstand p ts φ hts hφ m₀ ε hinit εf ηF
    νin hfield L hcoef hεf Ω' _ P' _ Y₀ Y hY₀ hlaw hY => ?_⟩
  subst hs hT
  obtain ⟨Ca, Λ₁, hCa, hspec⟩ := a8p_adjSpec hd S.s hs0 hsd Rg MB Λ VB ν₀
  obtain ⟨Cp, hCp0, hCp⟩ := a8p_hom_prod hd hs0 hsd
  obtain ⟨cT, hcT0, hcT⟩ := a8p_transport_bound hd MB S.s hs0
  obtain ⟨K, hK0, hK⟩ := fi1_hIdiff hd S.s hs0 hsd Rg MB Λ VB ν₀ S.T
  have hmS : PDE.mStar d ≤ gammaIdx d + 2 := by unfold gammaIdx; omega
  have hSm : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 := A9.a9_standing_mono hmS hstand
  have hSg : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈 :=
    A9.a9_standing_mono (by omega) hstand
  have hsm : ∀ a, Torus.IsSmooth (φ a) := hφ
  -- the constant comparing `H^γ` and `H^{m_*}` norms of the finitely many tests
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ a, K * sobolevNorm (gammaIdx d : ℝ) (φ a) ≤
      c * sobolevNorm (PDE.mStar d : ℝ) (φ a) := by
    choose ca hca0 hca using fun a => fi1_smooth_sob (PDE.mStar d : ℝ) (gammaIdx d : ℝ) (hφ a)
    refine ⟨K * ∑ a, ca a, mul_nonneg hK0 (Finset.sum_nonneg fun a _ => hca0 a), fun a => ?_⟩
    have hle : ca a ≤ ∑ b, ca b := Finset.single_le_sum (fun b _ => hca0 b) (Finset.mem_univ a)
    have h0 : 0 ≤ sobolevNorm (PDE.mStar d : ℝ) (φ a) := Real.sqrt_nonneg _
    calc K * sobolevNorm (gammaIdx d : ℝ) (φ a) ≤ K * (ca a * sobolevNorm (PDE.mStar d : ℝ) (φ a)) :=
          mul_le_mul_of_nonneg_left (hca a) hK0
      _ ≤ K * ((∑ b, ca b) * sobolevNorm (PDE.mStar d : ℝ) (φ a)) := by gcongr
      _ = _ := by ring
  -- pointwise facts
  have hφc : ∀ a, Continuous (φ a) := fun a => A33.a33_cont (hsm a)
  have hφm : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a) := fun a => A33.a33_memSob _ (hsm a)
  have hts' : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T := hts
  have hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT :=
    ⟨hCa.le, hspec, hcom, hCq.le, hC, hCp0, hCp, hcT0, hcT⟩
  set R' := etaF R (gammaIdx d) ηF with hR'
  have hSR' : TorusStanding S R' Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 := fi1_standing _ ηF hSm
  -- the rate
  have hrate : Tendsto (fun N => masterRate d (c * εf N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N)
      atTop (𝓝 0) :=
    a8p_rate_tendsto S hd (fun N => c * εf N) 𝔈 (by simpa using hεf.const_mul c)
      hSm.energy.small (fun N hN => (hSm.energy.pos N hN).le)
  -- the coupling bound, `N ≥ 2`
  have hbound : ∀ N : ℕ, 2 ≤ N →
      smoothDist 2 (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (R N).P (R' N).η) ≤
      ((1 / 2) * Cq * cT * S.T + 1 + 4 * S.T * d * Ca ^ 2 + 2 * S.T * Cq * (2 * d * Ca ^ 2 + Cp)) *
        ((∑ a, a8pK Λ₁ (ts a) (φ a)) + (∑ a, a8pK Λ₁ (ts a) (φ a)) ^ 2) *
        masterRate d (c * εf N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N := by
    intro N hN2
    have hN1 : 1 ≤ N := by omega
    have hε := hfield.εf_nonneg N hN1
    refine a8p_smooth_iota (R := R') hspec hCa.le hSR' hN2 hcom hCq.le hC hCp0 hCp hcT0 hcT ts hts' φ hφc
      hφm (a8p_nullContact hSm hN1) (fi1_eta_meas hfield N) (mul_nonneg hc0 hε) (fun a => ?_)
    refine (hK S rfl rfl R 𝔈 C₀ Cc hSg Cin εf ηF νin hfield N hN1 (ts a) (hts' a) (φ a) (hsm a)).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hc a
    have h2 : sobolevNorm (PDE.mStar d : ℝ) (φ a) ≤ a8pK Λ₁ (ts a) (φ a) := by
      have h0 : 0 ≤ sobolevNorm (PDE.mStar d : ℝ) (φ a) := Real.sqrt_nonneg _
      have : 1 ≤ Real.exp (|Λ₁| * ts a) := Real.one_le_exp (mul_nonneg (abs_nonneg _) (hts' a).1)
      unfold a8pK
      nlinarith
    calc εf N * (K * sobolevNorm (gammaIdx d : ℝ) (φ a))
        ≤ εf N * (c * sobolevNorm (PDE.mStar d : ℝ) (φ a)) := mul_le_mul_of_nonneg_left h1 hε
      _ ≤ εf N * (c * a8pK Λ₁ (ts a) (φ a)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hc0) hε
      _ = c * εf N * a8pK Λ₁ (ts a) (φ a) := by ring
  -- weak convergence of the surrogates (F3) and identification of the limit (F4)
  have hsurr : ∀ N : ℕ, 2 ≤ N →
      surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (R N).P (R' N).η =
        fieldSurr (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (gammaIdx d : ℝ) νin := fun N hN2 =>
    fi3c_surr_eq hfield (by omega) ts φ
      (fun a => (fi3a_prop S L hcoef (hts' a) (hsm a)).1 N (by omega) |>.1)
  haveI hνin : IsProbabilityMeasure νin := by
    rw [← hfield.law_eq 1 le_rfl]; infer_instance
  have hprop := fun a => fi3a_prop S L hcoef (hts' a) (hsm a)
  have hqN : ∀ N : ℕ, 1 ≤ N → 0 ≤ S.qN N := fun N hN =>
    (HRS.A34.a34_qScale_bounds (N := N) hN (S.hκ N) (S.hinvβ N)).1
  have hlim := fi3d_converges S L hcoef ts hts' φ hsm hprop
    (fun N hN => fi3b_psd (S.dyn N) (S.ρ N) (hcoef.seq_adjoint N hN) (hqN N hN) ts hts' φ hsm)
    (fi3b_psd (L.dyn S) L.ρ hcoef.limit_adjoint L.hinvβstar ts hts' φ hsm)
    (fi3b_cov S L hcoef ts hts' φ hsm) νin
  have hid := fi4_identify S L rfl hcoef νin P' Y₀ Y hY₀ hlaw hY ts hts φ hsm
    (fun a => fa_memq hd hs0 hsd (L.dyn S) L.ρ hcoef.limit_adjoint (hts' a) (hsm a))
  have hsd0 : Tendsto (fun N => smoothDist 2
      (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
      (fieldSurr (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (gammaIdx d : ℝ) νin)) atTop (𝓝 0) := by
    have hup := hrate.const_mul
      (((1 / 2) * Cq * cT * S.T + 1 + 4 * S.T * d * Ca ^ 2 + 2 * S.T * Cq * (2 * d * Ca ^ 2 + Cp)) *
        ((∑ a, a8pK Λ₁ (ts a) (φ a)) + (∑ a, a8pK Λ₁ (ts a) (φ a)) ^ 2))
    rw [mul_zero] at hup
    refine squeeze_zero' (Eventually.of_forall fun N => smoothDist_nonneg _ _ _) ?_ hup
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [← hsurr N hN]
    exact hbound N hN
  -- probability measures along the shifted sequence (`Measure.map` is always a probability measure)
  haveI h1 : ∀ n : ℕ, IsProbabilityMeasure
      (fluctStatLaw (R (n + 2)).P (S.sigma (n + 2)) (R (n + 2)).X (S.ρ (n + 2)) ts φ) :=
    fun n => inferInstanceAs (IsProbabilityMeasure ((R (n + 2)).P.map _))
  haveI h2 : ∀ n : ℕ, IsProbabilityMeasure
      (fieldSurr (S.dyn (n + 2)) (S.ρ (n + 2)) (S.AN (n + 2)) (S.qN (n + 2)) ts φ (gammaIdx d : ℝ) νin) :=
    fun n => by unfold fieldSurr; infer_instance
  haveI h3 : IsProbabilityMeasure
      (fieldSurr (L.dyn S) L.ρ L.A L.invβstar ts φ (gammaIdx d : ℝ) νin) := by
    unfold fieldSurr; infer_instance
  rw [hid]
  refine (A9.a9_conv_shift 2).2 ?_
  exact fi2_transfer _ (fun n => fieldSurr (S.dyn (n + 2)) (S.ρ (n + 2)) (S.AN (n + 2))
    (S.qN (n + 2)) ts φ (gammaIdx d : ℝ) νin) _ ((A9.a9_conv_shift 2).1 hlim)
    (hsd0.comp (tendsto_add_atTop_nat 2))


theorem path_fidi_torus_proof (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∀ (S : Main.MainData d) (hs : S.s = s) (hT : S.T = T)
    (R : ∀ N, Main.Realization d N) (𝔈 : ℕ → ℝ)
    (hstand : Main.TorusStanding S R Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) C₀ Cc 𝔈)
    (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (hφ : ∀ a, IsTrigPolyT (φ a))
    (m₀ : ℕ) (ε : ℕ → ℝ) (hinit : Main.InitialFluctuation S R m₀ Cin ε (fun _ => ∅))
    (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (Main.gammaIdx d : ℝ))
    (νin : Measure (NegSobolev d (Main.gammaIdx d : ℝ)))
    (hfield : Main.InitialFluctuationField S R (Main.gammaIdx d) Cin εf ηF νin)
    (L : Main.LimitCoeffs d)
    (hcoef : Main.CoeffConvergence S L Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) (Main.gammaIdx d))
    (hεf : Tendsto εf atTop (𝓝 0)),
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Y₀ : Ω' → NegSobolev d ((qT d : ℕ) : ℝ)) (Y : ℝ → Ω' → NegSobolev d ((qT d : ℕ) : ℝ)),
      Measurable Y₀ → law P' Y₀ = νin.map (NegSobolev.embed ((qT d : ℕ) : ℝ)) →
      HRS.IsLinearFluctuationSolution P' (L.dyn S) L.ρ ((qT d : ℕ) : ℝ) L.invβstar T
        (fun ζ => L.A • Y₀ ζ) Y →
      Main.ConvergesInLaw
        (fun N => Main.fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (law P' (fun ζ => (WithLp.toLp 2 fun a => NegSobolev.eval (Y (ts a) ζ) (φ a) :
          EuclideanSpace ℝ (Fin p)))) := by
  obtain ⟨C₀min, h⟩ := path_fidi_smooth_proof (d := d) s
  exact ⟨C₀min, fun Rg ν₀ MB Λ T VB Cin C₀ Cc hC S hs hT R 𝔈 hstand p ts φ hts hφ m₀ ε hinit εf ηF νin
    hfield L hcoef hεf => h Rg ν₀ MB Λ T VB Cin C₀ Cc hC S hs hT R 𝔈 hstand p ts φ hts
      (fun a => fi1_trig_smooth (hφ a)) m₀ ε hinit εf ηF νin hfield L hcoef hεf⟩

end HRS.MP.FidiAssembly

example := (@HRS.MP.FidiAssembly.path_fidi_torus_proof : type_of% @HRS.Whole.AppendixALemmas.path_fidi_torus)
