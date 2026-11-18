import HRS.MP.InitModulus
import HRS.MP.KolmChentsov

/-!
# Packet MPIASM: Lemma S.A.23 (torus), assembly

The frozen statement `HRS.Whole.AppendixALemmas.path_initial_modulus_torus` is proved as
`path_initial_modulus_torus_proof` (namespace `HRS.MP.InitAsm`):

* the two moment conjuncts are `HRS.MP.InitMod.path_initial_modulus_torus_moments`;
* the two tightness conjuncts come from `HRS.MP.KC.kolmogorov_modulus_tightness_proof` with
  `E = NegSobolev d q_T`, `p = 2`, `β = 1`, applied to the clamped processes `t ↦ Z (clamp t)`
  (so that the measurability hypothesis `hZmeas`, which is required for all `t`, is available from the
  propagator membership on `[0,T]`), and transferred back to `Z` by `mia_cvt_transfer`.

The measurability facts are `mia_emp_measurable` and `mia_gauss_measurable`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.PDE HRS.Main HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate

namespace HRS.MP.InitAsm

variable {d : ℕ}

/-- `d / 2 < q_T`. -/
theorem mia_q_gt : (d : ℝ) / 2 < ((qT d : ℕ) : ℝ) := by
  obtain ⟨-, h⟩ := HRS.MP.InitMod.mim_gamma_bounds (d := d)
  linarith

/-- Measurability of the pairing `F ↦ F(ψ)` on `H^{-q}` for a test function in `H^{q}`. -/
theorem mia_eval_meas {q : ℝ} {ψ : Torus d → ℝ} (h : HRS.MemSobolev q ψ) :
    Measurable fun F : NegSobolev d q => NegSobolev.eval F ψ := by
  have : (fun F : NegSobolev d q => NegSobolev.eval F ψ) =
      fun F => inner ℝ F (HRS.Uniform.Q54.lpOf q h) := by
    funext F; exact HRS.Uniform.Q54.eval_eq_inner q F h
  rw [this]
  exact (continuous_id.inner continuous_const).measurable

/-- The set of `a` where the weighted coefficient sequence is in `ℓ²` is measurable. -/
theorem mia_memℓp_meas {α : Type*} [MeasurableSpace α] {q : ℝ} (c : NonzeroLattice d → α → ℝ)
    (hc : ∀ k, Measurable (c k)) :
    MeasurableSet {a : α | Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-q) * c k a) 2} := by
  have key : ∀ a : α, Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-q) * c k a) 2 ↔
      ∃ M : ℕ, ∀ u : Finset (NonzeroLattice d),
        ∑ k ∈ u, (Lattice.jp k.1 ^ (-q) * c k a) ^ 2 ≤ (M : ℝ) := by
    intro a
    have hn : ∀ k : NonzeroLattice d,
        ‖Lattice.jp k.1 ^ (-q) * c k a‖ ^ ((2 : ℝ≥0∞).toReal) =
          (Lattice.jp k.1 ^ (-q) * c k a) ^ 2 := by
      intro k
      rw [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    rw [memℓp_gen_iff (by norm_num)]
    simp only [hn]
    constructor
    · intro hs
      refine ⟨⌈∑' k, (Lattice.jp k.1 ^ (-q) * c k a) ^ 2⌉₊, fun u => ?_⟩
      exact (Summable.sum_le_tsum u (fun k _ => sq_nonneg _) hs).trans (Nat.le_ceil _)
    · rintro ⟨M, hM⟩
      exact summable_of_sum_le (fun k => sq_nonneg _) hM
  have hset : {a : α | Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-q) * c k a) 2} =
      ⋃ M : ℕ, ⋂ u : Finset (NonzeroLattice d),
        {a : α | ∑ k ∈ u, (Lattice.jp k.1 ^ (-q) * c k a) ^ 2 ≤ (M : ℝ)} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
    exact key a
  rw [hset]
  refine MeasurableSet.iUnion fun M => MeasurableSet.iInter fun u => ?_
  exact measurableSet_le
    (Finset.measurable_sum u fun k _ => (measurable_const.mul (hc k)).pow_const 2) measurable_const

open Classical in
/-- Coordinates of `ofSeq`: the weighted entry, or `0` when the weighted sequence is not in `ℓ²`. -/
theorem mia_coord_ofSeq (m : ℝ) (c : NonzeroLattice d → ℝ) (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.ofSeq m c) k =
      if Memℓp (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-m) * c j) 2 then
        Lattice.jp k.1 ^ (-m) * c k else 0 := by
  by_cases h : Memℓp (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-m) * c j) 2
  · rw [if_pos h, NegSobolev.ofSeq_of_mem c h]
    rfl
  · rw [if_neg h]
    simp [NegSobolev.ofSeq, NegSobolev.coord, h] <;> rfl

/-- Measurability of the transported field `F ↦ V^{t,0}F` at the index `q` (for test functions
`U^{0,t}e_k` in `H^{q}`). -/
theorem mia_transport_meas {q : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t : ℝ)
    (hU : ∀ k : NonzeroLattice d, HRS.MemSobolev q (propagator D ρ 0 t (Torus.realMode k))) :
    Measurable fun F : NegSobolev d q => transportField D ρ t q F := by
  classical
  have hc : ∀ k : NonzeroLattice d, Measurable fun F : NegSobolev d q =>
      NegSobolev.eval F (propagator D ρ 0 t (Torus.realMode k)) :=
    fun k => mia_eval_meas (hU k)
  refine HRS.Uniform.Q54c.measurable_of_coord fun k => ?_
  have hcoord : (fun F : NegSobolev d q => NegSobolev.coord (transportField D ρ t q F) k) =
      fun F => if Memℓp (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-q) *
          NegSobolev.eval F (propagator D ρ 0 t (Torus.realMode j))) 2 then
        Lattice.jp k.1 ^ (-q) * NegSobolev.eval F (propagator D ρ 0 t (Torus.realMode k)) else 0 := by
    funext F
    unfold transportField
    exact mia_coord_ofSeq q (fun j => NegSobolev.eval F (propagator D ρ 0 t (Torus.realMode j))) k
  rw [hcoord]
  exact Measurable.ite
    (mia_memℓp_meas (fun j (F : NegSobolev d q) => NegSobolev.eval F (propagator D ρ 0 t (Torus.realMode j))) hc)
    (measurable_const.mul (hc k)) measurable_const

/-- Measurability of the embedding `H^{γ} ↪ H^{q}` (as a map of the source element). -/
theorem mia_embed_meas {γ q : ℝ} : Measurable fun F : NegSobolev d γ => NegSobolev.embed q F := by
  classical
  have hc : ∀ k : NonzeroLattice d, Measurable fun F : NegSobolev d γ => NegSobolev.fourierCoeff F k :=
    fun k => (HRS.FieldSingAux.coordCLM γ k).continuous.measurable
  refine HRS.Uniform.Q54c.measurable_of_coord fun k => ?_
  have hcoord : (fun F : NegSobolev d γ => NegSobolev.coord (NegSobolev.embed q F) k) =
      fun F => if Memℓp (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-q) *
          NegSobolev.fourierCoeff F j) 2 then
        Lattice.jp k.1 ^ (-q) * NegSobolev.fourierCoeff F k else 0 := by
    funext F
    unfold NegSobolev.embed
    exact mia_coord_ofSeq q (fun j => NegSobolev.fourierCoeff F j) k
  rw [hcoord]
  exact Measurable.ite
    (mia_memℓp_meas (fun j (F : NegSobolev d γ) => NegSobolev.fourierCoeff F j) hc)
    (measurable_const.mul (hc k)) measurable_const

/-- Measurability of `ζ ↦ 𝓘_{N,emp}^t` (`transportedEmpT`) for `N ≥ 1` and any time `t` at which the
coordinate test functions `U^{0,t}e_k` lie in `H^{q_T}`; the only input on the probability space is the
measurability of the initial configuration `X₀`. -/
theorem mia_emp_measurable (S : Main.MainData d) (R : ∀ N, Main.Realization d N) (N : ℕ) (t : ℝ)
    (hX0 : Measurable (R N).X₀)
    (hU : ∀ k : NonzeroLattice d,
      HRS.MemSobolev ((qT d : ℕ) : ℝ) (propagator (S.dyn N) (S.ρ N) 0 t (Torus.realMode k))) :
    Measurable (fun ζ => transportedEmpT S R (qT d) N t ζ) := by
  unfold transportedEmpT
  refine (measurable_const_smul (S.AN N)).comp
    ((mia_transport_meas (S.dyn N) (S.ρ N) t hU).comp ?_)
  exact (measurable_const_smul (S.κ N)).comp
    ((HRS.GF.gf_measurable_ofMeasureDiff_proof (N := N) ((qT d : ℕ) : ℝ) mia_q_gt S.μ0).comp hX0)

/-- Measurability of `ζ ↦ 𝓘_N^t` (`transportedGaussT`) for `N ≥ 1` and any time `t` at which the
coordinate test functions `U^{0,t}e_k` lie in `H^{q_T}`; the only input on the probability space is the
measurability of the initial field `ηF N`. -/
theorem mia_gauss_measurable (S : Main.MainData d) (R : ∀ N, Main.Realization d N)
    (ηF : ∀ N, (R N).Ω → NegSobolev d (Main.gammaIdx d : ℝ)) (N : ℕ) (t : ℝ)
    (hη : Measurable (ηF N))
    (hU : ∀ k : NonzeroLattice d,
      HRS.MemSobolev ((qT d : ℕ) : ℝ) (propagator (S.dyn N) (S.ρ N) 0 t (Torus.realMode k))) :
    Measurable (fun ζ => transportedGaussT S R (qT d) (Main.gammaIdx d) ηF N t ζ) := by
  unfold transportedGaussT
  exact (measurable_const_smul (S.AN N)).comp
    ((mia_transport_meas (S.dyn N) (S.ρ N) t hU).comp ((mia_embed_meas).comp hη))

/-- The clamp of a time to `[0, T]`. -/
def mia_clamp (T t : ℝ) : ℝ := max 0 (min t T)

theorem mia_clamp_mem {T : ℝ} (hT : 0 < T) (t : ℝ) : mia_clamp T t ∈ Set.Icc (0 : ℝ) T :=
  ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩

theorem mia_clamp_eq {T t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) : mia_clamp T t = t := by
  unfold mia_clamp
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-- Transfer of `ContVersionTight` across processes that agree on `[0,T]`. -/
theorem mia_cvt_transfer {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {T : ℝ} {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    (Z Z' Zc : ∀ N, ℝ → Ω N → E)
    (hZ : ∀ N t ζ, t ∈ Set.Icc (0 : ℝ) T → Z' N t ζ = Z N t ζ)
    (h : ContVersionTight T P Z' Zc) : ContVersionTight T P Z Zc := by
  unfold ContVersionTight at h ⊢
  obtain ⟨c1, c2, c3, c4, c5⟩ := h
  refine ⟨fun N hN t ht => ?_, c2, c3, c4, fun htight => c5 fun t ht => ?_⟩
  · filter_upwards [c1 N hN t ht] with ζ hζ
    exact hζ.trans (hZ N t ζ ht)
  · have hset : {μ : Measure E | ∃ N : ℕ, 1 ≤ N ∧ μ = (P N).map (Z' N t)} =
        {μ : Measure E | ∃ N : ℕ, 1 ≤ N ∧ μ = (P N).map (Z N t)} := by
      have hf : ∀ N, Z' N t = Z N t := fun N => funext fun ζ => hZ N t ζ ht
      simp only [hf]
    rw [hset]
    exact htight t ht

open HRS.A34 in
/-- The field membership of the propagator of a smooth test at the level `q_T`, from the adjoint data at
that level (as in `HRS.MP.FidiAssembly.fa_memq`). -/
theorem mia_memq {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {Rg : PDE.Regime}
    {MB Λ VB ν₀ T : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (hA : PDE.AdjointData s (gammaIdx d + 2) Rg MB Λ VB D ν₀ T ρ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    HRS.MemSobolev ((gammaIdx d + 2 : ℕ) : ℝ) (propagator D ρ 0 t φ) := by
  have hJ : PDE.mStar d ≤ gammaIdx d + 2 := by unfold gammaIdx; omega
  have hφc : Continuous φ := HRS.A33.a33_cont hφ
  have hφm : HRS.MemSobolev ((gammaIdx d + 2 : ℕ) : ℝ) φ := HRS.A33.a33_memSob _ hφ
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [a34_prop_zero hd (gammaIdx d + 2) hJ Rg s MB Λ VB ν₀ T D ρ hA hφc hφm]
    exact hφm
  · obtain ⟨K, K₂, -, -, hu⟩ := a34_unif hd s hs0 hsd (gammaIdx d + 2) hJ Rg MB Λ VB ν₀ T
    obtain ⟨-, hr⟩ := hu D ρ hA ⟨hpos, ht.2⟩ hφc hφm
    obtain ⟨h1, -, -⟩ := hr 0 ⟨le_rfl, hpos.le⟩
    exact (h1 (gammaIdx d + 2) (by unfold gammaIdx; omega) le_rfl).1

/-- Lemma S.A.23, torus part (frozen statement `HRS.Whole.AppendixALemmas.path_initial_modulus_torus`,
copied verbatim). -/
theorem path_initial_modulus_torus_proof (s : ℝ) (Rg : PDE.Regime)
    (ν₀ MB Λ T VB Cin C₀ Cc νbar : ℝ) :
    ∃ C : ℝ, ∀ (S : Main.MainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      ∀ (R : ∀ N, Main.Realization d N) (𝔈 : ℕ → ℝ),
        Main.TorusStanding S R Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) C₀ Cc 𝔈 →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ) (Ψ : ℕ → Set (Torus d → ℝ)), Main.InitialFluctuation S R m₀ Cin ε Ψ →
        ∀ (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (Main.gammaIdx d : ℝ))
          (νin : Measure (NegSobolev d (Main.gammaIdx d : ℝ))),
          Main.InitialFluctuationField S R (Main.gammaIdx d) Cin εf ηF νin →
        (∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ‖transportedEmpT S R (qT d) N t ζ - transportedEmpT S R (qT d) N s' ζ‖ₑ ^ 2 ∂(R N).P +
            ∫⁻ ζ, ‖transportedGaussT S R (qT d) (Main.gammaIdx d) ηF N t ζ -
              transportedGaussT S R (qT d) (Main.gammaIdx d) ηF N s' ζ‖ₑ ^ 2 ∂(R N).P ≤
          ENNReal.ofReal (C * |t - s'| ^ 2)) ∧
        (∀ L : Main.LimitCoeffs d,
          Main.CoeffConvergence S L Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) (Main.gammaIdx d) →
          ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
            ∫⁻ F, ‖L.A • Main.transportField (L.dyn S) L.ρ t ((qT d : ℕ) : ℝ)
                (NegSobolev.embed ((qT d : ℕ) : ℝ) F) -
              L.A • Main.transportField (L.dyn S) L.ρ s' ((qT d : ℕ) : ℝ)
                (NegSobolev.embed ((qT d : ℕ) : ℝ) F)‖ₑ ^ 2 ∂νin ≤
            ENNReal.ofReal (C * |t - s'| ^ 2)) ∧
        (∃ Zc, ContVersionTight (E := NegSobolev d ((qT d : ℕ) : ℝ)) T (fun N => (R N).P)
          (fun N t ζ => transportedEmpT S R (qT d) N t ζ) Zc) ∧
        (∃ Zc, ContVersionTight (E := NegSobolev d ((qT d : ℕ) : ℝ)) T (fun N => (R N).P)
          (fun N t ζ => transportedGaussT S R (qT d) (Main.gammaIdx d) ηF N t ζ) Zc) := by
  obtain ⟨C, hC⟩ := HRS.MP.InitMod.path_initial_modulus_torus_moments (d := d) s Rg ν₀ MB Λ T VB Cin
    C₀ Cc νbar
  refine ⟨C, fun S hs hT hν R 𝔈 hS m₀ ε Ψ hinit εf ηF νin hfield => ?_⟩
  obtain ⟨h1, h2⟩ := hC S hs hT hν R 𝔈 hS m₀ ε Ψ hinit εf ηF νin hfield
  have hTpos : 0 < T := hT ▸ S.hT
  have hd : 1 ≤ d := S.hd
  have hX0 : ∀ N : ℕ, 1 ≤ N → Measurable (R N).X₀ := fun N hN => (hS.flow N hN).init_meas
  have hU : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d,
      HRS.MemSobolev ((qT d : ℕ) : ℝ) (propagator (S.dyn N) (S.ρ N) 0 t (Torus.realMode k)) := by
    intro N hN t ht k
    have hA : PDE.AdjointData s (gammaIdx d + 2) Rg MB Λ VB (S.dyn N) ν₀ T (S.ρ N) := by
      have h := HRS.Main.A9.a9_adjointData (show PDE.mStar d ≤ gammaIdx d + 2 by unfold gammaIdx; omega)
        hS hN
      rw [hs, hT] at h
      exact h
    exact mia_memq hd (hs ▸ S.hs0) (hs ▸ S.hsd) (S.dyn N) (S.ρ N) hA ht
      (HRS.StaticLimitAux.isSmooth_realMode' k)
  have hZE : ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ,
      Measurable (fun ζ => transportedEmpT S R (qT d) N (mia_clamp T t) ζ) :=
    fun N hN t => mia_emp_measurable S R N (mia_clamp T t) (hX0 N hN) (hU N hN _ (mia_clamp_mem hTpos t))
  have hZG : ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ,
      Measurable (fun ζ => transportedGaussT S R (qT d) (Main.gammaIdx d) ηF N (mia_clamp T t) ζ) :=
    fun N hN t => mia_gauss_measurable S R ηF N (mia_clamp T t) (hfield.ηF_meas N)
      (hU N hN _ (mia_clamp_mem hTpos t))
  have hmE : ∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖transportedEmpT S R (qT d) N (mia_clamp T t) ζ -
          transportedEmpT S R (qT d) N (mia_clamp T s') ζ‖ₑ ^ (2 : ℝ) ∂(R N).P ≤
        ENNReal.ofReal (C * |t - s'| ^ (1 + (1 : ℝ))) := by
    intro N hN s' hs' t ht
    rw [mia_clamp_eq ht, mia_clamp_eq hs']
    have h := h1 N hN s' hs' t ht
    rw [show |t - s'| ^ (1 + (1 : ℝ)) = |t - s'| ^ 2 by
      rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two]]
    simp only [ENNReal.rpow_two]
    exact le_trans le_self_add h
  have hmG : ∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖transportedGaussT S R (qT d) (Main.gammaIdx d) ηF N (mia_clamp T t) ζ -
          transportedGaussT S R (qT d) (Main.gammaIdx d) ηF N (mia_clamp T s') ζ‖ₑ ^ (2 : ℝ) ∂(R N).P ≤
        ENNReal.ofReal (C * |t - s'| ^ (1 + (1 : ℝ))) := by
    intro N hN s' hs' t ht
    rw [mia_clamp_eq ht, mia_clamp_eq hs']
    have h := h1 N hN s' hs' t ht
    rw [show |t - s'| ^ (1 + (1 : ℝ)) = |t - s'| ^ 2 by
      rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two]]
    simp only [ENNReal.rpow_two]
    exact le_trans le_add_self h
  obtain ⟨Zc1, hZc1⟩ := HRS.MP.KC.kolmogorov_modulus_tightness_proof (E := NegSobolev d ((qT d : ℕ) : ℝ))
    (Ω := fun N => (R N).Ω) T hTpos (fun N => (R N).P)
    (fun N t ζ => transportedEmpT S R (qT d) N (mia_clamp T t) ζ) hZE 2 1 C (by norm_num) (by norm_num) hmE
  obtain ⟨Zc2, hZc2⟩ := HRS.MP.KC.kolmogorov_modulus_tightness_proof (E := NegSobolev d ((qT d : ℕ) : ℝ))
    (Ω := fun N => (R N).Ω) T hTpos (fun N => (R N).P)
    (fun N t ζ => transportedGaussT S R (qT d) (Main.gammaIdx d) ηF N (mia_clamp T t) ζ) hZG 2 1 C
    (by norm_num) (by norm_num) hmG
  exact ⟨h1, h2,
    ⟨Zc1, mia_cvt_transfer (fun N => (R N).P) (fun N t ζ => transportedEmpT S R (qT d) N t ζ)
      (fun N t ζ => transportedEmpT S R (qT d) N (mia_clamp T t) ζ) Zc1
      (fun N t ζ ht => by simp only [mia_clamp_eq ht]) hZc1⟩,
    ⟨Zc2, mia_cvt_transfer (fun N => (R N).P)
      (fun N t ζ => transportedGaussT S R (qT d) (Main.gammaIdx d) ηF N t ζ)
      (fun N t ζ => transportedGaussT S R (qT d) (Main.gammaIdx d) ηF N (mia_clamp T t) ζ) Zc2
      (fun N t ζ ht => by simp only [mia_clamp_eq ht]) hZc2⟩⟩

example :=(@path_initial_modulus_torus_proof :
  type_of% @HRS.Whole.AppendixALemmas.path_initial_modulus_torus)

end HRS.MP.InitAsm
