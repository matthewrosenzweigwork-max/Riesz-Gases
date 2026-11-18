import HRS.MP.KernIncr
import HRS.Main.A9Aux5
import HRS.Main.A8PAux13
import HRS.Main.GFEVAux7
import HRS.Main.A34Aux5

/-!
# Packet MPINIT (stage 1): the moment bounds of S.A.23 on the torus

The first two conjuncts of `HRS.Whole.AppendixALemmas.path_initial_modulus_torus`: the second-moment
increment bounds `E‖𝓘_{N,emp}^t - 𝓘_{N,emp}^s‖² + E‖𝓘_N^t - 𝓘_N^s‖² ≤ C|t-s|²` and its limit version.

Route.  The transport `V^{t,0} = (U^{0,t})^*` is dual to the propagator, so for `F ∈ H^{-γ}` and the
embedding `embed q F ∈ H^{-q}` (`q = γ + 2`) the increment `(V^{t,0} - V^{s,0}) F` has coefficients
`F((U^{0,t} - U^{0,s}) e_k)`; against a trigonometric polynomial `φ` it is bounded by
`‖F‖_{H^{-γ}} ‖(U^{0,t} - U^{0,s}) φ‖_{H^γ} ≤ ‖F‖ C₁ |t-s| ‖φ‖_{H^q}` (the frozen S.A.22(i), via
`HRS.MP.PropIncr.path_propagator_increment_torus_proof`), and the dual norm is controlled by the
trigonometric polynomial tests (`mpk_norm_le_of_eval`).  The second moments of `κ_NΞ_N^0` and `η°`
are the fields of `InitialFluctuationField`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MP.InitMod

open HRS HRS.PDE HRS.Main HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-! ### Stage 1: the transported field at level `q` is the embedding of the level-`γ` one -/

theorem mim_fc_embed {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (NegSobolev.embed m' F) k = NegSobolev.fourierCoeff F k :=
  HRS.GF.gfev_fourierCoeff_embed hmm' F k

theorem mim_eval_embed {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) (φ : Torus d → ℝ) :
    NegSobolev.eval (NegSobolev.embed m' F) φ = NegSobolev.eval F φ := by
  unfold NegSobolev.eval
  exact tsum_congr fun k => by rw [mim_fc_embed hmm']

theorem mim_gamma_le_q : ((gammaIdx d : ℕ) : ℝ) ≤ ((qT d : ℕ) : ℝ) := by
  have : gammaIdx d ≤ qT d := by unfold qT; omega
  exact_mod_cast this

/-- the Fourier coefficients of the level-`γ` transported field are the pairings with the propagated
modes. -/
theorem mim_fc_tf (hd : 1 ≤ d) {s : ℝ} (Rg : Regime) (MB Λ VB ν₀ T : ℝ) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (hA : AdjointData s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (F : NegSobolev d (gammaIdx d : ℝ)) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (transportField D ρ t (gammaIdx d : ℝ) F) k =
      NegSobolev.eval F (propagator D ρ 0 t (Torus.realMode k)) := by
  unfold NegSobolev.fourierCoeff
  rw [HRS.A34.a34_coord_tf hd Rg MB Λ VB ν₀ T D ρ hA ht F k, ← mul_assoc,
    ← Real.rpow_add (Torus.jp_pos k.1)]
  simp

theorem mim_tf_embed (hd : 1 ≤ d) {s : ℝ} (Rg : Regime) (MB Λ VB ν₀ T : ℝ) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (hA : AdjointData s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (F : NegSobolev d (gammaIdx d : ℝ)) :
    transportField D ρ t ((qT d : ℕ) : ℝ) (NegSobolev.embed ((qT d : ℕ) : ℝ) F) =
      NegSobolev.embed ((qT d : ℕ) : ℝ) (transportField D ρ t (gammaIdx d : ℝ) F) := by
  unfold transportField
  show NegSobolev.ofSeq _ _ = NegSobolev.ofSeq _ (NegSobolev.fourierCoeff (transportField D ρ t (gammaIdx d : ℝ) F))
  congr 1
  funext k
  rw [mim_eval_embed mim_gamma_le_q, mim_fc_tf hd Rg MB Λ VB ν₀ T D ρ hA ht F k]

theorem mim_fc_tf_q (hd : 1 ≤ d) {s : ℝ} (Rg : Regime) (MB Λ VB ν₀ T : ℝ) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (hA : AdjointData s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (F : NegSobolev d (gammaIdx d : ℝ)) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff
        (transportField D ρ t ((qT d : ℕ) : ℝ) (NegSobolev.embed ((qT d : ℕ) : ℝ) F)) k =
      NegSobolev.eval F (propagator D ρ 0 t (Torus.realMode k)) := by
  rw [mim_tf_embed hd Rg MB Λ VB ν₀ T D ρ hA ht F, mim_fc_embed mim_gamma_le_q,
    mim_fc_tf hd Rg MB Λ VB ν₀ T D ρ hA ht F k]

/-! ### Stage 2: the deterministic dual increment bound -/

theorem mim_dual_increment (hd : 1 ≤ d) (Rg : Regime) (MB Λ VB ν₀ T : ℝ) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (hA : AdjointData D.s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ) (C₁ : ℝ)
    (hC₁ : 0 ≤ C₁)
    (hbd : ∀ s' t : ℝ, 0 ≤ s' → s' ≤ t → t ≤ T → ∀ φ : Torus d → ℝ,
      HRS.MemSobolev ((qT d : ℕ) : ℝ) φ → Continuous φ →
        HRS.MemSobolev (gammaIdx d : ℝ) (fun x => propagator D ρ 0 t φ x - propagator D ρ 0 s' φ x) ∧
        HRS.sobolevNorm (gammaIdx d : ℝ) (fun x => propagator D ρ 0 t φ x - propagator D ρ 0 s' φ x) ≤
          C₁ * |t - s'| * HRS.sobolevNorm ((qT d : ℕ) : ℝ) φ)
    (F : NegSobolev d (gammaIdx d : ℝ)) {s' t : ℝ} (hs' : 0 ≤ s') (hst : s' ≤ t) (htT : t ≤ T) :
    ‖transportField D ρ t ((qT d : ℕ) : ℝ) (NegSobolev.embed ((qT d : ℕ) : ℝ) F) -
        transportField D ρ s' ((qT d : ℕ) : ℝ) (NegSobolev.embed ((qT d : ℕ) : ℝ) F)‖ ≤
      C₁ * |t - s'| * ‖F‖ := by
  have ht : t ∈ Set.Icc (0 : ℝ) T := ⟨hs'.trans hst, htT⟩
  have hs'T : s' ∈ Set.Icc (0 : ℝ) T := ⟨hs', hst.trans htT⟩
  refine HRS.MP.KernIncr.mpk_norm_le_of_eval _ _ (by positivity) ?_
  intro S b
  set φ : Torus d → ℝ := HRS.FieldSingAux.trigPoly S b with hφ
  have hφs : Torus.IsSmooth φ := HRS.FieldSingAux.isSmooth_trigPoly S b
  let Su : HRS.A33.A33Setup d := HRS.Main.A9.a9Setup hd Rg MB Λ VB ν₀ D T ρ hA
  -- the pairing with a trigonometric polynomial is the functional `ell`
  have hell : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      NegSobolev.eval (transportField D ρ τ ((qT d : ℕ) : ℝ) (NegSobolev.embed ((qT d : ℕ) : ℝ) F)) φ =
        NegSobolev.eval F (propagator D ρ 0 τ φ) := by
    intro τ hτ
    have hSu := Su.ell_trigPoly (t := τ) hτ F S b
    rw [HRS.MP.KernIncr.mpk_eval_trigPoly]
    have e1 : ∀ k ∈ S, NegSobolev.fourierCoeff
        (transportField D ρ τ ((qT d : ℕ) : ℝ) (NegSobolev.embed ((qT d : ℕ) : ℝ) F)) k * b k =
        b k * Su.ell τ F (Torus.realMode k) := by
      intro k _
      rw [mim_fc_tf_q hd Rg MB Λ VB ν₀ T D ρ hA hτ F k]
      show _ * _ = b k * NegSobolev.eval F (propagator D ρ 0 τ (Torus.realMode k))
      ring
    rw [Finset.sum_congr rfl e1]
    exact hSu.symm
  rw [HRS.MP.KernIncr.mpk_eval_sub_trig, hell t ht, hell s' hs'T]
  obtain ⟨hmem, hnorm⟩ := hbd s' t hs' hst htT φ
    (HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφs _) (HRS.A33.a33_cont hφs)
  have hlin : NegSobolev.eval F (propagator D ρ 0 t φ) - NegSobolev.eval F (propagator D ρ 0 s' φ) =
      NegSobolev.eval F (fun x => propagator D ρ 0 t φ x - propagator D ρ 0 s' φ x) := by
    obtain ⟨K, -, hK⟩ := Su.U_bound
    have h1 : NegSobolev.eval F (fun x => 1 * propagator D ρ 0 t φ x + (-1) * propagator D ρ 0 s' φ x) =
        1 * NegSobolev.eval F (propagator D ρ 0 t φ) + (-1) * NegSobolev.eval F (propagator D ρ 0 s' φ) :=
      HRS.A33.a33_eval_lin F (Su.U_cont ht hφs) (Su.U_cont hs'T hφs)
      (HRS.A33.a33_ws_of_memSobolev (hK ht hφs).1) (HRS.A33.a33_ws_of_memSobolev (hK hs'T hφs).1) 1 (-1)
    have e : (fun x => 1 * propagator D ρ 0 t φ x + (-1) * propagator D ρ 0 s' φ x) =
        fun x => propagator D ρ 0 t φ x - propagator D ρ 0 s' φ x := by
      funext x; ring
    rw [e] at h1
    rw [h1]; ring
  rw [hlin]
  refine (HRS.A33.a33_abs_eval_le F (HRS.A33.a33_ws_of_memSobolev hmem)).trans ?_
  calc ‖F‖ * HRS.sobolevNorm (gammaIdx d : ℝ) (fun x => propagator D ρ 0 t φ x - propagator D ρ 0 s' φ x)
      ≤ ‖F‖ * (C₁ * |t - s'| * HRS.sobolevNorm ((qT d : ℕ) : ℝ) φ) :=
        mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = C₁ * |t - s'| * ‖F‖ * HRS.sobolevNorm ((qT d : ℕ) : ℝ) φ := by ring

/-- the uniform form: one constant for every admissible coefficient pair with `D.invβ ≤ νbar`. -/
theorem mim_det_uniform (s : ℝ) (Rg : Regime) (ν₀ MB Λ T VB νbar : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (hd : 1 ≤ d) (D : DynData d) (ρ : ℝ → Torus d → ℝ),
      AdjointData s (gammaIdx d + 2) Rg MB Λ VB D ν₀ T ρ → D.invβ ≤ νbar →
      ∀ (F : NegSobolev d (gammaIdx d : ℝ)) {s' t : ℝ}, s' ∈ Set.Icc (0 : ℝ) T →
        t ∈ Set.Icc (0 : ℝ) T →
        ‖transportField D ρ t ((qT d : ℕ) : ℝ) (NegSobolev.embed ((qT d : ℕ) : ℝ) F) -
            transportField D ρ s' ((qT d : ℕ) : ℝ) (NegSobolev.embed ((qT d : ℕ) : ℝ) F)‖ ≤
          K * |t - s'| * ‖F‖ := by
  obtain ⟨C, hC⟩ := HRS.MP.PropIncr.path_propagator_increment_torus_proof (d := d) s Rg ν₀ MB Λ T VB
    νbar
  have e2 : qT d - 2 = gammaIdx d := by unfold qT; omega
  refine ⟨max C 0, le_max_right _ _, fun hd D ρ hA hν F s' t hs' ht => ?_⟩
  have hAγ : AdjointData D.s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ := by
    have h1 := HRS.PDE.StabAux.adjointData_mono (m' := gammaIdx d) (by omega) hA
    have e : D.s = s := hA.hs
    rw [e]; exact h1
  have hbd : ∀ s' t : ℝ, 0 ≤ s' → s' ≤ t → t ≤ T → ∀ φ : Torus d → ℝ,
      HRS.MemSobolev ((qT d : ℕ) : ℝ) φ → Continuous φ →
        HRS.MemSobolev (gammaIdx d : ℝ) (fun x => propagator D ρ 0 t φ x - propagator D ρ 0 s' φ x) ∧
        HRS.sobolevNorm (gammaIdx d : ℝ) (fun x => propagator D ρ 0 t φ x - propagator D ρ 0 s' φ x) ≤
          max C 0 * |t - s'| * HRS.sobolevNorm ((qT d : ℕ) : ℝ) φ := by
    intro s' t hs' hst htT φ hφS hφc
    have h := hC (ι := Unit) (fun _ => D) (fun _ => ρ) (fun _ => hA) (fun _ => hν) () 0 s' t le_rfl
      hs' hst htT φ hφS hφc
    rw [e2] at h
    refine ⟨h.1, h.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
      (Real.sqrt_nonneg _)
  rcases le_total s' t with hst | hts
  · exact mim_dual_increment hd Rg MB Λ VB ν₀ T D ρ hAγ (max C 0) (le_max_right _ _) hbd F hs'.1 hst
      ht.2
  · have := mim_dual_increment hd Rg MB Λ VB ν₀ T D ρ hAγ (max C 0) (le_max_right _ _) hbd F ht.1 hts
      hs'.2
    rwa [norm_sub_rev, abs_sub_comm] at this

/-! ### Stage 3: second moments -/

theorem mim_ofReal_norm_sq {E : Type*} [NormedAddCommGroup E] (x : E) :
    ENNReal.ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

/-- pointwise bound of the scaled increment by the (squared) size of the initial field. -/
theorem mim_pointwise {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    {K Δt A : ℝ} (hK : 0 ≤ K) (hΔ : 0 ≤ Δt) (hA : |A| ≤ 1) (X Y : E) (F : E')
    (h : ‖X - Y‖ ≤ K * Δt * ‖F‖) :
    ‖A • X - A • Y‖ₑ ^ 2 ≤ ENNReal.ofReal (K ^ 2 * Δt ^ 2) * ‖F‖ₑ ^ 2 := by
  have h1 : ‖A • X - A • Y‖ ≤ K * Δt * ‖F‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    calc |A| * ‖X - Y‖ ≤ 1 * ‖X - Y‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      _ ≤ K * Δt * ‖F‖ := by rw [one_mul]; exact h
  rw [← mim_ofReal_norm_sq, ← mim_ofReal_norm_sq, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖A • X - A • Y‖ ^ 2 ≤ (K * Δt * ‖F‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = K ^ 2 * Δt ^ 2 * ‖F‖ ^ 2 := by ring

theorem mim_embed_smul_ofMeasureDiff {m m' : ℝ} (hmm : m ≤ m') (hm : (d : ℝ) < 2 * m)
    (hm' : (d : ℝ) < 2 * m') (σ : ℝ) (μ ν : Measure (Torus d)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    NegSobolev.embed m' (σ • NegSobolev.ofMeasureDiff m μ ν) =
      σ • NegSobolev.ofMeasureDiff m' μ ν := by
  refine HRS.GF.gfev_ext fun k => ?_
  rw [HRS.GF.gfev_coord_embed hmm, HRS.GF.gfev_fc_smul, HRS.GF.gfev_coord_smul,
    HRS.InitialDataAux.coord_ofMeasureDiff hm' μ ν k, NegSobolev.fourierCoeff_ofMeasureDiff hm μ ν k]
  ring

theorem mim_gamma_bounds : (d : ℝ) < 2 * ((gammaIdx d : ℕ) : ℝ) ∧ (d : ℝ) < 2 * ((qT d : ℕ) : ℝ) := by
  have h : gammaIdx d = mStar d + d + 3 := rfl
  have hq : qT d = gammaIdx d + 2 := rfl
  have h0 : (0 : ℝ) ≤ (mStar d : ℝ) := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have e : ((gammaIdx d : ℕ) : ℝ) = (mStar d : ℝ) + d + 3 := by rw [h]; push_cast; ring
  have e' : ((qT d : ℕ) : ℝ) = (mStar d : ℝ) + d + 5 := by rw [hq, h]; push_cast; ring
  rw [e, e']
  constructor <;> linarith

theorem path_initial_modulus_torus_moments (s : ℝ) (Rg : PDE.Regime)
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
            ENNReal.ofReal (C * |t - s'| ^ 2)) := by
  obtain ⟨K, hK0, hK⟩ := mim_det_uniform (d := d) s Rg ν₀ MB Λ T VB νbar
  refine ⟨K ^ 2 * Cin ^ 2, ?_⟩
  intro S hs hT hν R 𝔈 hS m₀ ε Ψ hinit εf ηF νin hfield
  have hd : 1 ≤ d := S.hd
  have hq : PDE.mStar d ≤ gammaIdx d + 2 := by unfold gammaIdx; omega
  obtain ⟨hg2, hq2⟩ := mim_gamma_bounds (d := d)
  haveI := S.hμ0
  refine ⟨?_, ?_⟩
  · intro N hN s' hs' t ht
    have hA : AdjointData s (gammaIdx d + 2) Rg MB Λ VB (S.dyn N) ν₀ T (S.ρ N) := by
      have h := HRS.Main.A9.a9_adjointData hq hS hN
      rw [hs, hT] at h; exact h
    have hdet := hK hd (S.dyn N) (S.ρ N) hA (hν N)
    have hAN := HRS.Main.A8P.a8p_A_abs_le S N
    have hΔ : 0 ≤ |t - s'| := abs_nonneg _
    have hsec := hfield.second_moment N hN
    have hKΔ : ∀ F : NegSobolev d (gammaIdx d : ℝ),
        ‖S.AN N • transportField (S.dyn N) (S.ρ N) t ((qT d : ℕ) : ℝ) (NegSobolev.embed ((qT d : ℕ) : ℝ) F) -
          S.AN N • transportField (S.dyn N) (S.ρ N) s' ((qT d : ℕ) : ℝ)
            (NegSobolev.embed ((qT d : ℕ) : ℝ) F)‖ₑ ^ 2 ≤
          ENNReal.ofReal (K ^ 2 * |t - s'| ^ 2) * ‖F‖ₑ ^ 2 := fun F =>
      mim_pointwise hK0 hΔ hAN _ _ F (hdet F hs' ht)
    have hemp : ∫⁻ ζ, ‖transportedEmpT S R (qT d) N t ζ - transportedEmpT S R (qT d) N s' ζ‖ₑ ^ 2 ∂(R N).P ≤
        ENNReal.ofReal (K ^ 2 * |t - s'| ^ 2) *
          ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ω)) S.μ0‖ₑ ^ 2
            ∂(R N).P := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun ζ => ?_
      have e := mim_embed_smul_ofMeasureDiff (d := d) mim_gamma_le_q (m := (gammaIdx d : ℝ)) hg2 hq2 (S.κ N)
        (empirical ((R N).X₀ ζ)) S.μ0
      have := hKΔ (S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ζ)) S.μ0)
      rw [e] at this
      exact this
    have hgau : ∫⁻ ζ, ‖transportedGaussT S R (qT d) (gammaIdx d) ηF N t ζ -
        transportedGaussT S R (qT d) (gammaIdx d) ηF N s' ζ‖ₑ ^ 2 ∂(R N).P ≤
        ENNReal.ofReal (K ^ 2 * |t - s'| ^ 2) * ∫⁻ ω, ‖ηF N ω‖ₑ ^ 2 ∂(R N).P := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_mono fun ζ => hKΔ (ηF N ζ)
    calc _ ≤ ENNReal.ofReal (K ^ 2 * |t - s'| ^ 2) *
          ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ω)) S.μ0‖ₑ ^ 2
            ∂(R N).P +
          ENNReal.ofReal (K ^ 2 * |t - s'| ^ 2) * ∫⁻ ω, ‖ηF N ω‖ₑ ^ 2 ∂(R N).P := add_le_add hemp hgau
      _ = ENNReal.ofReal (K ^ 2 * |t - s'| ^ 2) *
          (∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ω)) S.μ0‖ₑ ^ 2
            ∂(R N).P + ∫⁻ ω, ‖ηF N ω‖ₑ ^ 2 ∂(R N).P) := (mul_add _ _ _).symm
      _ ≤ ENNReal.ofReal (K ^ 2 * |t - s'| ^ 2) * ENNReal.ofReal (Cin ^ 2) :=
          mul_le_mul' le_rfl hsec
      _ = ENNReal.ofReal (K ^ 2 * Cin ^ 2 * |t - s'| ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  · intro L hL s' hs' t ht
    have hfacts := fun N (hN : 1 ≤ N) => HRS.A34.a34_delta_facts S L (gammaIdx d) N Rg ν₀ MB Λ VB
      (hL.seq_adjoint N hN) hL.limit_adjoint
    have hΔt := hL.tendsto
    -- `S.invβ N → L.invβ` and `S.AN N → L.A`
    have hlim : ∀ (f : ℕ → ℝ) (a : ℝ), (∀ N, 1 ≤ N → |f N - a| ≤ S.coeffDiscrepancy L (gammaIdx d) N) →
        Tendsto f atTop (𝓝 a) := by
      intro f a hf
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun N => dist_nonneg) ?_ hΔt
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [Real.dist_eq]; exact hf N hN
    have hβ : L.invβ ≤ νbar := by
      have := hlim (fun N => S.invβ N) L.invβ fun N hN => (hfacts N hN).2.2.1
      exact le_of_tendsto this (Eventually.of_forall fun N => hν N)
    have hAL : |L.A| ≤ 1 := by
      have := hlim (fun N => S.AN N) L.A fun N hN => (hfacts N hN).2.2.2.2
      have h2 : Tendsto (fun N => |S.AN N|) atTop (𝓝 |L.A|) := this.abs
      exact le_of_tendsto h2 (Eventually.of_forall fun N => HRS.Main.A8P.a8p_A_abs_le S N)
    have hA : AdjointData s (gammaIdx d + 2) Rg MB Λ VB (L.dyn S) ν₀ T L.ρ := by
      have h := hL.limit_adjoint
      rw [hs, hT] at h; exact h
    have hdet := hK hd (L.dyn S) L.ρ hA hβ
    have hΔ : 0 ≤ |t - s'| := abs_nonneg _
    have hpt : ∀ F : NegSobolev d (gammaIdx d : ℝ),
        ‖L.A • transportField (L.dyn S) L.ρ t ((qT d : ℕ) : ℝ) (NegSobolev.embed ((qT d : ℕ) : ℝ) F) -
          L.A • transportField (L.dyn S) L.ρ s' ((qT d : ℕ) : ℝ)
            (NegSobolev.embed ((qT d : ℕ) : ℝ) F)‖ₑ ^ 2 ≤
          ENNReal.ofReal (K ^ 2 * |t - s'| ^ 2) * ‖F‖ₑ ^ 2 := fun F =>
      mim_pointwise hK0 hΔ hAL _ _ F (hdet F hs' ht)
    have hsec := (hfield.second_moment 1 le_rfl)
    have hlaw : ∫⁻ F, ‖F‖ₑ ^ 2 ∂νin = ∫⁻ ω, ‖ηF 1 ω‖ₑ ^ 2 ∂(R 1).P := by
      rw [← hfield.law_eq 1 le_rfl]
      unfold law
      exact lintegral_map (by fun_prop) (hfield.ηF_meas 1)
    calc _ ≤ ∫⁻ F, ENNReal.ofReal (K ^ 2 * |t - s'| ^ 2) * ‖F‖ₑ ^ 2 ∂νin := lintegral_mono hpt
      _ = ENNReal.ofReal (K ^ 2 * |t - s'| ^ 2) * ∫⁻ F, ‖F‖ₑ ^ 2 ∂νin :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (K ^ 2 * |t - s'| ^ 2) * ENNReal.ofReal (Cin ^ 2) := by
          rw [hlaw]
          exact mul_le_mul' le_rfl (le_trans le_add_self hsec)
      _ = ENNReal.ofReal (K ^ 2 * Cin ^ 2 * |t - s'| ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring

end HRS.MP.InitMod
