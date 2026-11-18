import HRS.Main.GFB3Aux8
import HRS.Stochastic.DualityProof
import HRS.Stochastic.EmpiricalIto

/-!
# Packet GFB3, part 9: the Itô-integral representation of the pairings `⟨M_τ, x⟩` of the particle martingale
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS HRS.Uniform HRS.Uniform.Q54c

section PairIto

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {κ : Type*} [Fintype κ]

/-- For a finite index set, the coordinates `⟨M_τ, x⟩` of the Hilbert Itô integral are the real Itô integral of
`⟨Φ, x⟩` (the `approx` field at the full finite set, plus reindexing along `↥univ ≃ κ`). -/
lemma gfb3_pair_ito {W' : ℝ≥0 → Ω → κ → ℝ} (hW : IsBrownianFiltration P ℱ W') {Φ : ℝ → Ω → κ → H}
    {Mart : ℝ → Ω → H} (hMart : IsHilbertItoIntegral P ℱ W' Φ Mart) (x : H)
    (hξ' : IsProgressiveL2 P ℱ
      (fun r ω (k : (Finset.univ : Finset κ)) => inner ℝ (Φ r ω k) x))
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (fun ω => inner ℝ (Mart τ ω) x) =ᵐ[P]
      itoIntegral P ℱ W' (fun r ω k => inner ℝ (Φ r ω k) x) τ := by
  classical
  have h := hMart.approx τ hτ x
  have h1 : (atTop : Filter (Finset κ)) = pure Finset.univ :=
    atTop_eq_pure_of_isTop (x := (Finset.univ : Finset κ)) (fun s => Finset.subset_univ s)
  rw [h1] at h
  have h0 := tendsto_nhds_unique (tendsto_pure_nhds _ _) h
  set e : ↥(Finset.univ : Finset κ) → κ := fun k => (k : κ) with he
  have hinj : Function.Injective e := Subtype.val_injective
  have hW₁ : IsBrownianFiltration P ℱ (fun t ω (i : (Finset.univ : Finset κ)) => W' t ω (e i)) :=
    gfb3_isBrownianFiltration_restrict e hinj hW
  have hpad := itoIntegral_pad e hinj hW hW₁ hξ'
  have hpadfun : padFun e (fun r ω (k : (Finset.univ : Finset κ)) => inner ℝ (Φ r ω k) x) =
      fun r ω k => inner ℝ (Φ r ω k) x := by
    funext r ω k
    have := padVec_apply e hinj (fun (k : (Finset.univ : Finset κ)) => inner ℝ (Φ r ω k) x)
      ⟨k, Finset.mem_univ k⟩
    simpa [padFun, he] using this
  rw [hpadfun] at hpad
  have hmeas : AEMeasurable (fun ω => itoIntegral P ℱ
      (fun t ω (k : (Finset.univ : Finset κ)) => W' t ω k)
      (fun r ω (k : (Finset.univ : Finset κ)) => inner ℝ (Φ r ω k) x) τ ω - inner ℝ (Mart τ ω) x) P := by
    refine ((((adapted_itoIntegral P ℱ _ _ τ).mono (ℱ.le τ) le_rfl)).sub ?_).aemeasurable
    exact ((hMart.adapted τ).mono (ℱ.le τ) le_rfl).inner measurable_const
  have h2 := ae_eq_zero_of_lintegral_enorm_sq_eq_zero hmeas h0
  filter_upwards [h2, hpad] with ω hω hp
  have hp' := hp τ
  have : itoIntegral P ℱ (fun t ω (k : (Finset.univ : Finset κ)) => W' t ω k)
      (fun r ω (k : (Finset.univ : Finset κ)) => inner ℝ (Φ r ω k) x) τ ω - inner ℝ (Mart τ ω) x = 0 := hω
  rw [← hp']
  linarith

end PairIto

section Concrete

variable {d : ℕ} (S : GeneralSetup d) (N : ℕ)

/-- `η^ψ(s,ω,(i,j)) = (σ√(2β⁻¹)/N) ∂_jψ(X^i_s)`: the pairing of the noise integrand with `lpFun γ ψ`. -/
def gfb3_eta {Ω : Type*} (X : ℝ≥0 → Ω → Config d N) (ψ : Torus d → ℝ) :
    ℝ → Ω → (Fin N × Fin d) → ℝ :=
  fun s ω k => (noiseScale S N / N) * Torus.partialDeriv k.2 ψ (X (Real.toNNReal s) ω k.1)

lemma gfb3_gamma_gt (S : GeneralSetup d) : (d : ℝ) / 2 + 2 < (S.γ : ℝ) := by
  have h := S.hγ
  have : ((2 * d + 10 : ℕ) : ℝ) < (S.γ : ℝ) := by exact_mod_cast h
  push_cast at this
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

lemma gfb3_eta_pair {Ω : Type*} (X : ℝ≥0 → Ω → Config d N) {ψ : Torus d → ℝ}
    (hψ : MemSobolev (S.γ : ℝ) ψ) (hc : Continuous ψ) (h1 : Torus.IsCk 1 ψ) (s : ℝ) (ω : Ω)
    (k : Fin N × Fin d) :
    inner ℝ (noiseIntegrand (S.γ : ℝ) (noiseScale S N) (fun r => X (Real.toNNReal r)) s ω k)
      (lpFun (S.γ : ℝ) ψ) = gfb3_eta S N X ψ s ω k := by
  unfold noiseIntegrand gfb3_eta
  rw [real_inner_smul_left, inner_bVec_lpFun (gfb3_gamma_gt S) hψ hc h1]

lemma gfb3_eta_bound {Ω : Type*} (X : ℝ≥0 → Ω → Config d N) {ψ : Torus d → ℝ}
    (h2 : Torus.IsCk 2 ψ) (s : ℝ) (ω : Ω) (k : Fin N × Fin d) :
    |gfb3_eta S N X ψ s ω k| ≤ |noiseScale S N / N| * Torus.cbNorm 2 ψ := by
  unfold gfb3_eta
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (HRS.PDE.MFPair.abs_partialDeriv_le (L := 2) (by norm_num) h2 _ _) (abs_nonneg _)

lemma gfb3_eta_prog {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ mΩ}
    (X : ℝ≥0 → Ω → Config d N) (hX : IsProgressive ℱ (ofNNRealTime X)) {ψ : Torus d → ℝ}
    (h1 : Torus.IsCk 1 ψ) : IsProgressive ℱ (gfb3_eta S N X ψ) := by
  intro i
  have hg : Measurable fun x : Config d N => fun k : Fin N × Fin d =>
      (noiseScale S N / N) * Torus.partialDeriv k.2 ψ (x k.1) :=
    measurable_pi_iff.2 fun k => measurable_const.mul
      ((HRS.PDE.continuous_partialDeriv k.2 ψ h1).measurable.comp (measurable_pi_apply k.1))
  exact hg.comp (hX i)

lemma gfb3_eta_L2 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} (X : ℝ≥0 → Ω → Config d N) (hX : IsProgressive ℱ (ofNNRealTime X))
    {ψ : Torus d → ℝ} (h2 : Torus.IsCk 2 ψ) : IsProgressiveL2 P ℱ (gfb3_eta S N X ψ) :=
  IsProgressiveL2.of_bounded P (gfb3_eta_prog S N X hX (h2.of_le (by norm_num))) _
    (fun s ω k => gfb3_eta_bound S N X h2 s ω k)

end Concrete

section Restrict

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
variable {κ : Type*} [Fintype κ]

lemma gfb3_isProgressiveL2_restrict_univ {Φ : ℝ → Ω → κ → ℝ} (hΦ : IsProgressiveL2 P ℱ Φ) :
    IsProgressiveL2 P ℱ (fun r ω (k : (Finset.univ : Finset κ)) => Φ r ω k) := by
  refine ⟨?_, fun T => ?_⟩
  · exact isProgressive_pi (u := fun (k : (Finset.univ : Finset κ)) r ω => Φ r ω k)
      fun k => isProgressive_coord hΦ.prog k
  · have := hΦ.sq T
    unfold sqIntegralOn at this ⊢
    refine lt_of_eq_of_lt (lintegral_congr fun ω => lintegral_congr fun s => ?_) this
    rw [Finset.sum_coe_sort (Finset.univ : Finset κ) (fun k => ‖Φ s ω k‖ₑ ^ 2)]

open Classical in
lemma gfb3_ito_restrict {W' : ℝ≥0 → Ω → κ → ℝ} [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W') {Φ : ℝ → Ω → κ → ℝ} (hΦ : IsProgressiveL2 P ℱ Φ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    IsProgressiveL2 P ℱ (restrictFun Φ a b Set.univ) ∧
      ∀ᵐ ω ∂P, ∀ τ, itoIntegral P ℱ W' (restrictFun Φ a b Set.univ) τ ω =
        itoIntegral P ℱ W' Φ (min τ b) ω - itoIntegral P ℱ W' Φ (min τ a) ω := by
  have hΨ : (fun s ω => Set.indicator (Set.Ioc a b) (fun _ => Φ s ω) s) =
      restrictFun Φ a b Set.univ := by
    funext s ω; simp [restrictFun, Set.indicator]
  refine ⟨hΦ.restrictFun (MeasurableSet.univ : MeasurableSet[ℱ a] (Set.univ : Set Ω)), ?_⟩
  have := itoIntegral_indicator_Ioc hW hΦ ha hab
  rw [hΨ] at this
  exact this

open Classical in
lemma gfb3_ito_rsum {W' : ℝ≥0 → Ω → κ → ℝ} [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W') {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hab : ∀ i, a i ≤ b i) (Φ : Fin n → ℝ → Ω → κ → ℝ) (hΦ : ∀ i, IsProgressiveL2 P ℱ (Φ i))
    (T : Finset (Fin n)) :
    IsProgressiveL2 P ℱ (fun s ω k => ∑ i ∈ T, restrictFun (Φ i) (a i) (b i) Set.univ s ω k) ∧
      ∀ᵐ ω ∂P, ∀ τ, itoIntegral P ℱ W' (fun s ω k => ∑ i ∈ T,
          restrictFun (Φ i) (a i) (b i) Set.univ s ω k) τ ω =
        ∑ i ∈ T, (itoIntegral P ℱ W' (Φ i) (min τ (b i)) ω - itoIntegral P ℱ W' (Φ i) (min τ (a i)) ω) := by
  induction T using Finset.induction_on with
  | empty =>
    have hz : (fun s ω k => ∑ i ∈ (∅ : Finset (Fin n)), restrictFun (Φ i) (a i) (b i) Set.univ s ω k) =
        fun _ _ => (0 : κ → ℝ) := by funext s ω k; simp
    rw [hz]
    refine ⟨IsProgressiveL2.const P ℱ 0, ?_⟩
    filter_upwards [itoIntegral_const hW (0 : κ → ℝ)] with ω hω τ
    simp [hω τ]
  | insert j T hj ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨h1, h2⟩ := gfb3_ito_restrict hW (hΦ j) (ha j) (hab j)
    have hfun : (fun s ω k => ∑ i ∈ insert j T, restrictFun (Φ i) (a i) (b i) Set.univ s ω k) =
        fun s ω => restrictFun (Φ j) (a j) (b j) Set.univ s ω +
          (fun k => ∑ i ∈ T, restrictFun (Φ i) (a i) (b i) Set.univ s ω k) := by
      funext s ω k; rw [Finset.sum_insert hj]; rfl
    rw [hfun]
    refine ⟨?_, ?_⟩
    · exact h1.add ih1
    · filter_upwards [itoIntegral_add hW h1 ih1, h2, ih2] with ω hadd hj2 hT2 τ
      have hadd' := hadd τ
      rw [hadd', hj2 τ, hT2 τ, Finset.sum_insert hj]

end Restrict

end HRS.GF
