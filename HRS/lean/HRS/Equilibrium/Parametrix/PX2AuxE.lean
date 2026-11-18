import HRS.Equilibrium.Parametrix.PX2AuxD
import HRS.Equilibrium.LocalDivSub

/-!
# Packet PX2b auxiliaries: congruence off the diagonal, smooth kernels, the source kernel

* `conormalL_congr_offDiag`: the class only depends on the kernel off the diagonal,
* `conormal_zero`, `conormal_of_smooth_kernel` (a `C^∞` kernel with bounded derivatives is in every class),
* the decomposition of `hTransport` and of `Hsource`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

universe u

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem conormalL_congr_offDiag {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ}
    {F F' : Torus d → Torus d → ℝ} (h : ∀ x y, x ≠ y → F x y = F' x y)
    (hF : ConormalL σ b m B F) : ConormalL σ b m B F' where
  smooth := by
    refine hF.smooth.congr fun p hp => ?_
    have : Torus.mk p.1 ≠ Torus.mk p.2 := hp
    exact (h _ _ this).symm
  near := by
    intro a c hac X z hz hzr
    have hzb : ∀ i, |z i| ≤ 1 / 2 := fun i => by
      have := PiLp.norm_apply_le z i
      rw [Real.norm_eq_abs] at this
      unfold r0 at hzr; linarith
    have hU : {z' : Euc d | Torus.mk z' ≠ 0} ∈ 𝓝 z :=
      isOpen_mk_ne_zero'.mem_nhds (box_ne_zero hz hzb)
    have hcongr : mixedDeriv a c (toChart F') X z = mixedDeriv a c (toChart F) X z := by
      refine mixedDeriv_congr a c X z hU fun X' z' hz' => ?_
      simp only [toChart]
      symm
      refine h _ _ ?_
      intro hEq
      apply hz'
      have : Torus.mk (X' + (1 / 2 : ℝ) • z') - Torus.mk (X' - (1 / 2 : ℝ) • z') = 0 := by
        rw [hEq, sub_self]
      rw [← mk_sub_eq] at this
      have e : X' + (1 / 2 : ℝ) • z' - (X' - (1 / 2 : ℝ) • z') = z' := by module
      rwa [e] at this
    rw [hcongr]
    exact hF.near a c hac X z hz hzr
  far := by
    intro k hk p hp hdist
    have hopen : IsOpen (offDiag d) := px2_isOpen_offDiag
    have hev : lift2 F' =ᶠ[𝓝 p] lift2 F := by
      filter_upwards [hopen.mem_nhds hp] with q hq
      have : Torus.mk q.1 ≠ Torus.mk q.2 := hq
      exact (h _ _ this).symm
    rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
    exact hF.far k hk p hp hdist

theorem conormal_zero (σ : ℝ) (b : ℕ → ℕ) (m : ℕ) :
    ConormalL σ b m 0 (fun (_ _ : Torus d) => (0 : ℝ)) where
  smooth := by
    have : lift2 (fun (_ _ : Torus d) => (0 : ℝ)) = fun _ => (0 : ℝ) := rfl
    rw [this]; exact contDiffOn_const
  near := by
    intro a c hac X z hz hzr
    have h0 : toChart (fun (_ _ : Torus d) => (0 : ℝ)) = fun _ => (0 : ℝ) := rfl
    rw [h0]
    have : mixedDeriv a c (fun _ : Euc d × Euc d => (0 : ℝ)) X z = 0 := by
      unfold mixedDeriv
      simp [iteratedFDeriv_zero_fun]
    rw [this, zero_mul]
    exact (norm_zero (E := ContinuousMultilinearMap ℝ (fun _ : Fin a => Euc d)
      (ContinuousMultilinearMap ℝ (fun _ : Fin c => Euc d) ℝ))).le
  far := by
    intro k hk p hp hdist
    have : iteratedFDeriv ℝ k (lift2 (fun (_ _ : Torus d) => (0 : ℝ))) p = 0 := by
      have h0 : lift2 (fun (_ _ : Torus d) => (0 : ℝ)) = fun _ => (0 : ℝ) := rfl
      rw [h0]; simp [iteratedFDeriv_zero_fun]
    rw [this]; simp

/-- The chart map `(X, z) ↦ (X + z/2, X - z/2)` as a continuous linear map. -/
def chartCLM (d : ℕ) : Euc d × Euc d →L[ℝ] Euc d × Euc d :=
  (ContinuousLinearMap.fst ℝ (Euc d) (Euc d) + (1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ (Euc d) (Euc d)).prod
    (ContinuousLinearMap.fst ℝ (Euc d) (Euc d) - (1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ (Euc d) (Euc d))

theorem chartCLM_apply (p : Euc d × Euc d) :
    chartCLM d p = (p.1 + (1 / 2 : ℝ) • p.2, p.1 - (1 / 2 : ℝ) • p.2) := rfl

theorem norm_chartCLM_le : ‖chartCLM d‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun p => ?_
  rw [chartCLM_apply, Prod.norm_def]
  have h1 : ‖p.1‖ ≤ ‖p‖ := by simpa using norm_fst_le p
  have h2 : ‖p.2‖ ≤ ‖p‖ := by simpa using norm_snd_le p
  have h3 : ‖p.1 + (1 / 2 : ℝ) • p.2‖ ≤ 2 * ‖p‖ := by
    calc _ ≤ ‖p.1‖ + ‖(1 / 2 : ℝ) • p.2‖ := norm_add_le _ _
      _ ≤ ‖p‖ + (1 / 2) * ‖p‖ := by
          rw [norm_smul]; norm_num; linarith
      _ ≤ 2 * ‖p‖ := by nlinarith [norm_nonneg p]
  have h4 : ‖p.1 - (1 / 2 : ℝ) • p.2‖ ≤ 2 * ‖p‖ := by
    calc _ ≤ ‖p.1‖ + ‖(1 / 2 : ℝ) • p.2‖ := norm_sub_le _ _
      _ ≤ ‖p‖ + (1 / 2) * ‖p‖ := by
          rw [norm_smul]; norm_num; linarith
      _ ≤ 2 * ‖p‖ := by nlinarith [norm_nonneg p]
  exact max_le h3 h4

theorem conormal_of_smooth_kernel (σ : ℝ) (b : ℕ → ℕ) (m : ℕ) {a : Torus d → Torus d → ℝ}
    (ha : ContDiff ℝ ∞' (lift2 a)) (N : ℕ → ℝ)
    (hN : ∀ (k : ℕ) (p : Euc d × Euc d), ‖iteratedFDeriv ℝ k (lift2 a) p‖ ≤ N k) :
    ConormalL σ b m (∑ k ∈ Finset.range (m + 1), 2 ^ k * N k) a := by
  have hN0 : ∀ k, 0 ≤ N k := fun k => (norm_nonneg _).trans (hN k 0)
  set B : ℝ := ∑ k ∈ Finset.range (m + 1), 2 ^ k * N k with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (hN0 k)
  have hle : ∀ k, k ≤ m → 2 ^ k * N k ≤ B := fun k hk =>
    Finset.single_le_sum (f := fun k => (2 : ℝ) ^ k * N k) (fun j _ => mul_nonneg (by positivity) (hN0 j))
      (Finset.mem_range.mpr (by omega))
  have hchart : toChart a = lift2 a ∘ chartCLM d := by
    funext p; rfl
  have hcd : ContDiff ℝ ∞' (toChart a) := by
    rw [hchart]; exact ha.comp (chartCLM d).contDiff
  refine ⟨ha.contDiffOn.of_le (natCast_le_infty m), ?_, ?_⟩
  · intro a' c hac X z hz hzr
    have h1 := norm_mixedDeriv_le c hcd a' X z
    refine h1.trans ?_
    rw [hchart, ContinuousLinearMap.iteratedFDeriv_comp_right _ ha (X, z) (natCast_le_infty _)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h2 : ∏ _j : Fin (a' + c), ‖chartCLM d‖ ≤ 2 ^ (a' + c) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact pow_le_pow_left₀ (norm_nonneg _) norm_chartCLM_le _
    have h3 : ‖iteratedFDeriv ℝ (a' + c) (lift2 a) (chartCLM d (X, z))‖ * ∏ _j : Fin (a' + c), ‖chartCLM d‖ ≤
        N (a' + c) * 2 ^ (a' + c) :=
      mul_le_mul (hN _ _) h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (hN0 _)
    refine h3.trans ?_
    have h4 : N (a' + c) * 2 ^ (a' + c) ≤ B := by
      have := hle (a' + c) hac; linarith
    have hw : 0 ≤ ‖z‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖z‖|) ^ b c :=
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
    nlinarith
  · intro k hk p hp hdist
    refine (hN k p).trans ?_
    have := hle k hk
    have h2 : N k ≤ 2 ^ k * N k := by
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith [hN0 k]
    linarith

/-- Closure of the classes under sums (the packet statement `ConormalL.add`). -/
def ConormalAdd (d : ℕ) : Prop :=
  ∀ (σ : ℝ) (b : ℕ → ℕ) (m : ℕ) (B B' : ℝ) (F G : Torus d → Torus d → ℝ),
    ConormalL σ b m B F → ConormalL σ b m B' G → ConormalL σ b m (B + B') (fun x y => F x y + G x y)

/-- Closure of the classes under real multiples (the packet statement `ConormalL.smul`). -/
def ConormalSmul (d : ℕ) : Prop :=
  ∀ (σ : ℝ) (b : ℕ → ℕ) (m : ℕ) (B : ℝ) (F : Torus d → Torus d → ℝ),
    ConormalL σ b m B F → ∀ a : ℝ, ConormalL σ b m (|a| * B) (fun x y => a * F x y)

theorem conormalL_mono_B {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B B' : ℝ} {F : Torus d → Torus d → ℝ}
    (h : ConormalL σ b m B F) (hB0 : 0 ≤ B) (hB : B ≤ B') : ConormalL σ b m B' F where
  smooth := h.smooth
  near := by
    intro a c hac X z hz hzr
    refine (h.near a c hac X z hz hzr).trans ?_
    have hw : 0 ≤ 1 + ‖z‖ ^ (-(σ + c)) * (1 + |Real.log ‖z‖|) ^ b c := by positivity
    exact mul_le_mul_of_nonneg_right hB hw
  far := fun k hk p hp hr => (h.far k hk p hp hr).trans hB

theorem conormal_finset_sum (hAdd : ConormalAdd d) {ι : Type*} [DecidableEq ι] (σ : ℝ) (b : ℕ → ℕ)
    (m : ℕ) (s : Finset ι) (F : ι → Torus d → Torus d → ℝ) (B : ι → ℝ)
    (hF : ∀ j ∈ s, ConormalL σ b m (B j) (F j)) :
    ConormalL σ b m (∑ j ∈ s, B j) (fun x y => ∑ j ∈ s, F j x y) := by
  induction s using Finset.induction_on with
  | empty => simpa using conormal_zero (d := d) σ b m
  | insert j s hj ih =>
    have h1 := hAdd σ b m (B j) (∑ k ∈ s, B k) (F j) (fun x y => ∑ k ∈ s, F k x y)
      (hF j (Finset.mem_insert_self j s)) (ih fun k hk => hF k (Finset.mem_insert_of_mem hk))
    rw [Finset.sum_insert hj]
    convert h1 using 2
    funext y
    rw [Finset.sum_insert hj]

theorem hTransport_eq_kernel {s : ℝ} {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    hTransport d s f = fun x y => ∑ j, (Torus.partialDeriv j f x - Torus.partialDeriv j f y) *
      (periodicRieszGrad d s (x - y)) j := by
  funext x y
  exact LocalDivAux.hTransport_eq s f hf x y

theorem le_posSeminorm {f : Torus d → ℝ} (hf : Torus.IsSmooth f) {K j : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ K)
    (y : Euc d) : ‖iteratedFDeriv ℝ j (Torus.lift f) y‖ ≤ posSeminorm K f := by
  have hF : ContDiff ℝ ∞' (Torus.lift f) := hf
  have hbdd : ∀ i : ℕ, BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ i (Torus.lift f) x‖) := by
    intro i
    obtain ⟨M, _, hM⟩ := bdd_iteratedFDeriv_lift f i (hF.of_le (natCast_le_infty i))
    exact ⟨M, by rintro _ ⟨x, rfl⟩; exact hM x⟩
  unfold posSeminorm
  have hnn : ∀ i ∈ Finset.Icc 1 K, 0 ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift f) x‖ :=
    fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _
  calc ‖iteratedFDeriv ℝ j (Torus.lift f) y‖ ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift f) x‖ :=
        le_ciSup (hbdd j) y
    _ ≤ ∑ i ∈ Finset.Icc 1 K, ⨆ x : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift f) x‖ :=
        Finset.single_le_sum (f := fun i => ⨆ x : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift f) x‖) hnn
          (Finset.mem_Icc.mpr ⟨hj1, hjK⟩)

theorem posSeminorm_nonneg (K : ℕ) (f : Torus d → ℝ) : 0 ≤ posSeminorm K f :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem nbound_partialDeriv {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (j : Fin d) (m : ℕ) :
    ∀ k : ℕ, k ≤ m + 1 → ∀ y : Euc d,
      ‖iteratedFDeriv ℝ k (Torus.lift (Torus.partialDeriv j f)) y‖ ≤ posSeminorm (m + 2) f := by
  intro k hk y
  exact (norm_lift_partialDeriv_le hf j k y).trans (le_posSeminorm hf (by omega) (by omega) y)

theorem conormal_component {σ : ℝ} {m : ℕ} {γ : Torus d → ℝ} (hγ : KerBound (σ + 1) m γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Torus d → ℝ), Torus.IsSmooth f → ∀ j : Fin d,
      Conormal σ 0 m (C * posSeminorm (m + 2) f)
        (fun x y => (Torus.partialDeriv j f x - Torus.partialDeriv j f y) * γ (x - y)) := by
  obtain ⟨C, hC0, hC⟩ := conormal_diffProd hγ
  refine ⟨C, hC0, fun f hf j => hC _ (LocalDivAux.isSmooth_partialDeriv hf j) _ (nbound_partialDeriv hf j m)⟩

/-- `hTransport` is conormal of order `s` with `m` derivatives, with constant proportional to
`posSeminorm (m+2) f`, for every `m`. -/
def HTransportConormal (d : ℕ) (s : ℝ) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
    Conormal s 0 m (C * posSeminorm (m + 2) f) (hTransport d s f)

theorem hTransport_conormal (hAdd : ConormalAdd d) (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) :
    HTransportConormal d s := by
  intro m
  have hj : ∀ j : Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Torus d → ℝ), Torus.IsSmooth f → ∀ j' : Fin d,
      Conormal s 0 m (C * posSeminorm (m + 2) f)
        (fun x y => (Torus.partialDeriv j' f x - Torus.partialDeriv j' f y) *
          (fun z => periodicRieszGrad d s z j) (x - y)) :=
    fun j => conormal_component (kerBound_periodicRieszGrad hd hs0 hsd m j)
  choose C hC0 hC using hj
  refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ => hC0 j, fun f hf => ?_⟩
  have h1 := conormal_finset_sum hAdd s (fun _ => 0) m Finset.univ
    (fun j x y => (Torus.partialDeriv j f x - Torus.partialDeriv j f y) * periodicRieszGrad d s (x - y) j)
    (fun j => C j * posSeminorm (m + 2) f) (fun j _ => hC j f hf j)
  rw [hTransport_eq_kernel hf, ← Finset.sum_mul] at *
  exact h1

theorem row_data (hd : 2 ≤ d) {s : ℝ} (hsd : s < d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    (hC : HTransportConormal d s) (m : ℕ) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Torus.IsSmooth (fun x => ∫ y, hTransport d s f x y ∂(withDensityReal ρ)) ∧
      Torus.cbNorm m (fun x => ∫ y, hTransport d s f x y ∂(withDensityReal ρ)) ≤
        Cr * posSeminorm (m + 2) f := by
  obtain ⟨C, hC0, hCm⟩ := hC m
  obtain ⟨Cr, hCr0, hCr⟩ := conormal_row_smooth_aux hd hρ hsd 0 m
  refine ⟨Cr * C, mul_nonneg hCr0 hC0, fun f hf => ⟨?_, ?_⟩⟩
  · unfold Torus.IsSmooth Torus.IsCk
    rw [contDiff_infty]
    intro n
    obtain ⟨C', hC'0, hC'⟩ := hC n
    obtain ⟨Cr', hCr'0, hCr'⟩ := conormal_row_smooth_aux hd hρ hsd 0 n
    exact (hCr' _ _ (mul_nonneg hC'0 (posSeminorm_nonneg _ _)) (hC' f hf)).1
  · have := (hCr _ _ (mul_nonneg hC0 (posSeminorm_nonneg _ _)) (hCm f hf)).2
    calc _ ≤ Cr * (C * posSeminorm (m + 2) f) := this
      _ = _ := by ring

theorem norm_iteratedFDeriv_const_le (c : ℝ) (k : ℕ) (p : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ k (fun _ : Euc d × Euc d => c) p‖ ≤ |c| := by
  rcases k with _ | k
  · simp [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne (by omega)]
    have : ‖(0 : Euc d × Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => Euc d × Euc d) ℝ) p‖ = 0 :=
      norm_zero (E := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => Euc d × Euc d) ℝ)
    rw [this]; exact abs_nonneg _

theorem norm_iteratedFDeriv_sigma_le {Φ : Euc d → ℝ} (hΦ : ContDiff ℝ ∞' Φ) (c : ℝ) (k : ℕ)
    (p : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ k (fun q : Euc d × Euc d => -Φ q.1 - Φ q.2 + c) p‖ ≤
      ‖iteratedFDeriv ℝ k Φ p.1‖ + ‖iteratedFDeriv ℝ k Φ p.2‖ + |c| := by
  have hneg : ContDiff ℝ ∞' (fun y => -Φ y) := hΦ.neg
  have h1 : ContDiff ℝ ∞' (fun q : Euc d × Euc d => -Φ q.1 - Φ q.2) :=
    (hneg.comp contDiff_fst).sub (hΦ.comp contDiff_snd)
  have e : (fun q : Euc d × Euc d => -Φ q.1 - Φ q.2 + c) =
      (fun q : Euc d × Euc d => -Φ q.1 - Φ q.2) + (fun _ : Euc d × Euc d => c) := rfl
  rw [e, iteratedFDeriv_add_apply (h1.contDiffAt.of_le (natCast_le_infty k))
    (contDiffAt_const.of_le (natCast_le_infty k))]
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_iteratedFDeriv_const_le c k p))
  have := norm_iteratedFDeriv_sub_prod_le' hneg hΦ k p
  have e2 : iteratedFDeriv ℝ k (fun y => -Φ y) p.1 = -iteratedFDeriv ℝ k Φ p.1 :=
    iteratedFDeriv_neg_apply
  simpa [e2] using this

theorem conormal_sigma (σ : ℝ) (b : ℕ → ℕ) (m : ℕ) :
    ∃ Csig : ℝ, 0 ≤ Csig ∧ ∀ (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (r : Torus d → ℝ),
      Torus.IsSmooth r →
      ConormalL σ b m (Csig * Torus.cbNorm m r)
        (fun x y => -r x - r y + ∫ x', r x' ∂μ) := by
  refine ⟨2 ^ m * (3 * (m + 1)), by positivity, fun μ _ r hr => ?_⟩
  have hΦ : ContDiff ℝ ∞' (Torus.lift r) := hr
  set c : ℝ := ∫ x', r x' ∂μ with hc
  have hbdd : ∀ i : ℕ, BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ i (Torus.lift r) x‖) := by
    intro i
    obtain ⟨M, _, hM⟩ := bdd_iteratedFDeriv_lift r i (hΦ.of_le (natCast_le_infty i))
    exact ⟨M, by rintro _ ⟨x, rfl⟩; exact hM x⟩
  set R : ℕ → ℝ := fun k => ⨆ y : Euc d, ‖iteratedFDeriv ℝ k (Torus.lift r) y‖ with hR
  have hR0 : ∀ k, 0 ≤ R k := fun k => Real.iSup_nonneg fun _ => norm_nonneg _
  have hRle : ∀ k y, ‖iteratedFDeriv ℝ k (Torus.lift r) y‖ ≤ R k := fun k y => le_ciSup (hbdd k) y
  have hcb : Torus.cbNorm m r = ∑ k ∈ Finset.range (m + 1), R k := rfl
  have hRcb : ∀ k, k ≤ m → R k ≤ Torus.cbNorm m r := fun k hk => by
    rw [hcb]
    exact Finset.single_le_sum (f := R) (fun j _ => hR0 j) (Finset.mem_range.mpr (by omega))
  have hcle : |c| ≤ R 0 := by
    have : ∀ x : Torus d, ‖r x‖ ≤ R 0 := by
      intro x
      have := hRle 0 (Torus.rep x)
      rw [norm_iteratedFDeriv_zero] at this
      simpa [Torus.lift, Torus.mk_rep] using this
    have h2 := norm_integral_le_of_norm_le_const (μ := μ) (f := r) (C := R 0)
      (Filter.Eventually.of_forall this)
    rw [hc, ← Real.norm_eq_abs]
    simpa using h2
  have hcb0 : 0 ≤ Torus.cbNorm m r := by rw [hcb]; exact Finset.sum_nonneg fun k _ => hR0 k
  have hsm : ContDiff ℝ ∞' (lift2 (fun x y : Torus d => -r x - r y + c)) := by
    have : lift2 (fun x y : Torus d => -r x - r y + c) =
        fun q : Euc d × Euc d => -Torus.lift r q.1 - Torus.lift r q.2 + c := rfl
    rw [this]
    exact (((hΦ.comp contDiff_fst).neg).sub (hΦ.comp contDiff_snd)).add contDiff_const
  have hk := conormal_of_smooth_kernel σ b m (a := fun x y : Torus d => -r x - r y + c) hsm
    (fun k => 2 * R k + |c|) (fun k p => by
      have := norm_iteratedFDeriv_sigma_le hΦ c k p
      have h1 := hRle k p.1
      have h2 := hRle k p.2
      show ‖iteratedFDeriv ℝ k (fun q : Euc d × Euc d => -Torus.lift r q.1 - Torus.lift r q.2 + c) p‖ ≤ _
      linarith)
  refine conormalL_mono_B hk (Finset.sum_nonneg fun k _ => mul_nonneg (by positivity)
    (by have := hR0 k; have := abs_nonneg c; linarith)) ?_
  calc ∑ k ∈ Finset.range (m + 1), (2 : ℝ) ^ k * (2 * R k + |c|)
      ≤ ∑ k ∈ Finset.range (m + 1), (2 : ℝ) ^ m * (2 * Torus.cbNorm m r + Torus.cbNorm m r) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k ≤ m := by have := Finset.mem_range.mp hk; omega
        have h2k : (2 : ℝ) ^ k ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hk'
        have : 2 * R k + |c| ≤ 2 * Torus.cbNorm m r + Torus.cbNorm m r := by
          have := hRcb k hk'; have := hRcb 0 (Nat.zero_le _); linarith
        exact mul_le_mul h2k this (by have := hR0 k; have := abs_nonneg c; linarith) (by positivity)
    _ = 2 ^ m * (3 * (m + 1)) * Torus.cbNorm m r := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-! ### The source `H_f` -/

theorem continuous_of_isSmooth {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : Continuous φ := by
  have hF : ContDiff ℝ ∞' (Torus.lift φ) := hφ
  exact KernelGrad.isOpenQuotientMap_mk.continuous_comp_iff.mp hF.continuous

theorem exists_density_bound {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ Rm : ℝ, ∀ y, ρ y ≤ Rm := by
  have hF : ContDiff ℝ ∞' (Torus.lift ρ) := hρ.smooth
  obtain ⟨M, _, hM⟩ := bdd_iteratedFDeriv_lift ρ 0 (hF.of_le (natCast_le_infty 0))
  refine ⟨M, fun y => ?_⟩
  have := hM (Torus.rep y)
  rw [norm_iteratedFDeriv_zero] at this
  have h2 : ρ y ≤ ‖Torus.lift ρ (Torus.rep y)‖ := by
    simp only [Torus.lift, Function.comp_apply, Torus.mk_rep]
    exact (le_abs_self _).trans (Real.norm_eq_abs _).symm.le
  exact h2.trans this

theorem hTransport_row_integrable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {f : Torus d → ℝ} (hf : Torus.IsSmooth f)
    (x : Torus d) : Integrable (fun y => hTransport d s f x y) (withDensityReal ρ) := by
  obtain ⟨B, hB0, hB⟩ := LocalDivAux.hT_bound hd hs0 hsd hf
  obtain ⟨Rm, hRm⟩ := exists_density_bound hρ
  have hgi : IntegrableOn (fun w : Euc d => (fun t : ℝ => B * t ^ (-s)) ‖w‖) (LocalDivAux.cube d) :=
    (LocalDivAux.integrableOn_cube_rpow (by omega) (a := s) hsd).const_mul B
  exact (LocalDivAux.kernel_int hρ hRm (LocalDivAux.measurable_hTransport hsd hf)
    (g := fun t : ℝ => B * t ^ (-s)) hB hgi x).1

theorem hsource_eq {s : ℝ} (hsd : s < d) {ρ : Torus d → ℝ} {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) (x y : Torus d) :
    Hsource d s ρ f x y = (1 / 2) * (hTransport d s f x y +
      (-(∫ y', hTransport d s f x y' ∂(withDensityReal ρ)) -
        (∫ y', hTransport d s f y y' ∂(withDensityReal ρ)) +
        ∫ x', ∫ y', hTransport d s f x' y' ∂(withDensityReal ρ) ∂(withDensityReal ρ))) := by
  unfold Hsource canonicalCenter
  have e : ∀ y, ∫ x', hTransport d s f x' y ∂(withDensityReal ρ) =
      ∫ y', hTransport d s f y y' ∂(withDensityReal ρ) := fun y =>
    integral_congr_ae (Filter.Eventually.of_forall fun x' => LocalDivAux.hTransport_symm hsd hf x' y)
  rw [e y]
  ring

theorem isSymmPair_hsource {s : ℝ} (hsd : s < d) {ρ : Torus d → ℝ} {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) : IsSymmPair (Hsource d s ρ f) := by
  intro x y
  rw [hsource_eq hsd hf x y, hsource_eq hsd hf y x, LocalDivAux.hTransport_symm hsd hf y x]
  ring

theorem integral_offZero_hsource_row (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {f : Torus d → ℝ} (hf : Torus.IsSmooth f)
    (hrow : Torus.IsSmooth (fun x => ∫ y, hTransport d s f x y ∂(withDensityReal ρ))) (x : Torus d) :
    ∫ y, offZero (Hsource d s ρ f) x y ∂(withDensityReal ρ) = 0 := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  set μ : Measure (Torus d) := withDensityReal ρ with hμ
  set r : Torus d → ℝ := fun x => ∫ y, hTransport d s f x y ∂μ with hr
  have hrc : Continuous r := continuous_of_isSmooth hrow
  have hr_int : Integrable r μ := by
    obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hrc.continuousOn
    exact Integrable.of_bound hrc.aestronglyMeasurable M (Filter.Eventually.of_forall fun y => hM y (Set.mem_univ y))
  have hne : ∀ᵐ y ∂μ, y ≠ x := by
    have h : ∀ᵐ y ∂(volume : Measure (Torus d)), y ≠ x := by
      rw [ae_iff]
      simpa using volume_singleton_torus (by omega) x
    exact (withDensity_absolutelyContinuous _ _).ae_le h
  have hae : (fun y => offZero (Hsource d s ρ f) x y) =ᵐ[μ] fun y => Hsource d s ρ f x y := by
    filter_upwards [hne] with y hy
    simp [offZero, Ne.symm hy]
  rw [integral_congr_ae hae]
  simp_rw [hsource_eq hsd hf x]
  have hhint := hTransport_row_integrable hd hs0 hsd hρ hf x
  set c : ℝ := ∫ x', r x' ∂μ with hc
  set rx : ℝ := ∫ y', hTransport d s f x y' ∂μ with hrx
  have hSfun : (fun y => -rx - r y + c) = fun y => (c - rx) - r y := by funext y; ring
  have hSint : Integrable (fun y => -rx - r y + c) μ := by
    rw [hSfun]; exact (integrable_const _).sub hr_int
  rw [integral_const_mul, integral_add hhint hSint]
  have e1 : ∫ y, (-rx - r y + c) ∂μ = -rx := by
    rw [hSfun, integral_sub (integrable_const _) hr_int]
    simp [hc]
  rw [e1]
  ring

theorem doublyCentered_hsource (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {f : Torus d → ℝ} (hf : Torus.IsSmooth f)
    (hrow : Torus.IsSmooth (fun x => ∫ y, hTransport d s f x y ∂(withDensityReal ρ))) :
    PDE.DoublyCentered (withDensityReal ρ) (offZero (Hsource d s ρ f)) := by
  have hsym : ∀ x y, offZero (Hsource d s ρ f) x y = offZero (Hsource d s ρ f) y x := by
    intro x y
    unfold offZero
    by_cases h : x = y
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
      exact isSymmPair_hsource hsd hf x y
  refine ⟨fun y => ?_, fun x => ?_⟩
  · unfold pair
    simp_rw [hsym _ y]
    exact integral_offZero_hsource_row hd hs0 hsd hρ hf hrow y
  · unfold pair
    exact integral_offZero_hsource_row hd hs0 hsd hρ hf hrow x

theorem hsource_conormal_aux (hAdd : ConormalAdd d) (hSmul : ConormalSmul d)
    {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ} (H : ParxHyp d s V β ρ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Conormal s 0 m (C * posSeminorm (m + 2) f) (offZero (Hsource d s ρ f)) ∧
      IsSymmPair (Hsource d s ρ f) ∧
      PDE.DoublyCentered (withDensityReal ρ) (offZero (Hsource d s ρ f)) := by
  have hd := H.two_le
  have hs0 : 0 < s := by
    have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    rw [H.crit]; linarith
  have hsd := H.s_lt
  have hHC := hTransport_conormal hAdd hd hs0 hsd
  obtain ⟨Ch, hCh0, hCh⟩ := hHC m
  obtain ⟨Cr, hCr0, hCr⟩ := row_data hd hsd H.rho_smooth hHC m
  obtain ⟨Csig, hCsig0, hCsig⟩ := conormal_sigma (d := d) s (fun _ => 0) m
  refine ⟨(1 / 2) * (Ch + Csig * Cr),
    mul_nonneg (by norm_num) (add_nonneg hCh0 (mul_nonneg hCsig0 hCr0)), fun f hf => ?_⟩
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal H.rho_smooth.density
  obtain ⟨hrsm, hcb⟩ := hCr f hf
  set N : ℝ := posSeminorm (m + 2) f with hN
  have hN0 : 0 ≤ N := posSeminorm_nonneg _ _
  set r : Torus d → ℝ := fun x => ∫ y, hTransport d s f x y ∂(withDensityReal ρ) with hr
  have hSig := hCsig (withDensityReal ρ) r hrsm
  have hsum := hAdd s (fun _ => 0) m (Ch * N) (Csig * Torus.cbNorm m r) _ _ (hCh f hf) hSig
  have hhalf := hSmul s (fun _ => 0) m _ _ hsum (1 / 2)
  refine ⟨?_, isSymmPair_hsource hsd hf, doublyCentered_hsource hd hs0.le hsd H.rho_smooth hf hrsm⟩
  have hcb0 : 0 ≤ Torus.cbNorm m r := by
    unfold Torus.cbNorm
    exact Finset.sum_nonneg fun k _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hB0 : 0 ≤ |(1 / 2 : ℝ)| * (Ch * N + Csig * Torus.cbNorm m r) := by positivity
  have hBle : |(1 / 2 : ℝ)| * (Ch * N + Csig * Torus.cbNorm m r) ≤ (1 / 2) * (Ch + Csig * Cr) * N := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have : Csig * Torus.cbNorm m r ≤ Csig * (Cr * N) := mul_le_mul_of_nonneg_left hcb hCsig0
    nlinarith
  refine conormalL_congr_offDiag (F := fun x y => (1 / 2) * (hTransport d s f x y +
    (-r x - r y + ∫ x', r x' ∂(withDensityReal ρ)))) (fun x y hxy => ?_)
    (conormalL_mono_B hhalf hB0 hBle)
  simp only [offZero, if_neg hxy]
  rw [hsource_eq hsd hf x y]

end HRS.Parx

end
