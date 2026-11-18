import HRS.MC.S7FCW5
import HRS.MC.QRPChaosLim
import HRS.MC.QRPHd
import HRS.MC.WCI
import HRS.Equilibrium.FieldSingAux

/-!
# S7FCW9Lem: general helpers for the proof of `s7_FC_C4_field_all_t` (FC-C4)

Helpers (no Regime): cube exhaustion of the nonzero frequencies, measurability of `NegSobolev.ofSeq`
of a measurable family, a.e. transfer of `HasFiniteGaussianCoeffs`, `ModeCovBound`, `IsHalfWick`,
the evaluation identity `eval F (realMode k) = fourierCoeff F k`, and the lattice summability.
All names carry the prefix `S7FCW9_`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCW9

open HRS HRS.Sec7 HRS.MC.QRSpec

variable {d : ℕ}

/-- The cube `{k ∈ ℤ^d ∖ {0} : max_i |k_i| ≤ L}`. -/
def S7FCW9_cube (d L : ℕ) : Finset (NonzeroLattice d) :=
  Finset.subtype (fun a : Lattice d => a ≠ 0)
    (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ))

theorem S7FCW9_mem_cube_iff (L : ℕ) (a : NonzeroLattice d) :
    a ∈ S7FCW9_cube d L ↔ ∀ i, |a.1 i| ≤ (L : ℤ) := by
  unfold S7FCW9_cube
  rw [Finset.mem_subtype, Fintype.mem_piFinset]
  simp only [Finset.mem_Icc, abs_le]

theorem S7FCW9_cube_mono : Monotone (S7FCW9_cube d) := by
  intro m n hmn a ha
  rw [S7FCW9_mem_cube_iff] at ha ⊢
  intro i
  exact (ha i).trans (by exact_mod_cast hmn)

theorem S7FCW9_exists_cube (S : Finset (NonzeroLattice d)) : ∃ L : ℕ, S ⊆ S7FCW9_cube d L := by
  refine ⟨∑ b ∈ S, ∑ j : Fin d, (b.1 j).natAbs, fun a ha => ?_⟩
  rw [S7FCW9_mem_cube_iff]
  intro i
  have h1 : (a.1 i).natAbs ≤ ∑ b ∈ S, ∑ j : Fin d, (b.1 j).natAbs :=
    le_trans (Finset.single_le_sum (f := fun j => (a.1 j).natAbs) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i))
      (Finset.single_le_sum (f := fun b => ∑ j : Fin d, (b.1 j).natAbs) (fun b _ => Nat.zero_le _) ha)
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h1

theorem S7FCW9_tendsto_cube : Tendsto (fun n : ℕ => S7FCW9_cube d n) atTop atTop :=
  tendsto_atTop_atTop_of_monotone S7FCW9_cube_mono fun S => by
    obtain ⟨L, hL⟩ := S7FCW9_exists_cube S
    exact ⟨L, hL⟩

theorem S7FCW9_tendsto_cube_succ : Tendsto (fun n : ℕ => S7FCW9_cube d (n + 1)) atTop atTop :=
  S7FCW9_tendsto_cube.comp (tendsto_add_atTop_nat 1)

theorem S7FCW9_tendsto_of_hasSum {f : NonzeroLattice d → ℝ} {a : ℝ} (h : HasSum f a) :
    Tendsto (fun n : ℕ => ∑ k ∈ S7FCW9_cube d n, f k) atTop (𝓝 a) := by
  have h' : Tendsto (fun s : Finset (NonzeroLattice d) => ∑ b ∈ s, f b) atTop (𝓝 a) := h
  exact h'.comp S7FCW9_tendsto_cube

theorem S7FCW9_summable_jp (α : ℝ) (hα : (d : ℝ) < α) :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-α) := by
  have h := summable_jp_rpow (d := d) (α / 2) (by linarith)
  rwa [show 2 * (α / 2) = α by ring] at h

theorem S7FCW9_memℓp_two_iff_bdd (g : NonzeroLattice d → ℝ) :
    Memℓp g 2 ↔ ∃ M : ℕ, ∀ n : ℕ, ∑ k ∈ S7FCW9_cube d n, g k ^ 2 ≤ M := by
  rw [Torus.memℓp_two_iff]
  constructor
  · intro hs
    refine ⟨⌈∑' k, g k ^ 2⌉₊, fun n => ?_⟩
    have h1 : ∑ k ∈ S7FCW9_cube d n, g k ^ 2 ≤ ∑' k, g k ^ 2 :=
      Summable.sum_le_tsum _ (fun k _ => sq_nonneg _) hs
    exact h1.trans (Nat.le_ceil _)
  · rintro ⟨M, hM⟩
    refine summable_of_sum_le (c := (M : ℝ)) (fun k => sq_nonneg (g k)) fun u => ?_
    obtain ⟨n, hn⟩ := S7FCW9_exists_cube u
    exact (Finset.sum_le_sum_of_subset_of_nonneg hn (fun k _ _ => sq_nonneg (g k))).trans (hM n)

theorem S7FCW9_measurableSet_memℓp {α : Type*} [MeasurableSpace α] (r : ℝ)
    (c : NonzeroLattice d → α → ℝ) (hc : ∀ k, Measurable (c k)) :
    MeasurableSet {a | Memℓp (fun k => Lattice.jp k.1 ^ (-r) * c k a) 2} := by
  have hset : {a | Memℓp (fun k => Lattice.jp k.1 ^ (-r) * c k a) 2} =
      ⋃ M : ℕ, ⋂ n : ℕ, {a | ∑ k ∈ S7FCW9_cube d n, (Lattice.jp k.1 ^ (-r) * c k a) ^ 2 ≤ (M : ℝ)} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, S7FCW9_memℓp_two_iff_bdd]
  rw [hset]
  refine MeasurableSet.iUnion fun M => MeasurableSet.iInter fun n => ?_
  refine measurableSet_le ?_ measurable_const
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (measurable_const.mul (hc k)).pow_const 2

theorem S7FCW9_isContinuous_single (r : ℝ) (k : NonzeroLattice d) :
    Continuous fun x : ℝ => (lp.single 2 k x : NegSobolev d r) :=
  (lp.isometry_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) k).continuous

/-- Measurability of `ω ↦ ofSeq r (c · ω)` for a family of measurable coefficient maps. -/
theorem S7FCW9_measurable_ofSeq {α : Type*} [MeasurableSpace α] (r : ℝ)
    (c : NonzeroLattice d → α → ℝ) (hc : ∀ k, Measurable (c k)) :
    Measurable fun a => NegSobolev.ofSeq r (fun k => c k a) := by
  classical
  set G : Set α := {a | Memℓp (fun k => Lattice.jp k.1 ^ (-r) * c k a) 2} with hGdef
  have hG : MeasurableSet G := S7FCW9_measurableSet_memℓp r c hc
  let Φ : ℕ → (NonzeroLattice d → ℝ) → NegSobolev d r := fun n y =>
    ∑ k ∈ S7FCW9_cube d n, (lp.single 2 k (Lattice.jp k.1 ^ (-r) * y k) : NegSobolev d r)
  have hΦc : ∀ n, Continuous (Φ n) := fun n =>
    continuous_finset_sum _ fun k _ =>
      (S7FCW9_isContinuous_single r k).comp (continuous_const.mul (continuous_apply k))
  let Ψ : ℕ → α → NegSobolev d r := fun n a => Φ n (fun k => c k a)
  have hΨm : ∀ n, Measurable (Ψ n) := fun n =>
    (hΦc n).measurable.comp (measurable_pi_iff.2 hc)
  have hlim : ∀ a : α, Tendsto (fun n => G.indicator (Ψ n) a) atTop
      (𝓝 (NegSobolev.ofSeq r (fun k => c k a))) := by
    intro a
    by_cases ha : a ∈ G
    · simp only [Set.indicator_of_mem ha]
      have ha' : Memℓp (fun k => Lattice.jp k.1 ^ (-r) * c k a) 2 := ha
      let x : NegSobolev d r := (⟨fun k => Lattice.jp k.1 ^ (-r) * c k a, ha'⟩ :
        lp (fun _ : NonzeroLattice d => ℝ) 2)
      have hx : NegSobolev.ofSeq r (fun k => c k a) = x := NegSobolev.ofSeq_of_mem _ ha'
      rw [hx]
      have hsum : HasSum (fun i : NonzeroLattice d =>
          (lp.single 2 i (Lattice.jp i.1 ^ (-r) * c i a) : NegSobolev d r)) x :=
        lp.hasSum_single ENNReal.ofNat_ne_top x
      exact (show Tendsto (fun s : Finset (NonzeroLattice d) => ∑ b ∈ s,
          (lp.single 2 b (Lattice.jp b.1 ^ (-r) * c b a) : NegSobolev d r)) atTop (𝓝 x) from hsum).comp
        S7FCW9_tendsto_cube
    · simp only [Set.indicator_of_notMem ha]
      have ha' : ¬ Memℓp (fun k => Lattice.jp k.1 ^ (-r) * c k a) 2 := ha
      have h0 : NegSobolev.ofSeq r (fun k => c k a) = 0 := by
        unfold NegSobolev.ofSeq
        exact dif_neg ha'
      rw [h0]
      exact tendsto_const_nhds
  exact measurable_of_tendsto_metrizable (fun n => (hΨm n).indicator hG) (tendsto_pi_nhds.2 hlim)

theorem S7FCW9_fourierCoeff_ofSeq {m : ℝ} (c : NonzeroLattice d → ℝ)
    (h : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (NegSobolev.ofSeq m c) k = c k := by
  unfold NegSobolev.fourierCoeff
  rw [NegSobolev.coord_ofSeq_of_mem c h k, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1),
    add_neg_cancel, Real.rpow_zero, one_mul]

theorem S7FCW9_eval_realMode {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.eval F (Torus.realMode k) = NegSobolev.fourierCoeff F k := by
  have hc : ∀ j : NonzeroLattice d,
      Torus.funRealCoeff (Torus.realMode k : Torus d → ℝ) j = if j = k then 1 else 0 := by
    intro j
    unfold Torus.funRealCoeff
    rw [Torus.realMode_orthonormal j k]
  unfold NegSobolev.eval
  rw [tsum_eq_single k (fun j hj => by simp [hc j, hj])]
  simp [hc k]

theorem S7FCW9_sq_rpow (x m : ℝ) : (x ^ 2) ^ m = |x| ^ (2 * m) := by
  rw [Real.rpow_mul (abs_nonneg x), Real.rpow_two, sq_abs]

theorem S7FCW9_hfgc_congr {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {r : ℝ}
    {X Y : Ω → NegSobolev d r} (h : X =ᵐ[P] Y) (hX : HasFiniteGaussianCoeffs P X) :
    HasFiniteGaussianCoeffs P Y := by
  intro S
  obtain ⟨h1, h2⟩ := hX S
  have hae : (fun ω (k : S) => NegSobolev.fourierCoeff (X ω) k.1) =ᵐ[P]
      (fun ω (k : S) => NegSobolev.fourierCoeff (Y ω) k.1) := by
    have hk : ∀ᵐ ω ∂P, ∀ k : S, NegSobolev.fourierCoeff (X ω) k.1 = NegSobolev.fourierCoeff (Y ω) k.1 :=
      ae_all_iff.2 fun k => h.mono fun ω hω => by simp only [hω]
    filter_upwards [hk] with ω hω
    funext k
    exact hω k
  refine ⟨h1.congr hae, fun k => ?_⟩
  have hI : ∫ ω, NegSobolev.fourierCoeff (Y ω) k ∂P = ∫ ω, NegSobolev.fourierCoeff (X ω) k ∂P :=
    integral_congr_ae (h.mono fun ω hω => by simp only [hω])
  rw [hI]
  exact h2 k

theorem S7FCW9_mcb_congr {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {r K : ℝ}
    {X Y : Ω → NegSobolev d r} (h : X =ᵐ[P] Y) (hX : ModeCovBound P X K) : ModeCovBound P Y K := by
  intro S a
  have e : ∫ ω, (∑ k ∈ S, a k * NegSobolev.fourierCoeff (Y ω) k) ^ 2 ∂P =
      ∫ ω, (∑ k ∈ S, a k * NegSobolev.fourierCoeff (X ω) k) ^ 2 ∂P :=
    integral_congr_ae (h.mono fun ω hω => by simp only [hω])
  rw [e]
  exact hX S a

theorem S7FCW9_isHalfWick_congr {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {r : ℝ}
    {η η' : Ω → NegSobolev d r} (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ)
    {Q Q' : Ω → ℝ} (hη : η =ᵐ[P] η') (hQ : Q =ᵐ[P] Q') (H : IsHalfWick P η μ h Q) :
    IsHalfWick P η' μ h Q' := by
  have hfc : ∀ k : NonzeroLattice d, (fun ω => NegSobolev.fourierCoeff (η ω) k) =ᵐ[P]
      (fun ω => NegSobolev.fourierCoeff (η' ω) k) := fun k =>
    hη.mono fun ω hω => by simp only [hω]
  have hint : ∀ k l : NonzeroLattice d,
      ∫ ω', NegSobolev.fourierCoeff (η ω') k * NegSobolev.fourierCoeff (η ω') l ∂P =
        ∫ ω', NegSobolev.fourierCoeff (η' ω') k * NegSobolev.fourierCoeff (η' ω') l ∂P :=
    fun k l => integral_congr_ae ((hfc k).mul (hfc l))
  have key : ∀ S : Finset (NonzeroLattice d),
      ∫⁻ ω, ‖Q' ω - (1 / 2) * ∑ k ∈ S, ∑ l ∈ S, wickCoeff μ h k l * (NegSobolev.fourierCoeff (η' ω) k *
        NegSobolev.fourierCoeff (η' ω) l - ∫ ω', NegSobolev.fourierCoeff (η' ω') k *
          NegSobolev.fourierCoeff (η' ω') l ∂P)‖ₑ ^ 2 ∂P =
      ∫⁻ ω, ‖Q ω - (1 / 2) * ∑ k ∈ S, ∑ l ∈ S, wickCoeff μ h k l * (NegSobolev.fourierCoeff (η ω) k *
        NegSobolev.fourierCoeff (η ω) l - ∫ ω', NegSobolev.fourierCoeff (η ω') k *
          NegSobolev.fourierCoeff (η ω') l ∂P)‖ₑ ^ 2 ∂P := by
    intro S
    refine lintegral_congr_ae ?_
    filter_upwards [hη, hQ] with ω h1 h2
    simp only [hint, h1, h2]
  unfold IsHalfWick at H ⊢
  exact Tendsto.congr (fun S => (key S).symm) H

end HRS.MC.Sec7.S7FCW9

end
