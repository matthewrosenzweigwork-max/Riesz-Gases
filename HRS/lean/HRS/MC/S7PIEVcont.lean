import HRS.MC.S7PIEVbd
import HRS.MC.S7PIECont
import HRS.MC.S7PIEStrong

/-!
# Packet PI-E, part 8: continuity of `V^{t,u}F` in `t` and in `u`

`pie_V_tendsto`: along any filter on which the matrix entries `pieT u t j k` converge, `V^{t,u}F` converges in `E_m`.
Combined with the Lipschitz bounds of `S7PIECont` this gives continuity of `t ↦ V^{t,u}F` and `u ↦ V^{t,u}F`.
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.PIE

open HRS HRS.PDE HRS.A33 HRS.Sec7

variable {d : ℕ}

lemma pie_jp_sublevel_finite (R : ℝ) : {k : NonzeroLattice d | Lattice.jp k.1 ≤ R}.Finite := by
  classical
  set N : ℤ := ⌈R⌉ with hN
  have hsub : {k : Lattice d | Lattice.jp k ≤ R} ⊆ Set.Icc (fun _ : Fin d => -N) (fun _ => N) := by
    intro k hk
    have h1 : Lattice.enorm k ≤ R := by
      have := Torus.two_pi_enorm_le_jp k
      have h2 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      have h3 : 0 ≤ Lattice.enorm k := norm_nonneg _
      nlinarith [hk.out]
    have h4 : ∀ i, |(k i : ℝ)| ≤ R := fun i => by
      have : ‖(Lattice.toEuc k) i‖ ≤ ‖Lattice.toEuc k‖ := PiLp.norm_apply_le _ i
      have e : (Lattice.toEuc k) i = (k i : ℝ) := rfl
      rw [e, Real.norm_eq_abs] at this
      exact this.trans h1
    have hR : R ≤ (N : ℝ) := Int.le_ceil R
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := (abs_le.1 ((h4 i).trans hR)).1
      exact_mod_cast this
    · have := (abs_le.1 ((h4 i).trans hR)).2
      exact_mod_cast this
  have hfin : (Set.Icc (fun _ : Fin d => -N) (fun _ => N)).Finite := Set.finite_Icc _ _
  exact (hfin.subset hsub).preimage (Set.injOn_of_injective Subtype.val_injective)

/-- a finite-section bound for the matrix at a real exponent `m` (interpolating between two integer levels) -/
lemma pie_finBd_real {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (m : ℝ) (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (hJ : n₀ + 1 ≤ J) (hm0 : (n₀ : ℝ) < m) (hm1 : m ≤ n₀ + 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Set.Ioc 0 T, ∀ u ∈ Set.Icc 0 t,
      pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) m) A := by
  obtain ⟨C0, hC0, h0⟩ := pie_finBd H n₀ hn₀ (by omega)
  obtain ⟨C1, hC1, h1⟩ := pie_finBd H (n₀ + 1) (by omega) hJ
  set θ : ℝ := m - n₀ with hθ
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  refine ⟨C0 ^ (1 - θ) * C1 ^ θ, mul_nonneg (Real.rpow_nonneg hC0 _) (Real.rpow_nonneg hC1 _),
    fun t ht u hu => ?_⟩
  have hw : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hint := pie_interp hw (T := pieT D μ u t) hC0 hC1 (h0 t ht u hu)
    (by simpa using h1 t ht u hu) hθ0 hθ1
  have hσ : (1 - θ) * (n₀ : ℝ) + θ * ((n₀ : ℝ) + 1) = m := by
    simp only [hθ]; ring
  rw [hσ] at hint
  exact hint

/-- the coordinates of `V^{t,u}F` -/
lemma pie_Vprop_coord (D : DynData d) (μ : ℝ → Torus d → ℝ) (m : ℝ) (t u : ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hH : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) m) A)
    (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (Vprop D μ m t u F) k =
      Lattice.jp k.1 ^ (-m) * ∑' j, NegSobolev.fourierCoeff F j * pieT D μ u t j k := by
  have hw : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hcoord : ∀ j, Lattice.jp j.1 ^ (-m) * NegSobolev.fourierCoeff F j = NegSobolev.coord F j := by
    intro j
    unfold NegSobolev.fourierCoeff
    rw [← mul_assoc, ← Real.rpow_add (hw j)]; simp
  obtain ⟨hF2, -⟩ := NegSobolev.coord_sq F
  have ha : Summable fun j : NonzeroLattice d =>
      (Lattice.jp j.1 ^ (-m) * NegSobolev.fourierCoeff F j) ^ 2 :=
    hF2.congr fun j => by rw [hcoord]
  obtain ⟨hs, -⟩ := pie_dual hw hA hH (fun j => NegSobolev.fourierCoeff F j) ha
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) *
      NegSobolev.eval F (propagator D μ u t (Torus.realMode k))) 2 := by
    rw [Torus.memℓp_two_iff]
    exact hs
  have hV : Vprop D μ m t u F = NegSobolev.ofSeq m
      (fun k => NegSobolev.eval F (propagator D μ u t (Torus.realMode k))) := rfl
  rw [hV, NegSobolev.coord_ofSeq_of_mem _ hmem k]
  rfl

/-- `V^{t,u}F` converges in `E_m` along any filter on which the matrix entries converge. -/
theorem pie_V_tendsto {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (m : ℝ) (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (hJ : n₀ + 1 ≤ J) (hm0 : (n₀ : ℝ) < m) (hm1 : m ≤ n₀ + 1)
    {X : Type*} (l : Filter X) (tt uu : X → ℝ) (t₀ u₀ : ℝ)
    (hmem : ∀ᶠ x in l, tt x ∈ Set.Ioc 0 T ∧ uu x ∈ Set.Icc 0 (tt x))
    (h₀ : t₀ ∈ Set.Ioc 0 T ∧ u₀ ∈ Set.Icc 0 t₀)
    (hc : ∀ j k, Tendsto (fun x => pieT D μ (uu x) (tt x) j k) l (𝓝 (pieT D μ u₀ t₀ j k)))
    (F : NegSobolev d m) :
    Tendsto (fun x => Vprop D μ m (tt x) (uu x) F) l (𝓝 (Vprop D μ m t₀ u₀ F)) := by
  obtain ⟨A, hA, hAb⟩ := pie_finBd_real H m n₀ hn₀ hJ hm0 hm1
  obtain ⟨A', hA', hA'b⟩ := pie_finBd H n₀ hn₀ (by omega)
  have hw : ∀ k : NonzeroLattice d, 1 ≤ Lattice.jp k.1 := fun k => Torus.jp_ge_one k.1
  have hwpos : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hcoord : ∀ j, Lattice.jp j.1 ^ (-m) * NegSobolev.fourierCoeff F j = NegSobolev.coord F j := by
    intro j
    unfold NegSobolev.fourierCoeff
    rw [← mul_assoc, ← Real.rpow_add (hwpos j)]; simp
  obtain ⟨hF2, -⟩ := NegSobolev.coord_sq F
  have ha : Summable fun j : NonzeroLattice d =>
      (Lattice.jp j.1 ^ (-m) * NegSobolev.fourierCoeff F j) ^ 2 :=
    hF2.congr fun j => by rw [hcoord]
  have key := pie_strong_abs l (fun k : NonzeroLattice d => Lattice.jp k.1) hw pie_jp_sublevel_finite
    (fun x => pieT D μ (uu x) (tt x)) (pieT D μ u₀ t₀) (m := m) (n := (n₀ : ℝ)) hm0 hA hA'
    (hmem.mono fun x hx => hAb _ hx.1 _ hx.2) (hAb _ h₀.1 _ h₀.2)
    (hmem.mono fun x hx => hA'b _ hx.1 _ hx.2) (hA'b _ h₀.1 _ h₀.2) hc
    (fun j => NegSobolev.fourierCoeff F j) ha
  have hsq := (Real.continuous_sqrt.tendsto 0).comp key
  rw [Real.sqrt_zero] at hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine hsq.congr' ?_
  filter_upwards [hmem] with x hx
  simp only [Function.comp]
  obtain ⟨-, hnorm⟩ := NegSobolev.coord_sq (Vprop D μ m (tt x) (uu x) F - Vprop D μ m t₀ u₀ F)
  rw [← Real.sqrt_sq (norm_nonneg _), hnorm]
  congr 1
  refine tsum_congr fun k => ?_
  have e1 := pie_Vprop_coord D μ m (tt x) (uu x) hA (hAb _ hx.1 _ hx.2) F k
  have e2 := pie_Vprop_coord D μ m t₀ u₀ hA (hAb _ h₀.1 _ h₀.2) F k
  have e3 : NegSobolev.coord (Vprop D μ m (tt x) (uu x) F - Vprop D μ m t₀ u₀ F) k =
      NegSobolev.coord (Vprop D μ m (tt x) (uu x) F) k - NegSobolev.coord (Vprop D μ m t₀ u₀ F) k := rfl
  rw [e3, e1, e2]
  ring_nf

end HRS.MC.Sec7.PIE

end
