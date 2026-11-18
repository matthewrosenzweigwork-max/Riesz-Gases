import HRS.MC.E213U16o

/-!
# Packet e213u16, file p: additivity of the window drift in the interval
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10

variable {d : ℕ}

section Split

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u16_winDrift_split (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (bq : ℝ → NegSobolev d (rLvl d)) (hbm : Measurable (nearCoef 0 bq))
    (hbi : IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 (a + T))) {u u' u'' : ℝ} (hu : 0 ≤ u) (huu : u ≤ u')
    (huu' : u' ≤ u'') (hu'' : u'' ≤ a + T) :
    winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq v)) u u'' =
      winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq v)) u u' +
        winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq v)) u' u'' := by
  obtain ⟨C, c, hC, hc, Vev, hsp⟩ := HRS.MC.E213U1.u1_vev hE
  have c1 := HRS.MC.E213U1.winDrift_cont_proof hE T hT a ha bq hbm hbi u u' hu huu (huu'.trans hu'')
  have c2 := HRS.MC.E213U1.winDrift_cont_proof hE T hT a ha bq hbm hbi u' u'' (hu.trans huu) huu' hu''
  have c12 := HRS.MC.E213U1.winDrift_cont_proof hE T hT a ha bq hbm hbi u u'' hu (huu.trans huu') hu''
  have hint : ∀ t : Set.Icc (0 : ℝ) (a + T),
      (∫ v in Set.Ioc u (min u'' (t : ℝ)), Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (t : ℝ) v
        (NegSobolev.embed m (bq v))) =
      (∫ v in Set.Ioc u (min u' (t : ℝ)), Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (t : ℝ) v
        (NegSobolev.embed m (bq v))) +
      (∫ v in Set.Ioc u' (min u'' (t : ℝ)), Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (t : ℝ) v
        (NegSobolev.embed m (bq v))) := by
    intro t
    have hsp' := hsp
    obtain ⟨p12, -⟩ := HRS.MC.E213U1.u1_Fint hE hC hc hsp' T a hT ha bq hbm hbi u u'' hu hu'' t t.2
    obtain ⟨p1, q1, -⟩ := HRS.MC.E213U1.u1_Fint hE hC hc hsp' T a hT ha bq hbm hbi u u' hu (huu'.trans hu'') t t.2
    obtain ⟨p2, q2, -⟩ := HRS.MC.E213U1.u1_Fint hE hC hc hsp' T a hT ha bq hbm hbi u' u'' (hu.trans huu) hu'' t t.2
    rw [p12, p1, p2, ← setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc q1 q2,
      Set.Ioc_union_Ioc_eq_Ioc huu huu']
  unfold winDrift driftInc
  rw [← map_add]
  congr 1
  classical
  refine HRS.MC.E213O.e213o_ext (fun t => ?_)
  rw [HRS.MC.E213O.e213o_pathOf_at' _ c12 t]
  have hadd : ∀ (w₁ w₂ : PathSpace d m (a + T)) (t : Set.Icc (0 : ℝ) (a + T)),
      (w₁ + w₂).at' t = w₁.at' t + w₂.at' t := fun _ _ _ => rfl
  rw [hadd, HRS.MC.E213O.e213o_pathOf_at' _ c1 t, HRS.MC.E213O.e213o_pathOf_at' _ c2 t]
  exact hint t

/-- Telescoping of the window drift over a monotone partition. -/
theorem u16_winDrift_sum (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (bq : ℝ → NegSobolev d (rLvl d)) (hbm : Measurable (nearCoef 0 bq))
    (hbi : IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 (a + T))) (u : ℕ → ℝ) (hmono : Monotone u)
    (h0 : 0 ≤ u 0) {n : ℕ} (hn : 1 ≤ n) (hnH : u n ≤ a + T) :
    winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq v)) (u 0) (u n) =
      ∑ i ∈ Finset.range n, winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq v)) (u i) (u (i + 1)) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ← ih ((hmono (Nat.le_succ n)).trans hnH)]
    exact u16_winDrift_split hE T hT a ha bq hbm hbi h0 (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n)) hnH

end Split

end HRS.MC.E213U16

end
