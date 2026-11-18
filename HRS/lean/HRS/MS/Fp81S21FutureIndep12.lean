import HRS.MS.Fp81S21FutureIndep7
import HRS.MS.Fp81S21FutureIndep9

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.GenPath

/-- Once a path has the given source coordinates at a dense countable set of
times, it has an almost-everywhere measurable version and inherits independence
from the whole source family. This is the transfer step; it does not assert
existence of such a path. -/
theorem fp81s21_path_indep_of_source_coordinates
    {d : ℕ} {m H : ℝ} (hH : 0 ≤ H)
    {Ω A I : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) (past : Ω → A) (B : I → Ω → ℝ)
    (hBm : ∀ i, Measurable (B i))
    (hIndep : IndepFun past (fun ω i => B i ω) P)
    (X : Ω → OscPath d m H)
    (s : ℕ → Icc (0 : ℝ) H) (hs : DenseRange s)
    (b : ℕ × MultiIndex d → I)
    (hcoord : ∀ i, (fun ω => OscDual.coord (OscPath.at' (X ω) (s i.1)) i.2)
      =ᵐ[P] B (b i)) :
    AEMeasurable X P ∧ IndepFun past X P := by
  let Ψ := s56PathCoords (d := d) m H s
  have hemb := s56_measurableEmbedding_pathCoords (d := d) m H s hs
  obtain ⟨g, hgm, hg⟩ := hemb.exists_measurable_extend (g := id) measurable_id (fun _ => ⟨0⟩)
  let select : (I → ℝ) → (ℕ × MultiIndex d → ℝ) := fun z i => z (b i)
  have hselect : Measurable select := measurable_pi_iff.2 fun i => measurable_pi_apply (b i)
  have hfield : Measurable (fun ω i => B i ω) := measurable_pi_iff.2 hBm
  have hx : (fun ω => g (select (fun i => B i ω))) =ᵐ[P] X := by
    have hall : ∀ᵐ ω ∂P, ∀ i, OscDual.coord (OscPath.at' (X ω) (s i.1)) i.2 = B (b i) ω :=
      ae_all_iff.2 hcoord
    filter_upwards [hall] with ω hω
    have hc : Ψ (X ω) = select (fun i => B i ω) := by
      funext i
      exact hω i
    rw [← hc]
    exact congrFun hg (X ω)
  have hm : Measurable (fun ω => g (select (fun i => B i ω))) :=
    hgm.comp (hselect.comp hfield)
  have hind : IndepFun past (fun ω => g (select (fun i => B i ω))) P := by
    change IndepFun (id ∘ past) ((fun z => g (select z)) ∘ (fun ω i => B i ω)) P
    exact hIndep.comp measurable_id (hgm.comp hselect)
  exact ⟨hm.aemeasurable.congr hx, hind.congr (Filter.Eventually.of_forall fun _ => rfl) hx⟩

#print axioms fp81s21_path_indep_of_source_coordinates

end HRS.Fp81.S21
end
