import HRS.Commutator.Torus.Bridge
import HRS.Energy.Commutator.SubAssembly

/-! Statement check: the torus bridge has the statement of the (Route H) `HRS.Commutator.commutator_estimate_sub`.
Not imported by the assembly chain (which no longer depends on Route H). -/

namespace HRS.Commutator.TorusNote

example : @commutator_estimate_sub_of_torus = @HRS.Commutator.commutator_estimate_sub := rfl

end HRS.Commutator.TorusNote
