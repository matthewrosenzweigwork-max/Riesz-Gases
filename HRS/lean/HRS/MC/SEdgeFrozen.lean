import HRS.MC.SEdgeB14
import HRS.MC.SEdgeU4

/-!
# Proposition 7.4: the frozen statements `HRS.Sec7.static_edge` and `HRS.Sec7.static_edge_char`

The relocated proofs of the two frozen statements (Section 7.4) are
`HRS.MC.SEdge.B14.static_edge_assembly_proof` and `HRS.MC.SEdge.U4.static_edge_char_assembly_proof`; the `type_of%`
ties below check that their types coincide with the frozen statements.  This file is sorry-free.
-/

noncomputable section

example := (@HRS.MC.SEdge.B14.static_edge_assembly_proof : type_of% @HRS.Sec7.static_edge)

example := (@HRS.MC.SEdge.U4.static_edge_char_assembly_proof : type_of% @HRS.Sec7.static_edge_char)

end
