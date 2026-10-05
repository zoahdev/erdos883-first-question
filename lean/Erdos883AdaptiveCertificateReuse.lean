import Erdos883AdaptiveProfileReuse
namespace Erdos883Verified

theorem coreProfileMetadataCheck_rowsThrough {rows : List AdaptiveProfileRow}
    (h : coreProfileMetadataCheck rows = true) (U : Nat) :
    coreProfileMetadataCheck (adaptiveRowsThrough U rows) = true := by
  apply List.all_eq_true.mpr
  intro row hr
  exact List.all_eq_true.mp h row (List.mem_filter.mp hr).1

theorem adaptiveRowsThrough_flatten (U : Nat) (chunks : List (List AdaptiveProfileRow)) :
    adaptiveRowsThrough U chunks.flatten = (chunks.map (adaptiveRowsThrough U)).flatten := by
  simp only [adaptiveRowsThrough, List.filter_flatten]
  rfl
#print axioms coreProfileMetadataCheck_rowsThrough
#print axioms adaptiveRowsThrough_flatten
end Erdos883Verified
