import Erdos883AdaptiveCertificateDataCore
import Erdos883AdaptiveCertificateTree
import Erdos883AdaptiveCertificateProfiles
import Erdos883NumericDegrees
namespace Erdos883Verified

theorem coreDegreeEntries_mem {rows : List AdaptiveProfileRow} {r : Nat}
    (hr : r < rows.length) (scale W c d H : Nat) (shift : Bool) :
    (r, if shift then coreNumericDegree scale W c d rows[r].numerator rows[r].value + H - r
      else coreNumericDegree scale W c d rows[r].numerator rows[r].value) ∈
        coreDegreeEntries scale W c d H shift rows := by
  apply List.mem_map.mpr
  refine ⟨(rows[r],r), ?_, rfl⟩
  exact List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [hr])
end Erdos883Verified
