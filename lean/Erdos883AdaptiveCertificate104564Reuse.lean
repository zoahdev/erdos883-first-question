import Erdos883AdaptiveCertificate104564Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq104564 : adaptiveRows104564 = adaptiveRowsThrough 104564 adaptiveRows199999 := by
  unfold adaptiveRows104564
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
