import Erdos883AdaptiveCertificate11671Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq11671 : adaptiveRows11671 = adaptiveRowsThrough 11671 adaptiveRows199999 := by
  unfold adaptiveRows11671
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
