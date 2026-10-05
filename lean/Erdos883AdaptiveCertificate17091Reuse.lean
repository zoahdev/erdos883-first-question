import Erdos883AdaptiveCertificate17091Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq17091 : adaptiveRows17091 = adaptiveRowsThrough 17091 adaptiveRows199999 := by
  unfold adaptiveRows17091
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
