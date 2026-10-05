import Erdos883AdaptiveCertificate48777Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq48777 : adaptiveRows48777 = adaptiveRowsThrough 48777 adaptiveRows199999 := by
  unfold adaptiveRows48777
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
