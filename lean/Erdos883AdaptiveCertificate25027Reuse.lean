import Erdos883AdaptiveCertificate25027Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq25027 : adaptiveRows25027 = adaptiveRowsThrough 25027 adaptiveRows199999 := by
  unfold adaptiveRows25027
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
