import Erdos883AdaptiveCertificate139177Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq139177 : adaptiveRows139177 = adaptiveRowsThrough 139177 adaptiveRows199999 := by
  unfold adaptiveRows139177
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
