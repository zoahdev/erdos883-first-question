import Erdos883AdaptiveCertificate153095Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq153095 : adaptiveRows153095 = adaptiveRowsThrough 153095 adaptiveRows199999 := by
  unfold adaptiveRows153095
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
