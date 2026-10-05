import Erdos883AdaptiveCertificate64924Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq64924 : adaptiveRows64924 = adaptiveRowsThrough 64924 adaptiveRows199999 := by
  unfold adaptiveRows64924
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
