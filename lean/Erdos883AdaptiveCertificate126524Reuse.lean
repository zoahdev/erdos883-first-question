import Erdos883AdaptiveCertificate126524Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq126524 : adaptiveRows126524 = adaptiveRowsThrough 126524 adaptiveRows199999 := by
  unfold adaptiveRows126524
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
