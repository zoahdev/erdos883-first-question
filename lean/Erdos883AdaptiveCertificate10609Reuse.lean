import Erdos883AdaptiveCertificate10609Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq10609 : adaptiveRows10609 = adaptiveRowsThrough 10609 adaptiveRows199999 := by
  unfold adaptiveRows10609
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
