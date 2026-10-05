import Erdos883AdaptiveCertificate27530Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq27530 : adaptiveRows27530 = adaptiveRowsThrough 27530 adaptiveRows199999 := by
  unfold adaptiveRows27530
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
