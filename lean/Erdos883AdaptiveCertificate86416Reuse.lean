import Erdos883AdaptiveCertificate86416Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq86416 : adaptiveRows86416 = adaptiveRowsThrough 86416 adaptiveRows199999 := by
  unfold adaptiveRows86416
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
