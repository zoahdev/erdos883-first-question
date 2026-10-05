import Erdos883AdaptiveCertificate53655Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq53655 : adaptiveRows53655 = adaptiveRowsThrough 53655 adaptiveRows199999 := by
  unfold adaptiveRows53655
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
