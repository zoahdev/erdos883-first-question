import Erdos883AdaptiveCertificate1241Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1241 : coreProfileOrderCheck adaptiveRows1241 = true := by decide +kernel
end Erdos883Verified
