import Erdos883AdaptiveCertificate1262Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1262 : coreProfileOrderCheck adaptiveRows1262 = true := by decide +kernel
end Erdos883Verified
