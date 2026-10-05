import Erdos883AdaptiveCertificate1310Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1310 : coreProfileOrderCheck adaptiveRows1310 = true := by decide +kernel
end Erdos883Verified
