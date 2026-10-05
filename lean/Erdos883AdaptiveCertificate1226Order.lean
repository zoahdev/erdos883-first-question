import Erdos883AdaptiveCertificate1226Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1226 : coreProfileOrderCheck adaptiveRows1226 = true := by decide +kernel
end Erdos883Verified
