import Erdos883AdaptiveCertificate1333Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1333 : coreProfileOrderCheck adaptiveRows1333 = true := by decide +kernel
end Erdos883Verified
