import Erdos883AdaptiveCertificate1310Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptivePermutation1310 : coreOrderPermutationCheck 1310 (coreProfileValues adaptiveRows1310) = true := by decide +kernel
end Erdos883Verified
