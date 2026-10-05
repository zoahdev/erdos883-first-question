import Erdos883AdaptiveCertificate1262Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptivePermutation1262 : coreOrderPermutationCheck 1262 (coreProfileValues adaptiveRows1262) = true := by decide +kernel
end Erdos883Verified
