import Erdos883AdaptiveCertificate1333Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptivePermutation1333 : coreOrderPermutationCheck 1333 (coreProfileValues adaptiveRows1333) = true := by decide +kernel
end Erdos883Verified
