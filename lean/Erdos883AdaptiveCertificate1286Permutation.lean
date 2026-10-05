import Erdos883AdaptiveCertificate1286Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptivePermutation1286 : coreOrderPermutationCheck 1286 (coreProfileValues adaptiveRows1286) = true := by decide +kernel
end Erdos883Verified
