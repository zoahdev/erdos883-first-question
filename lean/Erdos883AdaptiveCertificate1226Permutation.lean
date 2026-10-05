import Erdos883AdaptiveCertificate1226Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptivePermutation1226 : coreOrderPermutationCheck 1226 (coreProfileValues adaptiveRows1226) = true := by decide +kernel
end Erdos883Verified
