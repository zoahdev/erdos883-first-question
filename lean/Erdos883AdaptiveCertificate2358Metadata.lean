import Erdos883AdaptiveCertificate2358Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveMetadata2358 : coreProfileMetadataCheck adaptiveRows2358 = true := by decide +kernel
theorem adaptiveOrder2358 : coreProfileOrderCheck adaptiveRows2358 = true := by decide +kernel
theorem adaptivePermutation2358 : coreOrderPermutationCheck 2358 (coreProfileValues adaptiveRows2358) = true := by decide +kernel
end Erdos883Verified
