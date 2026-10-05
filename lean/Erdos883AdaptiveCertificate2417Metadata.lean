import Erdos883AdaptiveCertificate2417Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveMetadata2417 : coreProfileMetadataCheck adaptiveRows2417 = true := by decide +kernel
theorem adaptiveOrder2417 : coreProfileOrderCheck adaptiveRows2417 = true := by decide +kernel
theorem adaptivePermutation2417 : coreOrderPermutationCheck 2417 (coreProfileValues adaptiveRows2417) = true := by decide +kernel
end Erdos883Verified
