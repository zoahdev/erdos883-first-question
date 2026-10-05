import Erdos883AdaptiveCertificate5169MetadataBatch000
import Erdos883AdaptiveCertificate5169MetadataBatch001
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder5169 : coreProfileOrderCheck adaptiveRows5169 = true := by decide +kernel
theorem adaptivePermutation5169 : coreOrderPermutationCheck 5169 (coreProfileValues adaptiveRows5169) = true := by decide +kernel
theorem adaptiveMetadata5169 : coreProfileMetadataCheck adaptiveRows5169 = true := by
  simp only [adaptiveRows5169, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata5169Chunk0, adaptiveMetadata5169Chunk1, adaptiveMetadata5169Chunk2, adaptiveMetadata5169Chunk3, adaptiveMetadata5169Chunk4, adaptiveMetadata5169Chunk5, adaptiveMetadata5169Chunk6, adaptiveMetadata5169Chunk7, adaptiveMetadata5169Chunk8, adaptiveMetadata5169Chunk9, adaptiveMetadata5169Chunk10, adaptiveMetadata5169Chunk11, adaptiveMetadata5169Chunk12, adaptiveMetadata5169Chunk13, adaptiveMetadata5169Chunk14, adaptiveMetadata5169Chunk15, adaptiveMetadata5169Chunk16, adaptiveMetadata5169Chunk17, adaptiveMetadata5169Chunk18, adaptiveMetadata5169Chunk19, adaptiveMetadata5169Chunk20, Bool.true_and]
end Erdos883Verified
