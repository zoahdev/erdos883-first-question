import Erdos883AdaptiveCertificate5700MetadataBatch000
import Erdos883AdaptiveCertificate5700MetadataBatch001
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder5700 : coreProfileOrderCheck adaptiveRows5700 = true := by decide +kernel
theorem adaptivePermutation5700 : coreOrderPermutationCheck 5700 (coreProfileValues adaptiveRows5700) = true := by decide +kernel
theorem adaptiveMetadata5700 : coreProfileMetadataCheck adaptiveRows5700 = true := by
  simp only [adaptiveRows5700, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata5700Chunk0, adaptiveMetadata5700Chunk1, adaptiveMetadata5700Chunk2, adaptiveMetadata5700Chunk3, adaptiveMetadata5700Chunk4, adaptiveMetadata5700Chunk5, adaptiveMetadata5700Chunk6, adaptiveMetadata5700Chunk7, adaptiveMetadata5700Chunk8, adaptiveMetadata5700Chunk9, adaptiveMetadata5700Chunk10, adaptiveMetadata5700Chunk11, adaptiveMetadata5700Chunk12, adaptiveMetadata5700Chunk13, adaptiveMetadata5700Chunk14, adaptiveMetadata5700Chunk15, adaptiveMetadata5700Chunk16, adaptiveMetadata5700Chunk17, adaptiveMetadata5700Chunk18, adaptiveMetadata5700Chunk19, adaptiveMetadata5700Chunk20, adaptiveMetadata5700Chunk21, adaptiveMetadata5700Chunk22, Bool.true_and]
end Erdos883Verified
