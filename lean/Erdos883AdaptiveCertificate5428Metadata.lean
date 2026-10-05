import Erdos883AdaptiveCertificate5428MetadataBatch000
import Erdos883AdaptiveCertificate5428MetadataBatch001
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder5428 : coreProfileOrderCheck adaptiveRows5428 = true := by decide +kernel
theorem adaptivePermutation5428 : coreOrderPermutationCheck 5428 (coreProfileValues adaptiveRows5428) = true := by decide +kernel
theorem adaptiveMetadata5428 : coreProfileMetadataCheck adaptiveRows5428 = true := by
  simp only [adaptiveRows5428, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata5428Chunk0, adaptiveMetadata5428Chunk1, adaptiveMetadata5428Chunk2, adaptiveMetadata5428Chunk3, adaptiveMetadata5428Chunk4, adaptiveMetadata5428Chunk5, adaptiveMetadata5428Chunk6, adaptiveMetadata5428Chunk7, adaptiveMetadata5428Chunk8, adaptiveMetadata5428Chunk9, adaptiveMetadata5428Chunk10, adaptiveMetadata5428Chunk11, adaptiveMetadata5428Chunk12, adaptiveMetadata5428Chunk13, adaptiveMetadata5428Chunk14, adaptiveMetadata5428Chunk15, adaptiveMetadata5428Chunk16, adaptiveMetadata5428Chunk17, adaptiveMetadata5428Chunk18, adaptiveMetadata5428Chunk19, adaptiveMetadata5428Chunk20, adaptiveMetadata5428Chunk21, Bool.true_and]
end Erdos883Verified
