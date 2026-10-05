import Erdos883AdaptiveCertificate5986MetadataBatch000
import Erdos883AdaptiveCertificate5986MetadataBatch001
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder5986 : coreProfileOrderCheck adaptiveRows5986 = true := by decide +kernel
theorem adaptivePermutation5986 : coreOrderPermutationCheck 5986 (coreProfileValues adaptiveRows5986) = true := by decide +kernel
theorem adaptiveMetadata5986 : coreProfileMetadataCheck adaptiveRows5986 = true := by
  simp only [adaptiveRows5986, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata5986Chunk0, adaptiveMetadata5986Chunk1, adaptiveMetadata5986Chunk2, adaptiveMetadata5986Chunk3, adaptiveMetadata5986Chunk4, adaptiveMetadata5986Chunk5, adaptiveMetadata5986Chunk6, adaptiveMetadata5986Chunk7, adaptiveMetadata5986Chunk8, adaptiveMetadata5986Chunk9, adaptiveMetadata5986Chunk10, adaptiveMetadata5986Chunk11, adaptiveMetadata5986Chunk12, adaptiveMetadata5986Chunk13, adaptiveMetadata5986Chunk14, adaptiveMetadata5986Chunk15, adaptiveMetadata5986Chunk16, adaptiveMetadata5986Chunk17, adaptiveMetadata5986Chunk18, adaptiveMetadata5986Chunk19, adaptiveMetadata5986Chunk20, adaptiveMetadata5986Chunk21, adaptiveMetadata5986Chunk22, adaptiveMetadata5986Chunk23, Bool.true_and]
end Erdos883Verified
