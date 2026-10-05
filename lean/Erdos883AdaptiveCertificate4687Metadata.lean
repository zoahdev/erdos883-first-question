import Erdos883AdaptiveCertificate4687MetadataBatch000
import Erdos883AdaptiveCertificate4687MetadataBatch001
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder4687 : coreProfileOrderCheck adaptiveRows4687 = true := by decide +kernel
theorem adaptivePermutation4687 : coreOrderPermutationCheck 4687 (coreProfileValues adaptiveRows4687) = true := by decide +kernel
theorem adaptiveMetadata4687 : coreProfileMetadataCheck adaptiveRows4687 = true := by
  simp only [adaptiveRows4687, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata4687Chunk0, adaptiveMetadata4687Chunk1, adaptiveMetadata4687Chunk2, adaptiveMetadata4687Chunk3, adaptiveMetadata4687Chunk4, adaptiveMetadata4687Chunk5, adaptiveMetadata4687Chunk6, adaptiveMetadata4687Chunk7, adaptiveMetadata4687Chunk8, adaptiveMetadata4687Chunk9, adaptiveMetadata4687Chunk10, adaptiveMetadata4687Chunk11, adaptiveMetadata4687Chunk12, adaptiveMetadata4687Chunk13, adaptiveMetadata4687Chunk14, adaptiveMetadata4687Chunk15, adaptiveMetadata4687Chunk16, adaptiveMetadata4687Chunk17, adaptiveMetadata4687Chunk18, Bool.true_and]
end Erdos883Verified
