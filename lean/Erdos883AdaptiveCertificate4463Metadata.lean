import Erdos883AdaptiveCertificate4463MetadataBatch000
import Erdos883AdaptiveCertificate4463MetadataBatch001
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder4463 : coreProfileOrderCheck adaptiveRows4463 = true := by decide +kernel
theorem adaptivePermutation4463 : coreOrderPermutationCheck 4463 (coreProfileValues adaptiveRows4463) = true := by decide +kernel
theorem adaptiveMetadata4463 : coreProfileMetadataCheck adaptiveRows4463 = true := by
  simp only [adaptiveRows4463, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata4463Chunk0, adaptiveMetadata4463Chunk1, adaptiveMetadata4463Chunk2, adaptiveMetadata4463Chunk3, adaptiveMetadata4463Chunk4, adaptiveMetadata4463Chunk5, adaptiveMetadata4463Chunk6, adaptiveMetadata4463Chunk7, adaptiveMetadata4463Chunk8, adaptiveMetadata4463Chunk9, adaptiveMetadata4463Chunk10, adaptiveMetadata4463Chunk11, adaptiveMetadata4463Chunk12, adaptiveMetadata4463Chunk13, adaptiveMetadata4463Chunk14, adaptiveMetadata4463Chunk15, adaptiveMetadata4463Chunk16, adaptiveMetadata4463Chunk17, Bool.true_and]
end Erdos883Verified
