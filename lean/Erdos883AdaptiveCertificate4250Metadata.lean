import Erdos883AdaptiveCertificate4250MetadataBatch000
import Erdos883AdaptiveCertificate4250MetadataBatch001
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder4250 : coreProfileOrderCheck adaptiveRows4250 = true := by decide +kernel
theorem adaptivePermutation4250 : coreOrderPermutationCheck 4250 (coreProfileValues adaptiveRows4250) = true := by decide +kernel
theorem adaptiveMetadata4250 : coreProfileMetadataCheck adaptiveRows4250 = true := by
  simp only [adaptiveRows4250, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata4250Chunk0, adaptiveMetadata4250Chunk1, adaptiveMetadata4250Chunk2, adaptiveMetadata4250Chunk3, adaptiveMetadata4250Chunk4, adaptiveMetadata4250Chunk5, adaptiveMetadata4250Chunk6, adaptiveMetadata4250Chunk7, adaptiveMetadata4250Chunk8, adaptiveMetadata4250Chunk9, adaptiveMetadata4250Chunk10, adaptiveMetadata4250Chunk11, adaptiveMetadata4250Chunk12, adaptiveMetadata4250Chunk13, adaptiveMetadata4250Chunk14, adaptiveMetadata4250Chunk15, adaptiveMetadata4250Chunk16, Bool.true_and]
end Erdos883Verified
