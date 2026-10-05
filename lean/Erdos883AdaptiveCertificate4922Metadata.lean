import Erdos883AdaptiveCertificate4922MetadataBatch000
import Erdos883AdaptiveCertificate4922MetadataBatch001
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder4922 : coreProfileOrderCheck adaptiveRows4922 = true := by decide +kernel
theorem adaptivePermutation4922 : coreOrderPermutationCheck 4922 (coreProfileValues adaptiveRows4922) = true := by decide +kernel
theorem adaptiveMetadata4922 : coreProfileMetadataCheck adaptiveRows4922 = true := by
  simp only [adaptiveRows4922, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata4922Chunk0, adaptiveMetadata4922Chunk1, adaptiveMetadata4922Chunk2, adaptiveMetadata4922Chunk3, adaptiveMetadata4922Chunk4, adaptiveMetadata4922Chunk5, adaptiveMetadata4922Chunk6, adaptiveMetadata4922Chunk7, adaptiveMetadata4922Chunk8, adaptiveMetadata4922Chunk9, adaptiveMetadata4922Chunk10, adaptiveMetadata4922Chunk11, adaptiveMetadata4922Chunk12, adaptiveMetadata4922Chunk13, adaptiveMetadata4922Chunk14, adaptiveMetadata4922Chunk15, adaptiveMetadata4922Chunk16, adaptiveMetadata4922Chunk17, adaptiveMetadata4922Chunk18, adaptiveMetadata4922Chunk19, Bool.true_and]
end Erdos883Verified
