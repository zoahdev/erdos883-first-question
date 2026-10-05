import Erdos883AdaptiveCertificate4047MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder4047 : coreProfileOrderCheck adaptiveRows4047 = true := by decide +kernel
theorem adaptivePermutation4047 : coreOrderPermutationCheck 4047 (coreProfileValues adaptiveRows4047) = true := by decide +kernel
theorem adaptiveMetadata4047 : coreProfileMetadataCheck adaptiveRows4047 = true := by
  simp only [adaptiveRows4047, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata4047Chunk0, adaptiveMetadata4047Chunk1, adaptiveMetadata4047Chunk2, adaptiveMetadata4047Chunk3, adaptiveMetadata4047Chunk4, adaptiveMetadata4047Chunk5, adaptiveMetadata4047Chunk6, adaptiveMetadata4047Chunk7, adaptiveMetadata4047Chunk8, adaptiveMetadata4047Chunk9, adaptiveMetadata4047Chunk10, adaptiveMetadata4047Chunk11, adaptiveMetadata4047Chunk12, adaptiveMetadata4047Chunk13, adaptiveMetadata4047Chunk14, adaptiveMetadata4047Chunk15, Bool.true_and]
end Erdos883Verified
