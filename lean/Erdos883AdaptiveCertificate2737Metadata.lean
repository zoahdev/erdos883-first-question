import Erdos883AdaptiveCertificate2737MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder2737 : coreProfileOrderCheck adaptiveRows2737 = true := by decide +kernel
theorem adaptivePermutation2737 : coreOrderPermutationCheck 2737 (coreProfileValues adaptiveRows2737) = true := by decide +kernel
theorem adaptiveMetadata2737 : coreProfileMetadataCheck adaptiveRows2737 = true := by
  simp only [adaptiveRows2737, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata2737Chunk0, adaptiveMetadata2737Chunk1, adaptiveMetadata2737Chunk2, adaptiveMetadata2737Chunk3, adaptiveMetadata2737Chunk4, adaptiveMetadata2737Chunk5, adaptiveMetadata2737Chunk6, adaptiveMetadata2737Chunk7, adaptiveMetadata2737Chunk8, adaptiveMetadata2737Chunk9, adaptiveMetadata2737Chunk10, Bool.true_and]
end Erdos883Verified
