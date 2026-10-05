import Erdos883AdaptiveCertificate2192MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder2192 : coreProfileOrderCheck adaptiveRows2192 = true := by decide +kernel
theorem adaptivePermutation2192 : coreOrderPermutationCheck 2192 (coreProfileValues adaptiveRows2192) = true := by decide +kernel
theorem adaptiveMetadata2192 : coreProfileMetadataCheck adaptiveRows2192 = true := by
  simp only [adaptiveRows2192, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata2192Chunk0, adaptiveMetadata2192Chunk1, adaptiveMetadata2192Chunk2, adaptiveMetadata2192Chunk3, adaptiveMetadata2192Chunk4, adaptiveMetadata2192Chunk5, adaptiveMetadata2192Chunk6, adaptiveMetadata2192Chunk7, adaptiveMetadata2192Chunk8, Bool.true_and]
end Erdos883Verified
