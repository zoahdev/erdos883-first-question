import Erdos883AdaptiveCertificate2034MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder2034 : coreProfileOrderCheck adaptiveRows2034 = true := by decide +kernel
theorem adaptivePermutation2034 : coreOrderPermutationCheck 2034 (coreProfileValues adaptiveRows2034) = true := by decide +kernel
theorem adaptiveMetadata2034 : coreProfileMetadataCheck adaptiveRows2034 = true := by
  simp only [adaptiveRows2034, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata2034Chunk0, adaptiveMetadata2034Chunk1, adaptiveMetadata2034Chunk2, adaptiveMetadata2034Chunk3, adaptiveMetadata2034Chunk4, adaptiveMetadata2034Chunk5, adaptiveMetadata2034Chunk6, adaptiveMetadata2034Chunk7, Bool.true_and]
end Erdos883Verified
