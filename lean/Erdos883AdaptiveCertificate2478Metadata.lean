import Erdos883AdaptiveCertificate2478MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder2478 : coreProfileOrderCheck adaptiveRows2478 = true := by decide +kernel
theorem adaptivePermutation2478 : coreOrderPermutationCheck 2478 (coreProfileValues adaptiveRows2478) = true := by decide +kernel
theorem adaptiveMetadata2478 : coreProfileMetadataCheck adaptiveRows2478 = true := by
  simp only [adaptiveRows2478, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata2478Chunk0, adaptiveMetadata2478Chunk1, adaptiveMetadata2478Chunk2, adaptiveMetadata2478Chunk3, adaptiveMetadata2478Chunk4, adaptiveMetadata2478Chunk5, adaptiveMetadata2478Chunk6, adaptiveMetadata2478Chunk7, adaptiveMetadata2478Chunk8, adaptiveMetadata2478Chunk9, Bool.true_and]
end Erdos883Verified
