import Erdos883AdaptiveCertificate2300MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder2300 : coreProfileOrderCheck adaptiveRows2300 = true := by decide +kernel
theorem adaptivePermutation2300 : coreOrderPermutationCheck 2300 (coreProfileValues adaptiveRows2300) = true := by decide +kernel
theorem adaptiveMetadata2300 : coreProfileMetadataCheck adaptiveRows2300 = true := by
  simp only [adaptiveRows2300, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata2300Chunk0, adaptiveMetadata2300Chunk1, adaptiveMetadata2300Chunk2, adaptiveMetadata2300Chunk3, adaptiveMetadata2300Chunk4, adaptiveMetadata2300Chunk5, adaptiveMetadata2300Chunk6, adaptiveMetadata2300Chunk7, adaptiveMetadata2300Chunk8, Bool.true_and]
end Erdos883Verified
