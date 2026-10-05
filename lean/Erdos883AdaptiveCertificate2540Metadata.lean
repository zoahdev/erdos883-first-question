import Erdos883AdaptiveCertificate2540MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder2540 : coreProfileOrderCheck adaptiveRows2540 = true := by decide +kernel
theorem adaptivePermutation2540 : coreOrderPermutationCheck 2540 (coreProfileValues adaptiveRows2540) = true := by decide +kernel
theorem adaptiveMetadata2540 : coreProfileMetadataCheck adaptiveRows2540 = true := by
  simp only [adaptiveRows2540, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata2540Chunk0, adaptiveMetadata2540Chunk1, adaptiveMetadata2540Chunk2, adaptiveMetadata2540Chunk3, adaptiveMetadata2540Chunk4, adaptiveMetadata2540Chunk5, adaptiveMetadata2540Chunk6, adaptiveMetadata2540Chunk7, adaptiveMetadata2540Chunk8, adaptiveMetadata2540Chunk9, Bool.true_and]
end Erdos883Verified
