import Erdos883AdaptiveCertificate2670MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder2670 : coreProfileOrderCheck adaptiveRows2670 = true := by decide +kernel
theorem adaptivePermutation2670 : coreOrderPermutationCheck 2670 (coreProfileValues adaptiveRows2670) = true := by decide +kernel
theorem adaptiveMetadata2670 : coreProfileMetadataCheck adaptiveRows2670 = true := by
  simp only [adaptiveRows2670, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata2670Chunk0, adaptiveMetadata2670Chunk1, adaptiveMetadata2670Chunk2, adaptiveMetadata2670Chunk3, adaptiveMetadata2670Chunk4, adaptiveMetadata2670Chunk5, adaptiveMetadata2670Chunk6, adaptiveMetadata2670Chunk7, adaptiveMetadata2670Chunk8, adaptiveMetadata2670Chunk9, adaptiveMetadata2670Chunk10, Bool.true_and]
end Erdos883Verified
