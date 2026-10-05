import Erdos883AdaptiveCertificate2604MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder2604 : coreProfileOrderCheck adaptiveRows2604 = true := by decide +kernel
theorem adaptivePermutation2604 : coreOrderPermutationCheck 2604 (coreProfileValues adaptiveRows2604) = true := by decide +kernel
theorem adaptiveMetadata2604 : coreProfileMetadataCheck adaptiveRows2604 = true := by
  simp only [adaptiveRows2604, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata2604Chunk0, adaptiveMetadata2604Chunk1, adaptiveMetadata2604Chunk2, adaptiveMetadata2604Chunk3, adaptiveMetadata2604Chunk4, adaptiveMetadata2604Chunk5, adaptiveMetadata2604Chunk6, adaptiveMetadata2604Chunk7, adaptiveMetadata2604Chunk8, adaptiveMetadata2604Chunk9, adaptiveMetadata2604Chunk10, Bool.true_and]
end Erdos883Verified
