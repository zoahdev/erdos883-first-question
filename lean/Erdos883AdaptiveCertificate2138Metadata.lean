import Erdos883AdaptiveCertificate2138MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder2138 : coreProfileOrderCheck adaptiveRows2138 = true := by decide +kernel
theorem adaptivePermutation2138 : coreOrderPermutationCheck 2138 (coreProfileValues adaptiveRows2138) = true := by decide +kernel
theorem adaptiveMetadata2138 : coreProfileMetadataCheck adaptiveRows2138 = true := by
  simp only [adaptiveRows2138, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata2138Chunk0, adaptiveMetadata2138Chunk1, adaptiveMetadata2138Chunk2, adaptiveMetadata2138Chunk3, adaptiveMetadata2138Chunk4, adaptiveMetadata2138Chunk5, adaptiveMetadata2138Chunk6, adaptiveMetadata2138Chunk7, adaptiveMetadata2138Chunk8, Bool.true_and]
end Erdos883Verified
