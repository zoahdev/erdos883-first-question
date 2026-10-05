import Erdos883AdaptiveCertificate2244MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder2244 : coreProfileOrderCheck adaptiveRows2244 = true := by decide +kernel
theorem adaptivePermutation2244 : coreOrderPermutationCheck 2244 (coreProfileValues adaptiveRows2244) = true := by decide +kernel
theorem adaptiveMetadata2244 : coreProfileMetadataCheck adaptiveRows2244 = true := by
  simp only [adaptiveRows2244, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata2244Chunk0, adaptiveMetadata2244Chunk1, adaptiveMetadata2244Chunk2, adaptiveMetadata2244Chunk3, adaptiveMetadata2244Chunk4, adaptiveMetadata2244Chunk5, adaptiveMetadata2244Chunk6, adaptiveMetadata2244Chunk7, adaptiveMetadata2244Chunk8, Bool.true_and]
end Erdos883Verified
