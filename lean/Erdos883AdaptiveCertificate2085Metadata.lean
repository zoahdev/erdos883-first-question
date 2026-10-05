import Erdos883AdaptiveCertificate2085MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder2085 : coreProfileOrderCheck adaptiveRows2085 = true := by decide +kernel
theorem adaptivePermutation2085 : coreOrderPermutationCheck 2085 (coreProfileValues adaptiveRows2085) = true := by decide +kernel
theorem adaptiveMetadata2085 : coreProfileMetadataCheck adaptiveRows2085 = true := by
  simp only [adaptiveRows2085, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata2085Chunk0, adaptiveMetadata2085Chunk1, adaptiveMetadata2085Chunk2, adaptiveMetadata2085Chunk3, adaptiveMetadata2085Chunk4, adaptiveMetadata2085Chunk5, adaptiveMetadata2085Chunk6, adaptiveMetadata2085Chunk7, adaptiveMetadata2085Chunk8, Bool.true_and]
end Erdos883Verified
