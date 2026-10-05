import Erdos883AdaptiveCertificate1935MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1935 : coreProfileOrderCheck adaptiveRows1935 = true := by decide +kernel
theorem adaptivePermutation1935 : coreOrderPermutationCheck 1935 (coreProfileValues adaptiveRows1935) = true := by decide +kernel
theorem adaptiveMetadata1935 : coreProfileMetadataCheck adaptiveRows1935 = true := by
  simp only [adaptiveRows1935, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1935Chunk0, adaptiveMetadata1935Chunk1, adaptiveMetadata1935Chunk2, adaptiveMetadata1935Chunk3, adaptiveMetadata1935Chunk4, adaptiveMetadata1935Chunk5, adaptiveMetadata1935Chunk6, adaptiveMetadata1935Chunk7, Bool.true_and]
end Erdos883Verified
