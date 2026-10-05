import Erdos883AdaptiveCertificate1666MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1666 : coreProfileOrderCheck adaptiveRows1666 = true := by decide +kernel
theorem adaptivePermutation1666 : coreOrderPermutationCheck 1666 (coreProfileValues adaptiveRows1666) = true := by decide +kernel
theorem adaptiveMetadata1666 : coreProfileMetadataCheck adaptiveRows1666 = true := by
  simp only [adaptiveRows1666, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1666Chunk0, adaptiveMetadata1666Chunk1, adaptiveMetadata1666Chunk2, adaptiveMetadata1666Chunk3, adaptiveMetadata1666Chunk4, adaptiveMetadata1666Chunk5, adaptiveMetadata1666Chunk6, Bool.true_and]
end Erdos883Verified
