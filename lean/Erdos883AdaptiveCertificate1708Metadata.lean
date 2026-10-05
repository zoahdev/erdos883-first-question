import Erdos883AdaptiveCertificate1708MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1708 : coreProfileOrderCheck adaptiveRows1708 = true := by decide +kernel
theorem adaptivePermutation1708 : coreOrderPermutationCheck 1708 (coreProfileValues adaptiveRows1708) = true := by decide +kernel
theorem adaptiveMetadata1708 : coreProfileMetadataCheck adaptiveRows1708 = true := by
  simp only [adaptiveRows1708, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1708Chunk0, adaptiveMetadata1708Chunk1, adaptiveMetadata1708Chunk2, adaptiveMetadata1708Chunk3, adaptiveMetadata1708Chunk4, adaptiveMetadata1708Chunk5, adaptiveMetadata1708Chunk6, Bool.true_and]
end Erdos883Verified
