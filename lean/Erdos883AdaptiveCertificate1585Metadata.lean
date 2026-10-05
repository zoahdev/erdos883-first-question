import Erdos883AdaptiveCertificate1585MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1585 : coreProfileOrderCheck adaptiveRows1585 = true := by decide +kernel
theorem adaptivePermutation1585 : coreOrderPermutationCheck 1585 (coreProfileValues adaptiveRows1585) = true := by decide +kernel
theorem adaptiveMetadata1585 : coreProfileMetadataCheck adaptiveRows1585 = true := by
  simp only [adaptiveRows1585, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1585Chunk0, adaptiveMetadata1585Chunk1, adaptiveMetadata1585Chunk2, adaptiveMetadata1585Chunk3, adaptiveMetadata1585Chunk4, adaptiveMetadata1585Chunk5, adaptiveMetadata1585Chunk6, Bool.true_and]
end Erdos883Verified
