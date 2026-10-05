import Erdos883AdaptiveCertificate1840MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1840 : coreProfileOrderCheck adaptiveRows1840 = true := by decide +kernel
theorem adaptivePermutation1840 : coreOrderPermutationCheck 1840 (coreProfileValues adaptiveRows1840) = true := by decide +kernel
theorem adaptiveMetadata1840 : coreProfileMetadataCheck adaptiveRows1840 = true := by
  simp only [adaptiveRows1840, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1840Chunk0, adaptiveMetadata1840Chunk1, adaptiveMetadata1840Chunk2, adaptiveMetadata1840Chunk3, adaptiveMetadata1840Chunk4, adaptiveMetadata1840Chunk5, adaptiveMetadata1840Chunk6, adaptiveMetadata1840Chunk7, Bool.true_and]
end Erdos883Verified
