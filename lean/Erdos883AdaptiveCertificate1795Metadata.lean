import Erdos883AdaptiveCertificate1795MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1795 : coreProfileOrderCheck adaptiveRows1795 = true := by decide +kernel
theorem adaptivePermutation1795 : coreOrderPermutationCheck 1795 (coreProfileValues adaptiveRows1795) = true := by decide +kernel
theorem adaptiveMetadata1795 : coreProfileMetadataCheck adaptiveRows1795 = true := by
  simp only [adaptiveRows1795, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1795Chunk0, adaptiveMetadata1795Chunk1, adaptiveMetadata1795Chunk2, adaptiveMetadata1795Chunk3, adaptiveMetadata1795Chunk4, adaptiveMetadata1795Chunk5, adaptiveMetadata1795Chunk6, adaptiveMetadata1795Chunk7, Bool.true_and]
end Erdos883Verified
