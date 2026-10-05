import Erdos883AdaptiveCertificate1546MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1546 : coreProfileOrderCheck adaptiveRows1546 = true := by decide +kernel
theorem adaptivePermutation1546 : coreOrderPermutationCheck 1546 (coreProfileValues adaptiveRows1546) = true := by decide +kernel
theorem adaptiveMetadata1546 : coreProfileMetadataCheck adaptiveRows1546 = true := by
  simp only [adaptiveRows1546, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1546Chunk0, adaptiveMetadata1546Chunk1, adaptiveMetadata1546Chunk2, adaptiveMetadata1546Chunk3, adaptiveMetadata1546Chunk4, adaptiveMetadata1546Chunk5, adaptiveMetadata1546Chunk6, Bool.true_and]
end Erdos883Verified
