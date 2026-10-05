import Erdos883AdaptiveCertificate1435MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1435 : coreProfileOrderCheck adaptiveRows1435 = true := by decide +kernel
theorem adaptivePermutation1435 : coreOrderPermutationCheck 1435 (coreProfileValues adaptiveRows1435) = true := by decide +kernel
theorem adaptiveMetadata1435 : coreProfileMetadataCheck adaptiveRows1435 = true := by
  simp only [adaptiveRows1435, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1435Chunk0, adaptiveMetadata1435Chunk1, adaptiveMetadata1435Chunk2, adaptiveMetadata1435Chunk3, adaptiveMetadata1435Chunk4, adaptiveMetadata1435Chunk5, Bool.true_and]
end Erdos883Verified
