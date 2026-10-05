import Erdos883AdaptiveCertificate1508MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1508 : coreProfileOrderCheck adaptiveRows1508 = true := by decide +kernel
theorem adaptivePermutation1508 : coreOrderPermutationCheck 1508 (coreProfileValues adaptiveRows1508) = true := by decide +kernel
theorem adaptiveMetadata1508 : coreProfileMetadataCheck adaptiveRows1508 = true := by
  simp only [adaptiveRows1508, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1508Chunk0, adaptiveMetadata1508Chunk1, adaptiveMetadata1508Chunk2, adaptiveMetadata1508Chunk3, adaptiveMetadata1508Chunk4, adaptiveMetadata1508Chunk5, Bool.true_and]
end Erdos883Verified
