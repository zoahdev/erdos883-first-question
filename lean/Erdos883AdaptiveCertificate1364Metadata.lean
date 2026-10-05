import Erdos883AdaptiveCertificate1364MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1364 : coreProfileOrderCheck adaptiveRows1364 = true := by decide +kernel
theorem adaptivePermutation1364 : coreOrderPermutationCheck 1364 (coreProfileValues adaptiveRows1364) = true := by decide +kernel
theorem adaptiveMetadata1364 : coreProfileMetadataCheck adaptiveRows1364 = true := by
  simp only [adaptiveRows1364, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1364Chunk0, adaptiveMetadata1364Chunk1, adaptiveMetadata1364Chunk2, adaptiveMetadata1364Chunk3, adaptiveMetadata1364Chunk4, adaptiveMetadata1364Chunk5, Bool.true_and]
end Erdos883Verified
