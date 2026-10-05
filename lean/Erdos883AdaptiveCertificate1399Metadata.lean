import Erdos883AdaptiveCertificate1399MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1399 : coreProfileOrderCheck adaptiveRows1399 = true := by decide +kernel
theorem adaptivePermutation1399 : coreOrderPermutationCheck 1399 (coreProfileValues adaptiveRows1399) = true := by decide +kernel
theorem adaptiveMetadata1399 : coreProfileMetadataCheck adaptiveRows1399 = true := by
  simp only [adaptiveRows1399, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1399Chunk0, adaptiveMetadata1399Chunk1, adaptiveMetadata1399Chunk2, adaptiveMetadata1399Chunk3, adaptiveMetadata1399Chunk4, adaptiveMetadata1399Chunk5, Bool.true_and]
end Erdos883Verified
