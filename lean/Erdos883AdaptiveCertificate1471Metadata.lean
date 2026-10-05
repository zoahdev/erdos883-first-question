import Erdos883AdaptiveCertificate1471MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1471 : coreProfileOrderCheck adaptiveRows1471 = true := by decide +kernel
theorem adaptivePermutation1471 : coreOrderPermutationCheck 1471 (coreProfileValues adaptiveRows1471) = true := by decide +kernel
theorem adaptiveMetadata1471 : coreProfileMetadataCheck adaptiveRows1471 = true := by
  simp only [adaptiveRows1471, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1471Chunk0, adaptiveMetadata1471Chunk1, adaptiveMetadata1471Chunk2, adaptiveMetadata1471Chunk3, adaptiveMetadata1471Chunk4, adaptiveMetadata1471Chunk5, Bool.true_and]
end Erdos883Verified
