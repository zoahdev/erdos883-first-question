import Erdos883AdaptiveCertificate1625MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1625 : coreProfileOrderCheck adaptiveRows1625 = true := by decide +kernel
theorem adaptivePermutation1625 : coreOrderPermutationCheck 1625 (coreProfileValues adaptiveRows1625) = true := by decide +kernel
theorem adaptiveMetadata1625 : coreProfileMetadataCheck adaptiveRows1625 = true := by
  simp only [adaptiveRows1625, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1625Chunk0, adaptiveMetadata1625Chunk1, adaptiveMetadata1625Chunk2, adaptiveMetadata1625Chunk3, adaptiveMetadata1625Chunk4, adaptiveMetadata1625Chunk5, adaptiveMetadata1625Chunk6, Bool.true_and]
end Erdos883Verified
