import Erdos883AdaptiveCertificate1887MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1887 : coreProfileOrderCheck adaptiveRows1887 = true := by decide +kernel
theorem adaptivePermutation1887 : coreOrderPermutationCheck 1887 (coreProfileValues adaptiveRows1887) = true := by decide +kernel
theorem adaptiveMetadata1887 : coreProfileMetadataCheck adaptiveRows1887 = true := by
  simp only [adaptiveRows1887, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1887Chunk0, adaptiveMetadata1887Chunk1, adaptiveMetadata1887Chunk2, adaptiveMetadata1887Chunk3, adaptiveMetadata1887Chunk4, adaptiveMetadata1887Chunk5, adaptiveMetadata1887Chunk6, adaptiveMetadata1887Chunk7, Bool.true_and]
end Erdos883Verified
