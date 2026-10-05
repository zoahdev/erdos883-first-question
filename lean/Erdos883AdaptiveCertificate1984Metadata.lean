import Erdos883AdaptiveCertificate1984MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1984 : coreProfileOrderCheck adaptiveRows1984 = true := by decide +kernel
theorem adaptivePermutation1984 : coreOrderPermutationCheck 1984 (coreProfileValues adaptiveRows1984) = true := by decide +kernel
theorem adaptiveMetadata1984 : coreProfileMetadataCheck adaptiveRows1984 = true := by
  simp only [adaptiveRows1984, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1984Chunk0, adaptiveMetadata1984Chunk1, adaptiveMetadata1984Chunk2, adaptiveMetadata1984Chunk3, adaptiveMetadata1984Chunk4, adaptiveMetadata1984Chunk5, adaptiveMetadata1984Chunk6, adaptiveMetadata1984Chunk7, Bool.true_and]
end Erdos883Verified
