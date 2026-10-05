import Erdos883AdaptiveCertificate1751MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder1751 : coreProfileOrderCheck adaptiveRows1751 = true := by decide +kernel
theorem adaptivePermutation1751 : coreOrderPermutationCheck 1751 (coreProfileValues adaptiveRows1751) = true := by decide +kernel
theorem adaptiveMetadata1751 : coreProfileMetadataCheck adaptiveRows1751 = true := by
  simp only [adaptiveRows1751, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata1751Chunk0, adaptiveMetadata1751Chunk1, adaptiveMetadata1751Chunk2, adaptiveMetadata1751Chunk3, adaptiveMetadata1751Chunk4, adaptiveMetadata1751Chunk5, adaptiveMetadata1751Chunk6, Bool.true_and]
end Erdos883Verified
