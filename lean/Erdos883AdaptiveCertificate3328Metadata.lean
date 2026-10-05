import Erdos883AdaptiveCertificate3328MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder3328 : coreProfileOrderCheck adaptiveRows3328 = true := by decide +kernel
theorem adaptivePermutation3328 : coreOrderPermutationCheck 3328 (coreProfileValues adaptiveRows3328) = true := by decide +kernel
theorem adaptiveMetadata3328 : coreProfileMetadataCheck adaptiveRows3328 = true := by
  simp only [adaptiveRows3328, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata3328Chunk0, adaptiveMetadata3328Chunk1, adaptiveMetadata3328Chunk2, adaptiveMetadata3328Chunk3, adaptiveMetadata3328Chunk4, adaptiveMetadata3328Chunk5, adaptiveMetadata3328Chunk6, adaptiveMetadata3328Chunk7, adaptiveMetadata3328Chunk8, adaptiveMetadata3328Chunk9, adaptiveMetadata3328Chunk10, adaptiveMetadata3328Chunk11, adaptiveMetadata3328Chunk12, Bool.true_and]
end Erdos883Verified
