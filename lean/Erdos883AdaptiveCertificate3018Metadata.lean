import Erdos883AdaptiveCertificate3018MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder3018 : coreProfileOrderCheck adaptiveRows3018 = true := by decide +kernel
theorem adaptivePermutation3018 : coreOrderPermutationCheck 3018 (coreProfileValues adaptiveRows3018) = true := by decide +kernel
theorem adaptiveMetadata3018 : coreProfileMetadataCheck adaptiveRows3018 = true := by
  simp only [adaptiveRows3018, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata3018Chunk0, adaptiveMetadata3018Chunk1, adaptiveMetadata3018Chunk2, adaptiveMetadata3018Chunk3, adaptiveMetadata3018Chunk4, adaptiveMetadata3018Chunk5, adaptiveMetadata3018Chunk6, adaptiveMetadata3018Chunk7, adaptiveMetadata3018Chunk8, adaptiveMetadata3018Chunk9, adaptiveMetadata3018Chunk10, adaptiveMetadata3018Chunk11, Bool.true_and]
end Erdos883Verified
