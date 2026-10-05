import Erdos883AdaptiveCertificate3169MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder3169 : coreProfileOrderCheck adaptiveRows3169 = true := by decide +kernel
theorem adaptivePermutation3169 : coreOrderPermutationCheck 3169 (coreProfileValues adaptiveRows3169) = true := by decide +kernel
theorem adaptiveMetadata3169 : coreProfileMetadataCheck adaptiveRows3169 = true := by
  simp only [adaptiveRows3169, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata3169Chunk0, adaptiveMetadata3169Chunk1, adaptiveMetadata3169Chunk2, adaptiveMetadata3169Chunk3, adaptiveMetadata3169Chunk4, adaptiveMetadata3169Chunk5, adaptiveMetadata3169Chunk6, adaptiveMetadata3169Chunk7, adaptiveMetadata3169Chunk8, adaptiveMetadata3169Chunk9, adaptiveMetadata3169Chunk10, adaptiveMetadata3169Chunk11, adaptiveMetadata3169Chunk12, Bool.true_and]
end Erdos883Verified
