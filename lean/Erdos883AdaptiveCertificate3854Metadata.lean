import Erdos883AdaptiveCertificate3854MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder3854 : coreProfileOrderCheck adaptiveRows3854 = true := by decide +kernel
theorem adaptivePermutation3854 : coreOrderPermutationCheck 3854 (coreProfileValues adaptiveRows3854) = true := by decide +kernel
theorem adaptiveMetadata3854 : coreProfileMetadataCheck adaptiveRows3854 = true := by
  simp only [adaptiveRows3854, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata3854Chunk0, adaptiveMetadata3854Chunk1, adaptiveMetadata3854Chunk2, adaptiveMetadata3854Chunk3, adaptiveMetadata3854Chunk4, adaptiveMetadata3854Chunk5, adaptiveMetadata3854Chunk6, adaptiveMetadata3854Chunk7, adaptiveMetadata3854Chunk8, adaptiveMetadata3854Chunk9, adaptiveMetadata3854Chunk10, adaptiveMetadata3854Chunk11, adaptiveMetadata3854Chunk12, adaptiveMetadata3854Chunk13, adaptiveMetadata3854Chunk14, adaptiveMetadata3854Chunk15, Bool.true_and]
end Erdos883Verified
