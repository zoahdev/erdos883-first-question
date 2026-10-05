import Erdos883AdaptiveCertificate3670MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder3670 : coreProfileOrderCheck adaptiveRows3670 = true := by decide +kernel
theorem adaptivePermutation3670 : coreOrderPermutationCheck 3670 (coreProfileValues adaptiveRows3670) = true := by decide +kernel
theorem adaptiveMetadata3670 : coreProfileMetadataCheck adaptiveRows3670 = true := by
  simp only [adaptiveRows3670, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata3670Chunk0, adaptiveMetadata3670Chunk1, adaptiveMetadata3670Chunk2, adaptiveMetadata3670Chunk3, adaptiveMetadata3670Chunk4, adaptiveMetadata3670Chunk5, adaptiveMetadata3670Chunk6, adaptiveMetadata3670Chunk7, adaptiveMetadata3670Chunk8, adaptiveMetadata3670Chunk9, adaptiveMetadata3670Chunk10, adaptiveMetadata3670Chunk11, adaptiveMetadata3670Chunk12, adaptiveMetadata3670Chunk13, adaptiveMetadata3670Chunk14, Bool.true_and]
end Erdos883Verified
