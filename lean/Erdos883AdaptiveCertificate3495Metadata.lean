import Erdos883AdaptiveCertificate3495MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder3495 : coreProfileOrderCheck adaptiveRows3495 = true := by decide +kernel
theorem adaptivePermutation3495 : coreOrderPermutationCheck 3495 (coreProfileValues adaptiveRows3495) = true := by decide +kernel
theorem adaptiveMetadata3495 : coreProfileMetadataCheck adaptiveRows3495 = true := by
  simp only [adaptiveRows3495, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata3495Chunk0, adaptiveMetadata3495Chunk1, adaptiveMetadata3495Chunk2, adaptiveMetadata3495Chunk3, adaptiveMetadata3495Chunk4, adaptiveMetadata3495Chunk5, adaptiveMetadata3495Chunk6, adaptiveMetadata3495Chunk7, adaptiveMetadata3495Chunk8, adaptiveMetadata3495Chunk9, adaptiveMetadata3495Chunk10, adaptiveMetadata3495Chunk11, adaptiveMetadata3495Chunk12, adaptiveMetadata3495Chunk13, Bool.true_and]
end Erdos883Verified
