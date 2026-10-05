import Erdos883AdaptiveCertificate2874MetadataBatch000
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveOrder2874 : coreProfileOrderCheck adaptiveRows2874 = true := by decide +kernel
theorem adaptivePermutation2874 : coreOrderPermutationCheck 2874 (coreProfileValues adaptiveRows2874) = true := by decide +kernel
theorem adaptiveMetadata2874 : coreProfileMetadataCheck adaptiveRows2874 = true := by
  simp only [adaptiveRows2874, coreProfileMetadataCheck_flatten, List.all_cons, List.all_nil,
    adaptiveMetadata2874Chunk0, adaptiveMetadata2874Chunk1, adaptiveMetadata2874Chunk2, adaptiveMetadata2874Chunk3, adaptiveMetadata2874Chunk4, adaptiveMetadata2874Chunk5, adaptiveMetadata2874Chunk6, adaptiveMetadata2874Chunk7, adaptiveMetadata2874Chunk8, adaptiveMetadata2874Chunk9, adaptiveMetadata2874Chunk10, adaptiveMetadata2874Chunk11, Bool.true_and]
end Erdos883Verified
