import Erdos883AdaptiveSpan86416WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness86416ChunkLength6 : adaptiveSpanWitness86416Chunk6.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness86416ChunkCheck6 : (adaptiveSpanWitness86416Chunk6.zipIdx 6144).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 43208 28804 43207 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel86416 w.s).1 (adaptiveSpanLevel86416 w.s).2) = true := by
  simp only [adaptiveSpanLevel86416]
  decide +kernel
end Erdos883Verified
