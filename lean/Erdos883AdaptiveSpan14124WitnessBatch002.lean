import Erdos883AdaptiveSpan14124WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness14124ChunkLength2 : adaptiveSpanWitness14124Chunk2.length = 306 := by decide +kernel
theorem adaptiveSpanWitness14124ChunkCheck2 : (adaptiveSpanWitness14124Chunk2.zipIdx 2048).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 7062 4707 7062 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel14124 w.s).1 (adaptiveSpanLevel14124 w.s).2) = true := by
  simp only [adaptiveSpanLevel14124]
  decide +kernel
end Erdos883Verified
