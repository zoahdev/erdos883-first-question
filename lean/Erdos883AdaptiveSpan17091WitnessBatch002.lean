import Erdos883AdaptiveSpan17091WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness17091ChunkLength2 : adaptiveSpanWitness17091Chunk2.length = 800 := by decide +kernel
theorem adaptiveSpanWitness17091ChunkCheck2 : (adaptiveSpanWitness17091Chunk2.zipIdx 2048).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 8546 5696 8545 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel17091 w.s).1 (adaptiveSpanLevel17091 w.s).2) = true := by
  simp only [adaptiveSpanLevel17091]
  decide +kernel
end Erdos883Verified
