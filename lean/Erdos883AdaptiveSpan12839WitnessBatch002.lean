import Erdos883AdaptiveSpan12839WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness12839ChunkLength2 : adaptiveSpanWitness12839Chunk2.length = 91 := by decide +kernel
theorem adaptiveSpanWitness12839ChunkCheck2 : (adaptiveSpanWitness12839Chunk2.zipIdx 2048).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 6420 4279 6419 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel12839 w.s).1 (adaptiveSpanLevel12839 w.s).2) = true := by
  simp only [adaptiveSpanLevel12839]
  decide +kernel
end Erdos883Verified
