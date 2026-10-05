import Erdos883AdaptiveSpan48777WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness48777ChunkLength4 : adaptiveSpanWitness48777Chunk4.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness48777ChunkCheck4 : (adaptiveSpanWitness48777Chunk4.zipIdx 4096).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 24389 16258 24388 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel48777 w.s).1 (adaptiveSpanLevel48777 w.s).2) = true := by
  simp only [adaptiveSpanLevel48777]
  decide +kernel
end Erdos883Verified
