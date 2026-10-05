import Erdos883AdaptiveSpan48777WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness48777ChunkLength5 : adaptiveSpanWitness48777Chunk5.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness48777ChunkCheck5 : (adaptiveSpanWitness48777Chunk5.zipIdx 5120).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 24389 16258 24388 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel48777 w.s).1 (adaptiveSpanLevel48777 w.s).2) = true := by
  simp only [adaptiveSpanLevel48777]
  decide +kernel
end Erdos883Verified
