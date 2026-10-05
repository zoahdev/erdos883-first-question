import Erdos883AdaptiveSpan168405WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness168405ChunkLength2 : adaptiveSpanWitness168405Chunk2.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness168405ChunkCheck2 : (adaptiveSpanWitness168405Chunk2.zipIdx 2048).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 84203 56134 84202 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel168405 w.s).1 (adaptiveSpanLevel168405 w.s).2) = true := by
  simp only [adaptiveSpanLevel168405]
  decide +kernel
end Erdos883Verified
