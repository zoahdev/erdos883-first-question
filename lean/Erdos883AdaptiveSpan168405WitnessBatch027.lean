import Erdos883AdaptiveSpan168405WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness168405ChunkLength27 : adaptiveSpanWitness168405Chunk27.length = 419 := by decide +kernel
theorem adaptiveSpanWitness168405ChunkCheck27 : (adaptiveSpanWitness168405Chunk27.zipIdx 27648).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 84203 56134 84202 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel168405 w.s).1 (adaptiveSpanLevel168405 w.s).2) = true := by
  simp only [adaptiveSpanLevel168405]
  decide +kernel
end Erdos883Verified
