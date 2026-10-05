import Erdos883AdaptiveSpan30284WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness30284ChunkLength2 : adaptiveSpanWitness30284Chunk2.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness30284ChunkCheck2 : (adaptiveSpanWitness30284Chunk2.zipIdx 2048).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 15142 10094 15142 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel30284 w.s).1 (adaptiveSpanLevel30284 w.s).2) = true := by
  simp only [adaptiveSpanLevel30284]
  decide +kernel
end Erdos883Verified
