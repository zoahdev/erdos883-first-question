import Erdos883AdaptiveSpan40310WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness40310ChunkLength0 : adaptiveSpanWitness40310Chunk0.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness40310ChunkCheck0 : (adaptiveSpanWitness40310Chunk0.zipIdx 0).all (fun (w,i) => decide (w.s ≤ 9) && adaptiveSpanRankWitnessCheck 20155 13436 20155 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel40310 w.s).1 (adaptiveSpanLevel40310 w.s).2) = true := by
  simp only [adaptiveSpanLevel40310]
  decide +kernel
end Erdos883Verified
