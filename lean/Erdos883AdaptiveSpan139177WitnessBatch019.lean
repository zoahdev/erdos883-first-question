import Erdos883AdaptiveSpan139177WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness139177ChunkLength19 : adaptiveSpanWitness139177Chunk19.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness139177ChunkCheck19 : (adaptiveSpanWitness139177Chunk19.zipIdx 19456).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 69589 46392 69589 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel139177 w.s).1 (adaptiveSpanLevel139177 w.s).2) = true := by
  simp only [adaptiveSpanLevel139177]
  decide +kernel
end Erdos883Verified
