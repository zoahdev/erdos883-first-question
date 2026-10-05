import Erdos883AdaptiveSpan139177WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness139177ChunkLength8 : adaptiveSpanWitness139177Chunk8.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness139177ChunkCheck8 : (adaptiveSpanWitness139177Chunk8.zipIdx 8192).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 69589 46392 69589 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel139177 w.s).1 (adaptiveSpanLevel139177 w.s).2) = true := by
  simp only [adaptiveSpanLevel139177]
  decide +kernel
end Erdos883Verified
