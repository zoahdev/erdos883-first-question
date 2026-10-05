import Erdos883AdaptiveSpan126524WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness126524ChunkLength0 : adaptiveSpanWitness126524Chunk0.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness126524ChunkCheck0 : (adaptiveSpanWitness126524Chunk0.zipIdx 0).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 63262 42174 63262 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel126524 w.s).1 (adaptiveSpanLevel126524 w.s).2) = true := by
  simp only [adaptiveSpanLevel126524]
  decide +kernel
end Erdos883Verified
