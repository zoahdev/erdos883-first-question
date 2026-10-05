import Erdos883AdaptiveSpan126524WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness126524ChunkLength18 : adaptiveSpanWitness126524Chunk18.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness126524ChunkCheck18 : (adaptiveSpanWitness126524Chunk18.zipIdx 18432).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 63262 42174 63262 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel126524 w.s).1 (adaptiveSpanLevel126524 w.s).2) = true := by
  simp only [adaptiveSpanLevel126524]
  decide +kernel
end Erdos883Verified
