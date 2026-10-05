import Erdos883AdaptiveSpan153095WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness153095ChunkLength9 : adaptiveSpanWitness153095Chunk9.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness153095ChunkCheck9 : (adaptiveSpanWitness153095Chunk9.zipIdx 9216).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 76548 51031 76547 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel153095 w.s).1 (adaptiveSpanLevel153095 w.s).2) = true := by
  simp only [adaptiveSpanLevel153095]
  decide +kernel
end Erdos883Verified
