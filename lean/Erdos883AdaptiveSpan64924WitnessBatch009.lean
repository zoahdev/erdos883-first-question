import Erdos883AdaptiveSpan64924WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness64924ChunkLength9 : adaptiveSpanWitness64924Chunk9.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness64924ChunkCheck9 : (adaptiveSpanWitness64924Chunk9.zipIdx 9216).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 32462 21640 32461 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel64924 w.s).1 (adaptiveSpanLevel64924 w.s).2) = true := by
  simp only [adaptiveSpanLevel64924]
  decide +kernel
end Erdos883Verified
