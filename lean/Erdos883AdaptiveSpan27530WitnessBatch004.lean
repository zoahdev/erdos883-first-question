import Erdos883AdaptiveSpan27530WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness27530ChunkLength4 : adaptiveSpanWitness27530Chunk4.length = 492 := by decide +kernel
theorem adaptiveSpanWitness27530ChunkCheck4 : (adaptiveSpanWitness27530Chunk4.zipIdx 4096).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 13765 9176 13765 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel27530 w.s).1 (adaptiveSpanLevel27530 w.s).2) = true := by
  simp only [adaptiveSpanLevel27530]
  decide +kernel
end Erdos883Verified
