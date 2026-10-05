import Erdos883AdaptiveSpan27530WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness27530ChunkLength0 : adaptiveSpanWitness27530Chunk0.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness27530ChunkCheck0 : (adaptiveSpanWitness27530Chunk0.zipIdx 0).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 13765 9176 13765 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel27530 w.s).1 (adaptiveSpanLevel27530 w.s).2) = true := by
  simp only [adaptiveSpanLevel27530]
  decide +kernel
end Erdos883Verified
