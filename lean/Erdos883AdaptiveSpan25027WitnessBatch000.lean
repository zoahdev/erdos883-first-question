import Erdos883AdaptiveSpan25027WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness25027ChunkLength0 : adaptiveSpanWitness25027Chunk0.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness25027ChunkCheck0 : (adaptiveSpanWitness25027Chunk0.zipIdx 0).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 12514 8342 12514 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel25027 w.s).1 (adaptiveSpanLevel25027 w.s).2) = true := by
  simp only [adaptiveSpanLevel25027]
  decide +kernel
end Erdos883Verified
