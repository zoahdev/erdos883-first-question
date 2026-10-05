import Erdos883AdaptiveSpan18801WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness18801ChunkLength0 : adaptiveSpanWitness18801Chunk0.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness18801ChunkCheck0 : (adaptiveSpanWitness18801Chunk0.zipIdx 0).all (fun (w,i) => decide (w.s ≤ 7) && adaptiveSpanRankWitnessCheck 9401 6266 9400 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel18801 w.s).1 (adaptiveSpanLevel18801 w.s).2) = true := by
  simp only [adaptiveSpanLevel18801]
  decide +kernel
end Erdos883Verified
