import Erdos883AdaptiveSpan18801WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness18801ChunkLength3 : adaptiveSpanWitness18801Chunk3.length = 61 := by decide +kernel
theorem adaptiveSpanWitness18801ChunkCheck3 : (adaptiveSpanWitness18801Chunk3.zipIdx 3072).all (fun (w,i) => decide (w.s ≤ 7) && adaptiveSpanRankWitnessCheck 9401 6266 9400 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel18801 w.s).1 (adaptiveSpanLevel18801 w.s).2) = true := by
  simp only [adaptiveSpanLevel18801]
  decide +kernel
end Erdos883Verified
