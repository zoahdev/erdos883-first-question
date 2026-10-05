import Erdos883AdaptiveSpan20682WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness20682ChunkLength3 : adaptiveSpanWitness20682Chunk3.length = 375 := by decide +kernel
theorem adaptiveSpanWitness20682ChunkCheck3 : (adaptiveSpanWitness20682Chunk3.zipIdx 3072).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 10341 6893 10341 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel20682 w.s).1 (adaptiveSpanLevel20682 w.s).2) = true := by
  simp only [adaptiveSpanLevel20682]
  decide +kernel
end Erdos883Verified
