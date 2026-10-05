import Erdos883AdaptiveSpan15537WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness15537ChunkLength2 : adaptiveSpanWitness15537Chunk2.length = 541 := by decide +kernel
theorem adaptiveSpanWitness15537ChunkCheck2 : (adaptiveSpanWitness15537Chunk2.zipIdx 2048).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 7769 5178 7768 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel15537 w.s).1 (adaptiveSpanLevel15537 w.s).2) = true := by
  simp only [adaptiveSpanLevel15537]
  decide +kernel
end Erdos883Verified
