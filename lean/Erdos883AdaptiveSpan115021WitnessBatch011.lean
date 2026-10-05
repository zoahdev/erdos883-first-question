import Erdos883AdaptiveSpan115021WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness115021ChunkLength11 : adaptiveSpanWitness115021Chunk11.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness115021ChunkCheck11 : (adaptiveSpanWitness115021Chunk11.zipIdx 11264).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 57511 38340 57511 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel115021 w.s).1 (adaptiveSpanLevel115021 w.s).2) = true := by
  simp only [adaptiveSpanLevel115021]
  decide +kernel
end Erdos883Verified
