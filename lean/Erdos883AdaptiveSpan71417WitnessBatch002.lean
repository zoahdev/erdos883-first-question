import Erdos883AdaptiveSpan71417WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness71417ChunkLength2 : adaptiveSpanWitness71417Chunk2.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness71417ChunkCheck2 : (adaptiveSpanWitness71417Chunk2.zipIdx 2048).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 35709 23805 35708 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel71417 w.s).1 (adaptiveSpanLevel71417 w.s).2) = true := by
  simp only [adaptiveSpanLevel71417]
  decide +kernel
end Erdos883Verified
