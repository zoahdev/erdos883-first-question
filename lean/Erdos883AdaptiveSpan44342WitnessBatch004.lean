import Erdos883AdaptiveSpan44342WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness44342ChunkLength4 : adaptiveSpanWitness44342Chunk4.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness44342ChunkCheck4 : (adaptiveSpanWitness44342Chunk4.zipIdx 4096).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 22171 14780 22171 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel44342 w.s).1 (adaptiveSpanLevel44342 w.s).2) = true := by
  simp only [adaptiveSpanLevel44342]
  decide +kernel
end Erdos883Verified
