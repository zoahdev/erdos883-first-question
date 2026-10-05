import Erdos883AdaptiveSpan95058WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness95058ChunkLength12 : adaptiveSpanWitness95058Chunk12.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness95058ChunkCheck12 : (adaptiveSpanWitness95058Chunk12.zipIdx 12288).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 47529 31685 47529 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel95058 w.s).1 (adaptiveSpanLevel95058 w.s).2) = true := by
  simp only [adaptiveSpanLevel95058]
  decide +kernel
end Erdos883Verified
