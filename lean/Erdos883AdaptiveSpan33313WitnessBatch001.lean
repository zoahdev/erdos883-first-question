import Erdos883AdaptiveSpan33313WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness33313ChunkLength1 : adaptiveSpanWitness33313Chunk1.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness33313ChunkCheck1 : (adaptiveSpanWitness33313Chunk1.zipIdx 1024).all (fun (w,i) => decide (w.s ≤ 9) && adaptiveSpanRankWitnessCheck 16657 11104 16657 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel33313 w.s).1 (adaptiveSpanLevel33313 w.s).2) = true := by
  simp only [adaptiveSpanLevel33313]
  decide +kernel
end Erdos883Verified
