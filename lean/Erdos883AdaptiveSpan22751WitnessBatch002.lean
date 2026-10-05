import Erdos883AdaptiveSpan22751WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness22751ChunkLength2 : adaptiveSpanWitness22751Chunk2.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness22751ChunkCheck2 : (adaptiveSpanWitness22751Chunk2.zipIdx 2048).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 11376 7583 11375 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel22751 w.s).1 (adaptiveSpanLevel22751 w.s).2) = true := by
  simp only [adaptiveSpanLevel22751]
  decide +kernel
end Erdos883Verified
