import Erdos883AdaptiveSpan22751WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness22751ChunkLength3 : adaptiveSpanWitness22751Chunk3.length = 719 := by decide +kernel
theorem adaptiveSpanWitness22751ChunkCheck3 : (adaptiveSpanWitness22751Chunk3.zipIdx 3072).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 11376 7583 11375 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel22751 w.s).1 (adaptiveSpanLevel22751 w.s).2) = true := by
  simp only [adaptiveSpanLevel22751]
  decide +kernel
end Erdos883Verified
