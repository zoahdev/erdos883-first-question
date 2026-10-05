import Erdos883AdaptiveSpan199999WitnessData
import Erdos883AdaptiveSpan199999WitnessFast7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness199999ChunkLength32 : adaptiveSpanWitness199999Chunk32.length = 565 := by decide +kernel
theorem adaptiveSpanWitness199999ChunkCheck32 : (adaptiveSpanWitness199999Chunk32.zipIdx 32768).all (fun (w,i) => decide (w.s ≤ 7) && adaptiveSpanRankWitnessCheck 100000 66666 100000 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel199999 w.s).1 (adaptiveSpanLevel199999 w.s).2) = true := by
  simp only [adaptiveSpanLevel199999, adaptiveSpanEvenFastEq199999_7, adaptiveSpanWholeFastEq199999_7]
  decide +kernel
end Erdos883Verified
