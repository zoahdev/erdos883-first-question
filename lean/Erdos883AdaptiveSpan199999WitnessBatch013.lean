import Erdos883AdaptiveSpan199999WitnessData
import Erdos883AdaptiveSpan199999WitnessFast0
import Erdos883AdaptiveSpan199999WitnessFast2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness199999ChunkLength13 : adaptiveSpanWitness199999Chunk13.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness199999ChunkCheck13 : (adaptiveSpanWitness199999Chunk13.zipIdx 13312).all (fun (w,i) => decide (w.s ≤ 7) && adaptiveSpanRankWitnessCheck 100000 66666 100000 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel199999 w.s).1 (adaptiveSpanLevel199999 w.s).2) = true := by
  simp only [adaptiveSpanLevel199999, adaptiveSpanEvenFastEq199999_0, adaptiveSpanWholeFastEq199999_0, adaptiveSpanEvenFastEq199999_2, adaptiveSpanWholeFastEq199999_2]
  decide +kernel
end Erdos883Verified
