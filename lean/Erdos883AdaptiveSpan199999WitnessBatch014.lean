import Erdos883AdaptiveSpan199999WitnessData
import Erdos883AdaptiveSpan199999WitnessFast2
import Erdos883AdaptiveSpan199999WitnessFast3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness199999ChunkLength14 : adaptiveSpanWitness199999Chunk14.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness199999ChunkCheck14 : (adaptiveSpanWitness199999Chunk14.zipIdx 14336).all (fun (w,i) => decide (w.s ≤ 7) && adaptiveSpanRankWitnessCheck 100000 66666 100000 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel199999 w.s).1 (adaptiveSpanLevel199999 w.s).2) = true := by
  simp only [adaptiveSpanLevel199999, adaptiveSpanEvenFastEq199999_2, adaptiveSpanWholeFastEq199999_2, adaptiveSpanEvenFastEq199999_3, adaptiveSpanWholeFastEq199999_3]
  decide +kernel
end Erdos883Verified
