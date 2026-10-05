import Erdos883AdaptiveSpan11671WitnessData
import Erdos883AdaptiveSpan11671WitnessFast0
import Erdos883AdaptiveSpan11671WitnessFast2
import Erdos883AdaptiveSpan11671WitnessFast3
import Erdos883AdaptiveSpan11671WitnessFast4
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness11671ChunkLength0 : adaptiveSpanWitness11671Chunk0.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness11671ChunkCheck0 : (adaptiveSpanWitness11671Chunk0.zipIdx 0).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 5836 3890 5836 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel11671 w.s).1 (adaptiveSpanLevel11671 w.s).2) = true := by
  simp only [adaptiveSpanLevel11671, adaptiveSpanEvenFastEq11671_0, adaptiveSpanWholeFastEq11671_0, adaptiveSpanEvenFastEq11671_2, adaptiveSpanWholeFastEq11671_2, adaptiveSpanEvenFastEq11671_3, adaptiveSpanWholeFastEq11671_3, adaptiveSpanEvenFastEq11671_4, adaptiveSpanWholeFastEq11671_4]
  decide +kernel
end Erdos883Verified
