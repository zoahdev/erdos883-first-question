import Erdos883AdaptiveSpan11671WitnessData
import Erdos883AdaptiveSpan11671WitnessFast4
import Erdos883AdaptiveSpan11671WitnessFast5
import Erdos883AdaptiveSpan11671WitnessFast6
import Erdos883AdaptiveSpan11671WitnessFast7
import Erdos883AdaptiveSpan11671WitnessFast8
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness11671ChunkLength1 : adaptiveSpanWitness11671Chunk1.length = 921 := by decide +kernel
theorem adaptiveSpanWitness11671ChunkCheck1 : (adaptiveSpanWitness11671Chunk1.zipIdx 1024).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 5836 3890 5836 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel11671 w.s).1 (adaptiveSpanLevel11671 w.s).2) = true := by
  simp only [adaptiveSpanLevel11671, adaptiveSpanEvenFastEq11671_4, adaptiveSpanWholeFastEq11671_4, adaptiveSpanEvenFastEq11671_5, adaptiveSpanWholeFastEq11671_5, adaptiveSpanEvenFastEq11671_6, adaptiveSpanWholeFastEq11671_6, adaptiveSpanEvenFastEq11671_7, adaptiveSpanWholeFastEq11671_7, adaptiveSpanEvenFastEq11671_8, adaptiveSpanWholeFastEq11671_8]
  decide +kernel
end Erdos883Verified
