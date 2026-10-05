import Erdos883AdaptiveSpan11671Level0
import Erdos883AdaptiveSpan11671Level1
import Erdos883AdaptiveSpan11671Level2
import Erdos883AdaptiveSpan11671Level3
import Erdos883AdaptiveSpan11671Level4
import Erdos883AdaptiveSpan11671Level5
import Erdos883AdaptiveSpan11671Level6
import Erdos883AdaptiveSpan11671Level7
import Erdos883AdaptiveSpan11671Level8
import Erdos883AdaptiveSpan11671WitnessBatch000
import Erdos883AdaptiveSpan11671WitnessBatch001
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitnessLength11671 : adaptiveSpanWitness11671.length = 1945 := by
  simp only [adaptiveSpanWitness11671, List.length_flatten, List.map_cons, List.map_nil, adaptiveSpanWitness11671ChunkLength0, adaptiveSpanWitness11671ChunkLength1, List.sum_cons, List.sum_nil, Nat.reduceAdd]
theorem adaptiveSpanWitnessCheck11671 : adaptiveSpanWitness11671.zipIdx.all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 5836 3890 5836 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel11671 w.s).1 (adaptiveSpanLevel11671 w.s).2) = true := by
  apply adaptiveSpanZipIdxChunksCheck_sound
  simp only [adaptiveSpanZipIdxChunksCheck, adaptiveSpanWitness11671ChunkLength0, adaptiveSpanWitness11671ChunkLength1, Nat.reduceAdd, adaptiveSpanWitness11671ChunkCheck0, adaptiveSpanWitness11671ChunkCheck1, Bool.true_and]
end Erdos883Verified
