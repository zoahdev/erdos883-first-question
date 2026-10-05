import Erdos883AdaptiveSpan14124Level0
import Erdos883AdaptiveSpan14124Level1
import Erdos883AdaptiveSpan14124Level2
import Erdos883AdaptiveSpan14124Level3
import Erdos883AdaptiveSpan14124Level4
import Erdos883AdaptiveSpan14124Level5
import Erdos883AdaptiveSpan14124Level6
import Erdos883AdaptiveSpan14124Level7
import Erdos883AdaptiveSpan14124Level8
import Erdos883AdaptiveSpan14124WitnessBatch000
import Erdos883AdaptiveSpan14124WitnessBatch001
import Erdos883AdaptiveSpan14124WitnessBatch002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitnessLength14124 : adaptiveSpanWitness14124.length = 2354 := by
  simp only [adaptiveSpanWitness14124, List.length_flatten, List.map_cons, List.map_nil, adaptiveSpanWitness14124ChunkLength0, adaptiveSpanWitness14124ChunkLength1, adaptiveSpanWitness14124ChunkLength2, List.sum_cons, List.sum_nil, Nat.reduceAdd]
theorem adaptiveSpanWitnessCheck14124 : adaptiveSpanWitness14124.zipIdx.all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 7062 4707 7062 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel14124 w.s).1 (adaptiveSpanLevel14124 w.s).2) = true := by
  apply adaptiveSpanZipIdxChunksCheck_sound
  simp only [adaptiveSpanZipIdxChunksCheck, adaptiveSpanWitness14124ChunkLength0, adaptiveSpanWitness14124ChunkLength1, adaptiveSpanWitness14124ChunkLength2, Nat.reduceAdd, adaptiveSpanWitness14124ChunkCheck0, adaptiveSpanWitness14124ChunkCheck1, adaptiveSpanWitness14124ChunkCheck2, Bool.true_and]
end Erdos883Verified
