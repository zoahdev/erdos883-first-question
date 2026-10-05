import Erdos883AdaptiveSpan15537Level0
import Erdos883AdaptiveSpan15537Level1
import Erdos883AdaptiveSpan15537Level2
import Erdos883AdaptiveSpan15537Level3
import Erdos883AdaptiveSpan15537Level4
import Erdos883AdaptiveSpan15537Level5
import Erdos883AdaptiveSpan15537Level6
import Erdos883AdaptiveSpan15537Level7
import Erdos883AdaptiveSpan15537Level8
import Erdos883AdaptiveSpan15537WitnessBatch000
import Erdos883AdaptiveSpan15537WitnessBatch001
import Erdos883AdaptiveSpan15537WitnessBatch002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitnessLength15537 : adaptiveSpanWitness15537.length = 2589 := by
  simp only [adaptiveSpanWitness15537, List.length_flatten, List.map_cons, List.map_nil, adaptiveSpanWitness15537ChunkLength0, adaptiveSpanWitness15537ChunkLength1, adaptiveSpanWitness15537ChunkLength2, List.sum_cons, List.sum_nil, Nat.reduceAdd]
theorem adaptiveSpanWitnessCheck15537 : adaptiveSpanWitness15537.zipIdx.all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 7769 5178 7768 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel15537 w.s).1 (adaptiveSpanLevel15537 w.s).2) = true := by
  apply adaptiveSpanZipIdxChunksCheck_sound
  simp only [adaptiveSpanZipIdxChunksCheck, adaptiveSpanWitness15537ChunkLength0, adaptiveSpanWitness15537ChunkLength1, adaptiveSpanWitness15537ChunkLength2, Nat.reduceAdd, adaptiveSpanWitness15537ChunkCheck0, adaptiveSpanWitness15537ChunkCheck1, adaptiveSpanWitness15537ChunkCheck2, Bool.true_and]
end Erdos883Verified
