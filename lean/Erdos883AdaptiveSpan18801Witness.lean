import Erdos883AdaptiveSpan18801Level0
import Erdos883AdaptiveSpan18801Level1
import Erdos883AdaptiveSpan18801Level2
import Erdos883AdaptiveSpan18801Level3
import Erdos883AdaptiveSpan18801Level4
import Erdos883AdaptiveSpan18801Level5
import Erdos883AdaptiveSpan18801Level6
import Erdos883AdaptiveSpan18801Level7
import Erdos883AdaptiveSpan18801WitnessBatch000
import Erdos883AdaptiveSpan18801WitnessBatch001
import Erdos883AdaptiveSpan18801WitnessBatch002
import Erdos883AdaptiveSpan18801WitnessBatch003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitnessLength18801 : adaptiveSpanWitness18801.length = 3133 := by
  simp only [adaptiveSpanWitness18801, List.length_flatten, List.map_cons, List.map_nil, adaptiveSpanWitness18801ChunkLength0, adaptiveSpanWitness18801ChunkLength1, adaptiveSpanWitness18801ChunkLength2, adaptiveSpanWitness18801ChunkLength3, List.sum_cons, List.sum_nil, Nat.reduceAdd]
theorem adaptiveSpanWitnessCheck18801 : adaptiveSpanWitness18801.zipIdx.all (fun (w,i) => decide (w.s ≤ 7) && adaptiveSpanRankWitnessCheck 9401 6266 9400 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel18801 w.s).1 (adaptiveSpanLevel18801 w.s).2) = true := by
  apply adaptiveSpanZipIdxChunksCheck_sound
  simp only [adaptiveSpanZipIdxChunksCheck, adaptiveSpanWitness18801ChunkLength0, adaptiveSpanWitness18801ChunkLength1, adaptiveSpanWitness18801ChunkLength2, adaptiveSpanWitness18801ChunkLength3, Nat.reduceAdd, adaptiveSpanWitness18801ChunkCheck0, adaptiveSpanWitness18801ChunkCheck1, adaptiveSpanWitness18801ChunkCheck2, adaptiveSpanWitness18801ChunkCheck3, Bool.true_and]
end Erdos883Verified
