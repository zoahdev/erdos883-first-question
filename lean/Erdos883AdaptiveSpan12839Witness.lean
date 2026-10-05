import Erdos883AdaptiveSpan12839Level0
import Erdos883AdaptiveSpan12839Level1
import Erdos883AdaptiveSpan12839Level2
import Erdos883AdaptiveSpan12839Level3
import Erdos883AdaptiveSpan12839Level4
import Erdos883AdaptiveSpan12839Level5
import Erdos883AdaptiveSpan12839Level6
import Erdos883AdaptiveSpan12839Level7
import Erdos883AdaptiveSpan12839Level8
import Erdos883AdaptiveSpan12839WitnessBatch000
import Erdos883AdaptiveSpan12839WitnessBatch001
import Erdos883AdaptiveSpan12839WitnessBatch002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitnessLength12839 : adaptiveSpanWitness12839.length = 2139 := by
  simp only [adaptiveSpanWitness12839, List.length_flatten, List.map_cons, List.map_nil, adaptiveSpanWitness12839ChunkLength0, adaptiveSpanWitness12839ChunkLength1, adaptiveSpanWitness12839ChunkLength2, List.sum_cons, List.sum_nil, Nat.reduceAdd]
theorem adaptiveSpanWitnessCheck12839 : adaptiveSpanWitness12839.zipIdx.all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 6420 4279 6419 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel12839 w.s).1 (adaptiveSpanLevel12839 w.s).2) = true := by
  apply adaptiveSpanZipIdxChunksCheck_sound
  simp only [adaptiveSpanZipIdxChunksCheck, adaptiveSpanWitness12839ChunkLength0, adaptiveSpanWitness12839ChunkLength1, adaptiveSpanWitness12839ChunkLength2, Nat.reduceAdd, adaptiveSpanWitness12839ChunkCheck0, adaptiveSpanWitness12839ChunkCheck1, adaptiveSpanWitness12839ChunkCheck2, Bool.true_and]
end Erdos883Verified
