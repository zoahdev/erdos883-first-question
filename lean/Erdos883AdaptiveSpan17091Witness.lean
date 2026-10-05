import Erdos883AdaptiveSpan17091Level0
import Erdos883AdaptiveSpan17091Level1
import Erdos883AdaptiveSpan17091Level2
import Erdos883AdaptiveSpan17091Level3
import Erdos883AdaptiveSpan17091Level4
import Erdos883AdaptiveSpan17091Level5
import Erdos883AdaptiveSpan17091Level6
import Erdos883AdaptiveSpan17091Level7
import Erdos883AdaptiveSpan17091Level8
import Erdos883AdaptiveSpan17091WitnessBatch000
import Erdos883AdaptiveSpan17091WitnessBatch001
import Erdos883AdaptiveSpan17091WitnessBatch002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitnessLength17091 : adaptiveSpanWitness17091.length = 2848 := by
  simp only [adaptiveSpanWitness17091, List.length_flatten, List.map_cons, List.map_nil, adaptiveSpanWitness17091ChunkLength0, adaptiveSpanWitness17091ChunkLength1, adaptiveSpanWitness17091ChunkLength2, List.sum_cons, List.sum_nil, Nat.reduceAdd]
theorem adaptiveSpanWitnessCheck17091 : adaptiveSpanWitness17091.zipIdx.all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 8546 5696 8545 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel17091 w.s).1 (adaptiveSpanLevel17091 w.s).2) = true := by
  apply adaptiveSpanZipIdxChunksCheck_sound
  simp only [adaptiveSpanZipIdxChunksCheck, adaptiveSpanWitness17091ChunkLength0, adaptiveSpanWitness17091ChunkLength1, adaptiveSpanWitness17091ChunkLength2, Nat.reduceAdd, adaptiveSpanWitness17091ChunkCheck0, adaptiveSpanWitness17091ChunkCheck1, adaptiveSpanWitness17091ChunkCheck2, Bool.true_and]
end Erdos883Verified
