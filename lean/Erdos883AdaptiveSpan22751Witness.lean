import Erdos883AdaptiveSpan22751Level0
import Erdos883AdaptiveSpan22751Level1
import Erdos883AdaptiveSpan22751Level2
import Erdos883AdaptiveSpan22751Level3
import Erdos883AdaptiveSpan22751Level4
import Erdos883AdaptiveSpan22751Level5
import Erdos883AdaptiveSpan22751Level6
import Erdos883AdaptiveSpan22751Level7
import Erdos883AdaptiveSpan22751Level8
import Erdos883AdaptiveSpan22751WitnessBatch000
import Erdos883AdaptiveSpan22751WitnessBatch001
import Erdos883AdaptiveSpan22751WitnessBatch002
import Erdos883AdaptiveSpan22751WitnessBatch003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitnessLength22751 : adaptiveSpanWitness22751.length = 3791 := by
  simp only [adaptiveSpanWitness22751, List.length_flatten, List.map_cons, List.map_nil, adaptiveSpanWitness22751ChunkLength0, adaptiveSpanWitness22751ChunkLength1, adaptiveSpanWitness22751ChunkLength2, adaptiveSpanWitness22751ChunkLength3, List.sum_cons, List.sum_nil, Nat.reduceAdd]
theorem adaptiveSpanWitnessCheck22751 : adaptiveSpanWitness22751.zipIdx.all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 11376 7583 11375 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel22751 w.s).1 (adaptiveSpanLevel22751 w.s).2) = true := by
  apply adaptiveSpanZipIdxChunksCheck_sound
  simp only [adaptiveSpanZipIdxChunksCheck, adaptiveSpanWitness22751ChunkLength0, adaptiveSpanWitness22751ChunkLength1, adaptiveSpanWitness22751ChunkLength2, adaptiveSpanWitness22751ChunkLength3, Nat.reduceAdd, adaptiveSpanWitness22751ChunkCheck0, adaptiveSpanWitness22751ChunkCheck1, adaptiveSpanWitness22751ChunkCheck2, adaptiveSpanWitness22751ChunkCheck3, Bool.true_and]
end Erdos883Verified
