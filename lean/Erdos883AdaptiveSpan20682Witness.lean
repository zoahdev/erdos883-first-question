import Erdos883AdaptiveSpan20682Level0
import Erdos883AdaptiveSpan20682Level1
import Erdos883AdaptiveSpan20682Level2
import Erdos883AdaptiveSpan20682Level3
import Erdos883AdaptiveSpan20682Level4
import Erdos883AdaptiveSpan20682Level5
import Erdos883AdaptiveSpan20682Level6
import Erdos883AdaptiveSpan20682Level7
import Erdos883AdaptiveSpan20682Level8
import Erdos883AdaptiveSpan20682WitnessBatch000
import Erdos883AdaptiveSpan20682WitnessBatch001
import Erdos883AdaptiveSpan20682WitnessBatch002
import Erdos883AdaptiveSpan20682WitnessBatch003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitnessLength20682 : adaptiveSpanWitness20682.length = 3447 := by
  simp only [adaptiveSpanWitness20682, List.length_flatten, List.map_cons, List.map_nil, adaptiveSpanWitness20682ChunkLength0, adaptiveSpanWitness20682ChunkLength1, adaptiveSpanWitness20682ChunkLength2, adaptiveSpanWitness20682ChunkLength3, List.sum_cons, List.sum_nil, Nat.reduceAdd]
theorem adaptiveSpanWitnessCheck20682 : adaptiveSpanWitness20682.zipIdx.all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 10341 6893 10341 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel20682 w.s).1 (adaptiveSpanLevel20682 w.s).2) = true := by
  apply adaptiveSpanZipIdxChunksCheck_sound
  simp only [adaptiveSpanZipIdxChunksCheck, adaptiveSpanWitness20682ChunkLength0, adaptiveSpanWitness20682ChunkLength1, adaptiveSpanWitness20682ChunkLength2, adaptiveSpanWitness20682ChunkLength3, Nat.reduceAdd, adaptiveSpanWitness20682ChunkCheck0, adaptiveSpanWitness20682ChunkCheck1, adaptiveSpanWitness20682ChunkCheck2, adaptiveSpanWitness20682ChunkCheck3, Bool.true_and]
end Erdos883Verified
