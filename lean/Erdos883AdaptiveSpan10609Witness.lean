import Erdos883AdaptiveSpan10609Level0
import Erdos883AdaptiveSpan10609Level1
import Erdos883AdaptiveSpan10609Level2
import Erdos883AdaptiveSpan10609Level3
import Erdos883AdaptiveSpan10609Level4
import Erdos883AdaptiveSpan10609Level5
import Erdos883AdaptiveSpan10609Level6
import Erdos883AdaptiveSpan10609Level7
import Erdos883AdaptiveSpan10609Level8
import Erdos883AdaptiveSpan10609WitnessBatch000
import Erdos883AdaptiveSpan10609WitnessBatch001
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitnessLength10609 : adaptiveSpanWitness10609.length = 1768 := by
  simp only [adaptiveSpanWitness10609, List.length_flatten, List.map_cons, List.map_nil, adaptiveSpanWitness10609ChunkLength0, adaptiveSpanWitness10609ChunkLength1, List.sum_cons, List.sum_nil, Nat.reduceAdd]
theorem adaptiveSpanWitnessCheck10609 : adaptiveSpanWitness10609.zipIdx.all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 5305 3536 5305 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel10609 w.s).1 (adaptiveSpanLevel10609 w.s).2) = true := by
  apply adaptiveSpanZipIdxChunksCheck_sound
  simp only [adaptiveSpanZipIdxChunksCheck, adaptiveSpanWitness10609ChunkLength0, adaptiveSpanWitness10609ChunkLength1, Nat.reduceAdd, adaptiveSpanWitness10609ChunkCheck0, adaptiveSpanWitness10609ChunkCheck1, Bool.true_and]
end Erdos883Verified
