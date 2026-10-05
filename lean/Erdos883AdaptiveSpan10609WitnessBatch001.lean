import Erdos883AdaptiveSpan10609WitnessData
import Erdos883AdaptiveSpan10609WitnessFast5
import Erdos883AdaptiveSpan10609WitnessFast6
import Erdos883AdaptiveSpan10609WitnessFast7
import Erdos883AdaptiveSpan10609WitnessFast8
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness10609ChunkLength1 : adaptiveSpanWitness10609Chunk1.length = 744 := by decide +kernel
theorem adaptiveSpanWitness10609ChunkCheck1 : (adaptiveSpanWitness10609Chunk1.zipIdx 1024).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 5305 3536 5305 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel10609 w.s).1 (adaptiveSpanLevel10609 w.s).2) = true := by
  simp only [adaptiveSpanLevel10609, adaptiveSpanEvenFastEq10609_5, adaptiveSpanWholeFastEq10609_5, adaptiveSpanEvenFastEq10609_6, adaptiveSpanWholeFastEq10609_6, adaptiveSpanEvenFastEq10609_7, adaptiveSpanWholeFastEq10609_7, adaptiveSpanEvenFastEq10609_8, adaptiveSpanWholeFastEq10609_8]
  decide +kernel
end Erdos883Verified
