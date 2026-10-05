import Erdos883AdaptiveSpan10609WitnessData
import Erdos883AdaptiveSpan10609WitnessFast0
import Erdos883AdaptiveSpan10609WitnessFast2
import Erdos883AdaptiveSpan10609WitnessFast3
import Erdos883AdaptiveSpan10609WitnessFast4
import Erdos883AdaptiveSpan10609WitnessFast5
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness10609ChunkLength0 : adaptiveSpanWitness10609Chunk0.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness10609ChunkCheck0 : (adaptiveSpanWitness10609Chunk0.zipIdx 0).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 5305 3536 5305 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel10609 w.s).1 (adaptiveSpanLevel10609 w.s).2) = true := by
  simp only [adaptiveSpanLevel10609, adaptiveSpanEvenFastEq10609_0, adaptiveSpanWholeFastEq10609_0, adaptiveSpanEvenFastEq10609_2, adaptiveSpanWholeFastEq10609_2, adaptiveSpanEvenFastEq10609_3, adaptiveSpanWholeFastEq10609_3, adaptiveSpanEvenFastEq10609_4, adaptiveSpanWholeFastEq10609_4, adaptiveSpanEvenFastEq10609_5, adaptiveSpanWholeFastEq10609_5]
  decide +kernel
end Erdos883Verified
