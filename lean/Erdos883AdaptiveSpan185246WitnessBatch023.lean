import Erdos883AdaptiveSpan185246WitnessData
import Erdos883AdaptiveSpan185246WitnessFast5
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness185246ChunkLength23 : adaptiveSpanWitness185246Chunk23.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness185246ChunkCheck23 : (adaptiveSpanWitness185246Chunk23.zipIdx 23552).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 92623 61748 92623 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel185246 w.s).1 (adaptiveSpanLevel185246 w.s).2) = true := by
  simp only [adaptiveSpanLevel185246, adaptiveSpanEvenFastEq185246_5, adaptiveSpanWholeFastEq185246_5]
  decide +kernel
end Erdos883Verified
