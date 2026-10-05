import Erdos883AdaptiveSpan185246WitnessData
import Erdos883AdaptiveSpan185246WitnessFast8
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness185246ChunkLength30 : adaptiveSpanWitness185246Chunk30.length = 154 := by decide +kernel
theorem adaptiveSpanWitness185246ChunkCheck30 : (adaptiveSpanWitness185246Chunk30.zipIdx 30720).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 92623 61748 92623 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel185246 w.s).1 (adaptiveSpanLevel185246 w.s).2) = true := by
  simp only [adaptiveSpanLevel185246, adaptiveSpanEvenFastEq185246_8, adaptiveSpanWholeFastEq185246_8]
  decide +kernel
end Erdos883Verified
