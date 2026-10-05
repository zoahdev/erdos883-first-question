import Erdos883AdaptiveSpan78559WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness78559ChunkLength12 : adaptiveSpanWitness78559Chunk12.length = 805 := by decide +kernel
theorem adaptiveSpanWitness78559ChunkCheck12 : (adaptiveSpanWitness78559Chunk12.zipIdx 12288).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 39280 26186 39280 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel78559 w.s).1 (adaptiveSpanLevel78559 w.s).2) = true := by
  simp only [adaptiveSpanLevel78559]
  decide +kernel
end Erdos883Verified
