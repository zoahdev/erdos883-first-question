import Erdos883AdaptiveSpan78559WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness78559ChunkLength8 : adaptiveSpanWitness78559Chunk8.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness78559ChunkCheck8 : (adaptiveSpanWitness78559Chunk8.zipIdx 8192).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 39280 26186 39280 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel78559 w.s).1 (adaptiveSpanLevel78559 w.s).2) = true := by
  simp only [adaptiveSpanLevel78559]
  decide +kernel
end Erdos883Verified
