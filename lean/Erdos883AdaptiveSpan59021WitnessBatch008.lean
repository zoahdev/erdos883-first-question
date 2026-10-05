import Erdos883AdaptiveSpan59021WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness59021ChunkLength8 : adaptiveSpanWitness59021Chunk8.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness59021ChunkCheck8 : (adaptiveSpanWitness59021Chunk8.zipIdx 8192).all (fun (w,i) => decide (w.s ≤ 9) && adaptiveSpanRankWitnessCheck 29511 19673 29510 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel59021 w.s).1 (adaptiveSpanLevel59021 w.s).2) = true := by
  simp only [adaptiveSpanLevel59021]
  decide +kernel
end Erdos883Verified
