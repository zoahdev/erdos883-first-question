import Erdos883AdaptiveSpan53655WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness53655ChunkLength3 : adaptiveSpanWitness53655Chunk3.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness53655ChunkCheck3 : (adaptiveSpanWitness53655Chunk3.zipIdx 3072).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 26828 17884 26827 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel53655 w.s).1 (adaptiveSpanLevel53655 w.s).2) = true := by
  simp only [adaptiveSpanLevel53655]
  decide +kernel
end Erdos883Verified
