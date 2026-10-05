import Erdos883AdaptiveSpan104564WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness104564ChunkLength3 : adaptiveSpanWitness104564Chunk3.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness104564ChunkCheck3 : (adaptiveSpanWitness104564Chunk3.zipIdx 3072).all (fun (w,i) => decide (w.s ≤ 8) && adaptiveSpanRankWitnessCheck 52282 34854 52282 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel104564 w.s).1 (adaptiveSpanLevel104564 w.s).2) = true := by
  simp only [adaptiveSpanLevel104564]
  decide +kernel
end Erdos883Verified
