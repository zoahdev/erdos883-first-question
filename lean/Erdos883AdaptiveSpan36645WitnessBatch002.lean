import Erdos883AdaptiveSpan36645WitnessData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveSpanWitness36645ChunkLength2 : adaptiveSpanWitness36645Chunk2.length = 1024 := by decide +kernel
theorem adaptiveSpanWitness36645ChunkCheck2 : (adaptiveSpanWitness36645Chunk2.zipIdx 2048).all (fun (w,i) => decide (w.s ≤ 9) && adaptiveSpanRankWitnessCheck 18323 12214 18322 (i+1) (coreSignatureBudget w.s) w (adaptiveSpanLevel36645 w.s).1 (adaptiveSpanLevel36645 w.s).2) = true := by
  simp only [adaptiveSpanLevel36645]
  decide +kernel
end Erdos883Verified
