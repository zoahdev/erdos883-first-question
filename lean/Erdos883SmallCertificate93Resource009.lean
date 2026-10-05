import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_9 :
    (List.ofFn coreChunks93_9).flatten =
      (coreData93.take (coreResources93 9).q).drop 25 := by
  decide +kernel

theorem coreCheck93_9 :
    ∀ c : Fin 1, (coreChunks93_9 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 9)) = true := by
  decide +kernel
#print axioms coreFlatten93_9
#print axioms coreCheck93_9
end Erdos883Verified
