import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_1 :
    (List.ofFn coreChunks93_1).flatten =
      (coreData93.take (coreResources93 1).q).drop 11 := by
  decide +kernel

theorem coreCheck93_1 :
    ∀ c : Fin 1, (coreChunks93_1 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 1)) = true := by
  decide +kernel
#print axioms coreFlatten93_1
#print axioms coreCheck93_1
end Erdos883Verified
