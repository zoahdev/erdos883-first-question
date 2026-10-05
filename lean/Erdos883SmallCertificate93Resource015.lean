import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_15 :
    (List.ofFn coreChunks93_15).flatten =
      (coreData93.take (coreResources93 15).q).drop 37 := by
  decide +kernel

theorem coreCheck93_15 :
    ∀ c : Fin 1, (coreChunks93_15 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 15)) = true := by
  decide +kernel
#print axioms coreFlatten93_15
#print axioms coreCheck93_15
end Erdos883Verified
