import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_12 :
    (List.ofFn coreChunks93_12).flatten =
      (coreData93.take (coreResources93 12).q).drop 28 := by
  decide +kernel

theorem coreCheck93_12 :
    ∀ c : Fin 1, (coreChunks93_12 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 12)) = true := by
  decide +kernel
#print axioms coreFlatten93_12
#print axioms coreCheck93_12
end Erdos883Verified
