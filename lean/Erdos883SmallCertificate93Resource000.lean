import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_0 :
    (List.ofFn coreChunks93_0).flatten =
      (coreData93.take (coreResources93 0).q).drop 0 := by
  decide +kernel

theorem coreCheck93_0 :
    ∀ c : Fin 1, (coreChunks93_0 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 0)) = true := by
  decide +kernel
#print axioms coreFlatten93_0
#print axioms coreCheck93_0
end Erdos883Verified
