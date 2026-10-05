import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_18 :
    (List.ofFn coreChunks93_18).flatten =
      (coreData93.take (coreResources93 18).q).drop 0 := by
  decide +kernel

theorem coreCheck93_18 :
    ∀ c : Fin 2, (coreChunks93_18 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 18)) = true := by
  decide +kernel
#print axioms coreFlatten93_18
#print axioms coreCheck93_18
end Erdos883Verified
