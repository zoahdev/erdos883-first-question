import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_62 :
    (List.ofFn coreChunks419_62).flatten =
      (coreData419.take (coreResources419 62).q).drop 127 := by
  decide +kernel

theorem coreCheck419_62 :
    ∀ c : Fin 1, (coreChunks419_62 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 62)) = true := by
  decide +kernel
#print axioms coreFlatten419_62
#print axioms coreCheck419_62
end Erdos883Verified
