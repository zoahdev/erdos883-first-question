import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_55 :
    (List.ofFn coreChunks419_55).flatten =
      (coreData419.take (coreResources419 55).q).drop 108 := by
  decide +kernel

theorem coreCheck419_55 :
    ∀ c : Fin 1, (coreChunks419_55 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 55)) = true := by
  decide +kernel
#print axioms coreFlatten419_55
#print axioms coreCheck419_55
end Erdos883Verified
