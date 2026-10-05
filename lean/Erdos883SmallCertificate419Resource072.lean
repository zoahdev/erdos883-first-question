import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_72 :
    (List.ofFn coreChunks419_72).flatten =
      (coreData419.take (coreResources419 72).q).drop 180 := by
  decide +kernel

theorem coreCheck419_72 :
    ∀ c : Fin 1, (coreChunks419_72 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 72)) = true := by
  decide +kernel
#print axioms coreFlatten419_72
#print axioms coreCheck419_72
end Erdos883Verified
