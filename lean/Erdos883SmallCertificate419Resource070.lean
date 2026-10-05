import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_70 :
    (List.ofFn coreChunks419_70).flatten =
      (coreData419.take (coreResources419 70).q).drop 174 := by
  decide +kernel

theorem coreCheck419_70 :
    ∀ c : Fin 1, (coreChunks419_70 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 70)) = true := by
  decide +kernel
#print axioms coreFlatten419_70
#print axioms coreCheck419_70
end Erdos883Verified
