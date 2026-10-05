import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_43 :
    (List.ofFn coreChunks419_43).flatten =
      (coreData419.take (coreResources419 43).q).drop 87 := by
  decide +kernel

theorem coreCheck419_43 :
    ∀ c : Fin 1, (coreChunks419_43 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 43)) = true := by
  decide +kernel
#print axioms coreFlatten419_43
#print axioms coreCheck419_43
end Erdos883Verified
