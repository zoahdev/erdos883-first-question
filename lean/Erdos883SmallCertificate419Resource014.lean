import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_14 :
    (List.ofFn coreChunks419_14).flatten =
      (coreData419.take (coreResources419 14).q).drop 91 := by
  decide +kernel

theorem coreCheck419_14 :
    ∀ c : Fin 1, (coreChunks419_14 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 14)) = true := by
  decide +kernel
#print axioms coreFlatten419_14
#print axioms coreCheck419_14
end Erdos883Verified
