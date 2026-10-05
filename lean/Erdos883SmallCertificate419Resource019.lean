import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_19 :
    (List.ofFn coreChunks419_19).flatten =
      (coreData419.take (coreResources419 19).q).drop 100 := by
  decide +kernel

theorem coreCheck419_19 :
    ∀ c : Fin 1, (coreChunks419_19 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 19)) = true := by
  decide +kernel
#print axioms coreFlatten419_19
#print axioms coreCheck419_19
end Erdos883Verified
