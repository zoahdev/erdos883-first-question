import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_16 :
    (List.ofFn coreChunks419_16).flatten =
      (coreData419.take (coreResources419 16).q).drop 93 := by
  decide +kernel

theorem coreCheck419_16 :
    ∀ c : Fin 1, (coreChunks419_16 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 16)) = true := by
  decide +kernel
#print axioms coreFlatten419_16
#print axioms coreCheck419_16
end Erdos883Verified
