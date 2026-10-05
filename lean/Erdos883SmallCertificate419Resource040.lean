import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_40 :
    (List.ofFn coreChunks419_40).flatten =
      (coreData419.take (coreResources419 40).q).drop 83 := by
  decide +kernel

theorem coreCheck419_40 :
    ∀ c : Fin 1, (coreChunks419_40 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 40)) = true := by
  decide +kernel
#print axioms coreFlatten419_40
#print axioms coreCheck419_40
end Erdos883Verified
