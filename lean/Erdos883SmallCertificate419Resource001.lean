import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_1 :
    (List.ofFn coreChunks419_1).flatten =
      (coreData419.take (coreResources419 1).q).drop 40 := by
  decide +kernel

theorem coreCheck419_1 :
    ∀ c : Fin 1, (coreChunks419_1 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 1)) = true := by
  decide +kernel
#print axioms coreFlatten419_1
#print axioms coreCheck419_1
end Erdos883Verified
