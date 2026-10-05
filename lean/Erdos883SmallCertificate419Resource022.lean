import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_22 :
    (List.ofFn coreChunks419_22).flatten =
      (coreData419.take (coreResources419 22).q).drop 104 := by
  decide +kernel

theorem coreCheck419_22 :
    ∀ c : Fin 1, (coreChunks419_22 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 22)) = true := by
  decide +kernel
#print axioms coreFlatten419_22
#print axioms coreCheck419_22
end Erdos883Verified
