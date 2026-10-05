import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_56 :
    (List.ofFn coreChunks419_56).flatten =
      (coreData419.take (coreResources419 56).q).drop 110 := by
  decide +kernel

theorem coreCheck419_56 :
    ∀ c : Fin 1, (coreChunks419_56 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 56)) = true := by
  decide +kernel
#print axioms coreFlatten419_56
#print axioms coreCheck419_56
end Erdos883Verified
