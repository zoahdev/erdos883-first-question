import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_54 :
    (List.ofFn coreChunks419_54).flatten =
      (coreData419.take (coreResources419 54).q).drop 107 := by
  decide +kernel

theorem coreCheck419_54 :
    ∀ c : Fin 1, (coreChunks419_54 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 54)) = true := by
  decide +kernel
#print axioms coreFlatten419_54
#print axioms coreCheck419_54
end Erdos883Verified
