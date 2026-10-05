import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_74 :
    (List.ofFn coreChunks419_74).flatten =
      (coreData419.take (coreResources419 74).q).drop 0 := by
  decide +kernel

theorem coreCheck419_74 :
    ∀ c : Fin 11, (coreChunks419_74 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 74)) = true := by
  decide +kernel
#print axioms coreFlatten419_74
#print axioms coreCheck419_74
end Erdos883Verified
