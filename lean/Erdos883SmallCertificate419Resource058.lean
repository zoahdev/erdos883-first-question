import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_58 :
    (List.ofFn coreChunks419_58).flatten =
      (coreData419.take (coreResources419 58).q).drop 114 := by
  decide +kernel

theorem coreCheck419_58 :
    ∀ c : Fin 1, (coreChunks419_58 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 58)) = true := by
  decide +kernel
#print axioms coreFlatten419_58
#print axioms coreCheck419_58
end Erdos883Verified
