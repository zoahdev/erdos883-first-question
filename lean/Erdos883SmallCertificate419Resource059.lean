import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_59 :
    (List.ofFn coreChunks419_59).flatten =
      (coreData419.take (coreResources419 59).q).drop 119 := by
  decide +kernel

theorem coreCheck419_59 :
    ∀ c : Fin 1, (coreChunks419_59 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 59)) = true := by
  decide +kernel
#print axioms coreFlatten419_59
#print axioms coreCheck419_59
end Erdos883Verified
