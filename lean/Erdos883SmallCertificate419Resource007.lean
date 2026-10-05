import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_7 :
    (List.ofFn coreChunks419_7).flatten =
      (coreData419.take (coreResources419 7).q).drop 82 := by
  decide +kernel

theorem coreCheck419_7 :
    ∀ c : Fin 1, (coreChunks419_7 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 7)) = true := by
  decide +kernel
#print axioms coreFlatten419_7
#print axioms coreCheck419_7
end Erdos883Verified
