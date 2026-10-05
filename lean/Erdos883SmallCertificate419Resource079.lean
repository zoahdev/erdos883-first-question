import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_79 :
    (List.ofFn coreChunks419_79).flatten =
      (coreData419.take (coreResources419 79).q).drop 0 := by
  decide +kernel

theorem coreCheck419_79 :
    ∀ c : Fin 8, (coreChunks419_79 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 79)) = true := by
  decide +kernel
#print axioms coreFlatten419_79
#print axioms coreCheck419_79
end Erdos883Verified
