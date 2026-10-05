import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_50 :
    (List.ofFn coreChunks419_50).flatten =
      (coreData419.take (coreResources419 50).q).drop 100 := by
  decide +kernel

theorem coreCheck419_50 :
    ∀ c : Fin 1, (coreChunks419_50 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 50)) = true := by
  decide +kernel
#print axioms coreFlatten419_50
#print axioms coreCheck419_50
end Erdos883Verified
