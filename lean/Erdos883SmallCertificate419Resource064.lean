import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_64 :
    (List.ofFn coreChunks419_64).flatten =
      (coreData419.take (coreResources419 64).q).drop 130 := by
  decide +kernel

theorem coreCheck419_64 :
    ∀ c : Fin 1, (coreChunks419_64 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 64)) = true := by
  decide +kernel
#print axioms coreFlatten419_64
#print axioms coreCheck419_64
end Erdos883Verified
