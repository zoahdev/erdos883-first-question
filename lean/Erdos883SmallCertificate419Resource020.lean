import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_20 :
    (List.ofFn coreChunks419_20).flatten =
      (coreData419.take (coreResources419 20).q).drop 101 := by
  decide +kernel

theorem coreCheck419_20 :
    ∀ c : Fin 1, (coreChunks419_20 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 20)) = true := by
  decide +kernel
#print axioms coreFlatten419_20
#print axioms coreCheck419_20
end Erdos883Verified
