import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_11 :
    (List.ofFn coreChunks419_11).flatten =
      (coreData419.take (coreResources419 11).q).drop 87 := by
  decide +kernel

theorem coreCheck419_11 :
    ∀ c : Fin 1, (coreChunks419_11 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 11)) = true := by
  decide +kernel
#print axioms coreFlatten419_11
#print axioms coreCheck419_11
end Erdos883Verified
