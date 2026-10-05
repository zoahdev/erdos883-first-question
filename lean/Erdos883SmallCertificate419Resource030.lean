import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_30 :
    (List.ofFn coreChunks419_30).flatten =
      (coreData419.take (coreResources419 30).q).drop 68 := by
  decide +kernel

theorem coreCheck419_30 :
    ∀ c : Fin 1, (coreChunks419_30 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 30)) = true := by
  decide +kernel
#print axioms coreFlatten419_30
#print axioms coreCheck419_30
end Erdos883Verified
