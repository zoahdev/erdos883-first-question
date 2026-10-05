import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_6 :
    (List.ofFn coreChunks419_6).flatten =
      (coreData419.take (coreResources419 6).q).drop 79 := by
  decide +kernel

theorem coreCheck419_6 :
    ∀ c : Fin 1, (coreChunks419_6 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 6)) = true := by
  decide +kernel
#print axioms coreFlatten419_6
#print axioms coreCheck419_6
end Erdos883Verified
