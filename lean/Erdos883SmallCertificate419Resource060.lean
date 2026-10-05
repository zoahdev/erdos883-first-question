import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_60 :
    (List.ofFn coreChunks419_60).flatten =
      (coreData419.take (coreResources419 60).q).drop 122 := by
  decide +kernel

theorem coreCheck419_60 :
    ∀ c : Fin 1, (coreChunks419_60 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 60)) = true := by
  decide +kernel
#print axioms coreFlatten419_60
#print axioms coreCheck419_60
end Erdos883Verified
