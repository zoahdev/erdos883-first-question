import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_37 :
    (List.ofFn coreChunks419_37).flatten =
      (coreData419.take (coreResources419 37).q).drop 78 := by
  decide +kernel

theorem coreCheck419_37 :
    ∀ c : Fin 1, (coreChunks419_37 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 37)) = true := by
  decide +kernel
#print axioms coreFlatten419_37
#print axioms coreCheck419_37
end Erdos883Verified
