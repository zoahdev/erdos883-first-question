import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_38 :
    (List.ofFn coreChunks419_38).flatten =
      (coreData419.take (coreResources419 38).q).drop 80 := by
  decide +kernel

theorem coreCheck419_38 :
    ∀ c : Fin 1, (coreChunks419_38 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 38)) = true := by
  decide +kernel
#print axioms coreFlatten419_38
#print axioms coreCheck419_38
end Erdos883Verified
