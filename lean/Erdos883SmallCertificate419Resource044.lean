import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_44 :
    (List.ofFn coreChunks419_44).flatten =
      (coreData419.take (coreResources419 44).q).drop 88 := by
  decide +kernel

theorem coreCheck419_44 :
    ∀ c : Fin 1, (coreChunks419_44 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 44)) = true := by
  decide +kernel
#print axioms coreFlatten419_44
#print axioms coreCheck419_44
end Erdos883Verified
