import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_45 :
    (List.ofFn coreChunks419_45).flatten =
      (coreData419.take (coreResources419 45).q).drop 90 := by
  decide +kernel

theorem coreCheck419_45 :
    ∀ c : Fin 1, (coreChunks419_45 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 45)) = true := by
  decide +kernel
#print axioms coreFlatten419_45
#print axioms coreCheck419_45
end Erdos883Verified
