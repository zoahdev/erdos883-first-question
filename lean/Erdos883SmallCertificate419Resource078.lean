import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_78 :
    (List.ofFn coreChunks419_78).flatten =
      (coreData419.take (coreResources419 78).q).drop 0 := by
  decide +kernel

theorem coreCheck419_78 :
    ∀ c : Fin 7, (coreChunks419_78 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 78)) = true := by
  decide +kernel
#print axioms coreFlatten419_78
#print axioms coreCheck419_78
end Erdos883Verified
