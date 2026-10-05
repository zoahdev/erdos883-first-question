import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_2 :
    (List.ofFn coreChunks419_2).flatten =
      (coreData419.take (coreResources419 2).q).drop 41 := by
  decide +kernel

theorem coreCheck419_2 :
    ∀ c : Fin 1, (coreChunks419_2 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 2)) = true := by
  decide +kernel
#print axioms coreFlatten419_2
#print axioms coreCheck419_2
end Erdos883Verified
