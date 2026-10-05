import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_51 :
    (List.ofFn coreChunks419_51).flatten =
      (coreData419.take (coreResources419 51).q).drop 101 := by
  decide +kernel

theorem coreCheck419_51 :
    ∀ c : Fin 1, (coreChunks419_51 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 51)) = true := by
  decide +kernel
#print axioms coreFlatten419_51
#print axioms coreCheck419_51
end Erdos883Verified
