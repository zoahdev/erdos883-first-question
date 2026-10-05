import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_32 :
    (List.ofFn coreChunks419_32).flatten =
      (coreData419.take (coreResources419 32).q).drop 71 := by
  decide +kernel

theorem coreCheck419_32 :
    ∀ c : Fin 1, (coreChunks419_32 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 32)) = true := by
  decide +kernel
#print axioms coreFlatten419_32
#print axioms coreCheck419_32
end Erdos883Verified
