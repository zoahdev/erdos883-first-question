import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_71 :
    (List.ofFn coreChunks419_71).flatten =
      (coreData419.take (coreResources419 71).q).drop 178 := by
  decide +kernel

theorem coreCheck419_71 :
    ∀ c : Fin 1, (coreChunks419_71 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 71)) = true := by
  decide +kernel
#print axioms coreFlatten419_71
#print axioms coreCheck419_71
end Erdos883Verified
