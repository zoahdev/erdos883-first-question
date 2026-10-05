import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_47 :
    (List.ofFn coreChunks419_47).flatten =
      (coreData419.take (coreResources419 47).q).drop 93 := by
  decide +kernel

theorem coreCheck419_47 :
    ∀ c : Fin 1, (coreChunks419_47 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 47)) = true := by
  decide +kernel
#print axioms coreFlatten419_47
#print axioms coreCheck419_47
end Erdos883Verified
