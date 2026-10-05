import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_52 :
    (List.ofFn coreChunks419_52).flatten =
      (coreData419.take (coreResources419 52).q).drop 104 := by
  decide +kernel

theorem coreCheck419_52 :
    ∀ c : Fin 1, (coreChunks419_52 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 52)) = true := by
  decide +kernel
#print axioms coreFlatten419_52
#print axioms coreCheck419_52
end Erdos883Verified
