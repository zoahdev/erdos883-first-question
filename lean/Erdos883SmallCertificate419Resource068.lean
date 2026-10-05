import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_68 :
    (List.ofFn coreChunks419_68).flatten =
      (coreData419.take (coreResources419 68).q).drop 154 := by
  decide +kernel

theorem coreCheck419_68 :
    ∀ c : Fin 1, (coreChunks419_68 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 68)) = true := by
  decide +kernel
#print axioms coreFlatten419_68
#print axioms coreCheck419_68
end Erdos883Verified
