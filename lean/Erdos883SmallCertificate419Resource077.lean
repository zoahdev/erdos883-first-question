import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_77 :
    (List.ofFn coreChunks419_77).flatten =
      (coreData419.take (coreResources419 77).q).drop 136 := by
  decide +kernel

theorem coreCheck419_77 :
    ∀ c : Fin 1, (coreChunks419_77 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 77)) = true := by
  decide +kernel
#print axioms coreFlatten419_77
#print axioms coreCheck419_77
end Erdos883Verified
