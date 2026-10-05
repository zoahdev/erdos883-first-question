import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_63 :
    (List.ofFn coreChunks419_63).flatten =
      (coreData419.take (coreResources419 63).q).drop 129 := by
  decide +kernel

theorem coreCheck419_63 :
    ∀ c : Fin 1, (coreChunks419_63 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 63)) = true := by
  decide +kernel
#print axioms coreFlatten419_63
#print axioms coreCheck419_63
end Erdos883Verified
