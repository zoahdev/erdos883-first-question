import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_65 :
    (List.ofFn coreChunks419_65).flatten =
      (coreData419.take (coreResources419 65).q).drop 132 := by
  decide +kernel

theorem coreCheck419_65 :
    ∀ c : Fin 1, (coreChunks419_65 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 65)) = true := by
  decide +kernel
#print axioms coreFlatten419_65
#print axioms coreCheck419_65
end Erdos883Verified
