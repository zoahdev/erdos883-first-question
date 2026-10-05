import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_76 :
    (List.ofFn coreChunks419_76).flatten =
      (coreData419.take (coreResources419 76).q).drop 134 := by
  decide +kernel

theorem coreCheck419_76 :
    ∀ c : Fin 1, (coreChunks419_76 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 76)) = true := by
  decide +kernel
#print axioms coreFlatten419_76
#print axioms coreCheck419_76
end Erdos883Verified
