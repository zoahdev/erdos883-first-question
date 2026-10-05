import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_46 :
    (List.ofFn coreChunks419_46).flatten =
      (coreData419.take (coreResources419 46).q).drop 91 := by
  decide +kernel

theorem coreCheck419_46 :
    ∀ c : Fin 1, (coreChunks419_46 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 46)) = true := by
  decide +kernel
#print axioms coreFlatten419_46
#print axioms coreCheck419_46
end Erdos883Verified
