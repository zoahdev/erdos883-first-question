import Erdos883SmallCertificate419Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten419_73 :
    (List.ofFn coreChunks419_73).flatten =
      (coreData419.take (coreResources419 73).q).drop 181 := by
  decide +kernel

theorem coreCheck419_73 :
    ∀ c : Fin 2, (coreChunks419_73 c).all
      (coreResourceRowCheck 381 coreData419 (coreResources419 73)) = true := by
  decide +kernel
#print axioms coreFlatten419_73
#print axioms coreCheck419_73
end Erdos883Verified
