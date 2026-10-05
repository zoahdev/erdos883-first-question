import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_33 :
    (List.ofFn coreChunks258_33).flatten =
      (coreData258.take (coreResources258 33).q).drop 70 := by
  decide +kernel

theorem coreCheck258_33 :
    ∀ c : Fin 1, (coreChunks258_33 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 33)) = true := by
  decide +kernel
#print axioms coreFlatten258_33
#print axioms coreCheck258_33
end Erdos883Verified
