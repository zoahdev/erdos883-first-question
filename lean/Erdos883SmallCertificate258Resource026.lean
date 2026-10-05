import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_26 :
    (List.ofFn coreChunks258_26).flatten =
      (coreData258.take (coreResources258 26).q).drop 57 := by
  decide +kernel

theorem coreCheck258_26 :
    ∀ c : Fin 1, (coreChunks258_26 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 26)) = true := by
  decide +kernel
#print axioms coreFlatten258_26
#print axioms coreCheck258_26
end Erdos883Verified
