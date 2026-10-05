import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_28 :
    (List.ofFn coreChunks258_28).flatten =
      (coreData258.take (coreResources258 28).q).drop 62 := by
  decide +kernel

theorem coreCheck258_28 :
    ∀ c : Fin 1, (coreChunks258_28 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 28)) = true := by
  decide +kernel
#print axioms coreFlatten258_28
#print axioms coreCheck258_28
end Erdos883Verified
