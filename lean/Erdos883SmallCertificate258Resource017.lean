import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_17 :
    (List.ofFn coreChunks258_17).flatten =
      (coreData258.take (coreResources258 17).q).drop 45 := by
  decide +kernel

theorem coreCheck258_17 :
    ∀ c : Fin 1, (coreChunks258_17 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 17)) = true := by
  decide +kernel
#print axioms coreFlatten258_17
#print axioms coreCheck258_17
end Erdos883Verified
