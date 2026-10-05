import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_9 :
    (List.ofFn coreChunks258_9).flatten =
      (coreData258.take (coreResources258 9).q).drop 62 := by
  decide +kernel

theorem coreCheck258_9 :
    ∀ c : Fin 1, (coreChunks258_9 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 9)) = true := by
  decide +kernel
#print axioms coreFlatten258_9
#print axioms coreCheck258_9
end Erdos883Verified
