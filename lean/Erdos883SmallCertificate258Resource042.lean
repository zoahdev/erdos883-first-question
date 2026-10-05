import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_42 :
    (List.ofFn coreChunks258_42).flatten =
      (coreData258.take (coreResources258 42).q).drop 104 := by
  decide +kernel

theorem coreCheck258_42 :
    ∀ c : Fin 1, (coreChunks258_42 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 42)) = true := by
  decide +kernel
#print axioms coreFlatten258_42
#print axioms coreCheck258_42
end Erdos883Verified
