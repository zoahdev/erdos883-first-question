import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_23 :
    (List.ofFn coreChunks258_23).flatten =
      (coreData258.take (coreResources258 23).q).drop 52 := by
  decide +kernel

theorem coreCheck258_23 :
    ∀ c : Fin 1, (coreChunks258_23 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 23)) = true := by
  decide +kernel
#print axioms coreFlatten258_23
#print axioms coreCheck258_23
end Erdos883Verified
