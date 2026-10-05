import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_0 :
    (List.ofFn coreChunks258_0).flatten =
      (coreData258.take (coreResources258 0).q).drop 0 := by
  decide +kernel

theorem coreCheck258_0 :
    ∀ c : Fin 2, (coreChunks258_0 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 0)) = true := by
  decide +kernel
#print axioms coreFlatten258_0
#print axioms coreCheck258_0
end Erdos883Verified
