import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_1 :
    (List.ofFn coreChunks258_1).flatten =
      (coreData258.take (coreResources258 1).q).drop 26 := by
  decide +kernel

theorem coreCheck258_1 :
    ∀ c : Fin 1, (coreChunks258_1 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 1)) = true := by
  decide +kernel
#print axioms coreFlatten258_1
#print axioms coreCheck258_1
end Erdos883Verified
