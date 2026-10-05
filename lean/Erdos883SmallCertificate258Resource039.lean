import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_39 :
    (List.ofFn coreChunks258_39).flatten =
      (coreData258.take (coreResources258 39).q).drop 86 := by
  decide +kernel

theorem coreCheck258_39 :
    ∀ c : Fin 1, (coreChunks258_39 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 39)) = true := by
  decide +kernel
#print axioms coreFlatten258_39
#print axioms coreCheck258_39
end Erdos883Verified
