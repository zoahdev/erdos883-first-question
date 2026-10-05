import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_49 :
    (List.ofFn coreChunks258_49).flatten =
      (coreData258.take (coreResources258 49).q).drop 0 := by
  decide +kernel

theorem coreCheck258_49 :
    ∀ c : Fin 5, (coreChunks258_49 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 49)) = true := by
  decide +kernel
#print axioms coreFlatten258_49
#print axioms coreCheck258_49
end Erdos883Verified
