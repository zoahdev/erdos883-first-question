import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_34 :
    (List.ofFn coreChunks258_34).flatten =
      (coreData258.take (coreResources258 34).q).drop 71 := by
  decide +kernel

theorem coreCheck258_34 :
    ∀ c : Fin 1, (coreChunks258_34 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 34)) = true := by
  decide +kernel
#print axioms coreFlatten258_34
#print axioms coreCheck258_34
end Erdos883Verified
