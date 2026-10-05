import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_12 :
    (List.ofFn coreChunks258_12).flatten =
      (coreData258.take (coreResources258 12).q).drop 65 := by
  decide +kernel

theorem coreCheck258_12 :
    ∀ c : Fin 1, (coreChunks258_12 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 12)) = true := by
  decide +kernel
#print axioms coreFlatten258_12
#print axioms coreCheck258_12
end Erdos883Verified
