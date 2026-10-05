import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_14 :
    (List.ofFn coreChunks258_14).flatten =
      (coreData258.take (coreResources258 14).q).drop 40 := by
  decide +kernel

theorem coreCheck258_14 :
    ∀ c : Fin 1, (coreChunks258_14 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 14)) = true := by
  decide +kernel
#print axioms coreFlatten258_14
#print axioms coreCheck258_14
end Erdos883Verified
