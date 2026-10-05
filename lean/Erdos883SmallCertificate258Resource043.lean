import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_43 :
    (List.ofFn coreChunks258_43).flatten =
      (coreData258.take (coreResources258 43).q).drop 111 := by
  decide +kernel

theorem coreCheck258_43 :
    ∀ c : Fin 1, (coreChunks258_43 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 43)) = true := by
  decide +kernel
#print axioms coreFlatten258_43
#print axioms coreCheck258_43
end Erdos883Verified
