import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_24 :
    (List.ofFn coreChunks258_24).flatten =
      (coreData258.take (coreResources258 24).q).drop 54 := by
  decide +kernel

theorem coreCheck258_24 :
    ∀ c : Fin 1, (coreChunks258_24 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 24)) = true := by
  decide +kernel
#print axioms coreFlatten258_24
#print axioms coreCheck258_24
end Erdos883Verified
