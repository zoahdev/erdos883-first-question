import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_7 :
    (List.ofFn coreChunks258_7).flatten =
      (coreData258.take (coreResources258 7).q).drop 60 := by
  decide +kernel

theorem coreCheck258_7 :
    ∀ c : Fin 1, (coreChunks258_7 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 7)) = true := by
  decide +kernel
#print axioms coreFlatten258_7
#print axioms coreCheck258_7
end Erdos883Verified
