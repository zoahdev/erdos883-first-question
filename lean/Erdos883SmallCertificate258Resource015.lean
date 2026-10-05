import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_15 :
    (List.ofFn coreChunks258_15).flatten =
      (coreData258.take (coreResources258 15).q).drop 41 := by
  decide +kernel

theorem coreCheck258_15 :
    ∀ c : Fin 1, (coreChunks258_15 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 15)) = true := by
  decide +kernel
#print axioms coreFlatten258_15
#print axioms coreCheck258_15
end Erdos883Verified
