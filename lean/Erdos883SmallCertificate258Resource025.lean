import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_25 :
    (List.ofFn coreChunks258_25).flatten =
      (coreData258.take (coreResources258 25).q).drop 55 := by
  decide +kernel

theorem coreCheck258_25 :
    ∀ c : Fin 1, (coreChunks258_25 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 25)) = true := by
  decide +kernel
#print axioms coreFlatten258_25
#print axioms coreCheck258_25
end Erdos883Verified
