import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_18 :
    (List.ofFn coreChunks258_18).flatten =
      (coreData258.take (coreResources258 18).q).drop 46 := by
  decide +kernel

theorem coreCheck258_18 :
    ∀ c : Fin 1, (coreChunks258_18 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 18)) = true := by
  decide +kernel
#print axioms coreFlatten258_18
#print axioms coreCheck258_18
end Erdos883Verified
