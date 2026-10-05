import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_10 :
    (List.ofFn coreChunks258_10).flatten =
      (coreData258.take (coreResources258 10).q).drop 63 := by
  decide +kernel

theorem coreCheck258_10 :
    ∀ c : Fin 1, (coreChunks258_10 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 10)) = true := by
  decide +kernel
#print axioms coreFlatten258_10
#print axioms coreCheck258_10
end Erdos883Verified
