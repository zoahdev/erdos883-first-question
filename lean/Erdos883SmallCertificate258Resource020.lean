import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_20 :
    (List.ofFn coreChunks258_20).flatten =
      (coreData258.take (coreResources258 20).q).drop 48 := by
  decide +kernel

theorem coreCheck258_20 :
    ∀ c : Fin 1, (coreChunks258_20 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 20)) = true := by
  decide +kernel
#print axioms coreFlatten258_20
#print axioms coreCheck258_20
end Erdos883Verified
