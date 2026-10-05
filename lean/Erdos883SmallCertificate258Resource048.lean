import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_48 :
    (List.ofFn coreChunks258_48).flatten =
      (coreData258.take (coreResources258 48).q).drop 0 := by
  decide +kernel

theorem coreCheck258_48 :
    ∀ c : Fin 5, (coreChunks258_48 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 48)) = true := by
  decide +kernel
#print axioms coreFlatten258_48
#print axioms coreCheck258_48
end Erdos883Verified
