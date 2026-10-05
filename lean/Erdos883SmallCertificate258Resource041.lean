import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_41 :
    (List.ofFn coreChunks258_41).flatten =
      (coreData258.take (coreResources258 41).q).drop 98 := by
  decide +kernel

theorem coreCheck258_41 :
    ∀ c : Fin 1, (coreChunks258_41 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 41)) = true := by
  decide +kernel
#print axioms coreFlatten258_41
#print axioms coreCheck258_41
end Erdos883Verified
