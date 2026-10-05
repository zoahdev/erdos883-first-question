import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_3 :
    (List.ofFn coreChunks258_3).flatten =
      (coreData258.take (coreResources258 3).q).drop 35 := by
  decide +kernel

theorem coreCheck258_3 :
    ∀ c : Fin 2, (coreChunks258_3 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 3)) = true := by
  decide +kernel
#print axioms coreFlatten258_3
#print axioms coreCheck258_3
end Erdos883Verified
