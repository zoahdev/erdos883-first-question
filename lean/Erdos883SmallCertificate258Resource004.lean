import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_4 :
    (List.ofFn coreChunks258_4).flatten =
      (coreData258.take (coreResources258 4).q).drop 55 := by
  decide +kernel

theorem coreCheck258_4 :
    ∀ c : Fin 1, (coreChunks258_4 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 4)) = true := by
  decide +kernel
#print axioms coreFlatten258_4
#print axioms coreCheck258_4
end Erdos883Verified
