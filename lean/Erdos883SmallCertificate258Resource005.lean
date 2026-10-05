import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_5 :
    (List.ofFn coreChunks258_5).flatten =
      (coreData258.take (coreResources258 5).q).drop 57 := by
  decide +kernel

theorem coreCheck258_5 :
    ∀ c : Fin 1, (coreChunks258_5 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 5)) = true := by
  decide +kernel
#print axioms coreFlatten258_5
#print axioms coreCheck258_5
end Erdos883Verified
