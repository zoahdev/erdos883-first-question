import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_50 :
    (List.ofFn coreChunks258_50).flatten =
      (coreData258.take (coreResources258 50).q).drop 74 := by
  decide +kernel

theorem coreCheck258_50 :
    ∀ c : Fin 1, (coreChunks258_50 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 50)) = true := by
  decide +kernel
#print axioms coreFlatten258_50
#print axioms coreCheck258_50
end Erdos883Verified
