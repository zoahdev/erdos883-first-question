import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_2 :
    (List.ofFn coreChunks258_2).flatten =
      (coreData258.take (coreResources258 2).q).drop 27 := by
  decide +kernel

theorem coreCheck258_2 :
    ∀ c : Fin 1, (coreChunks258_2 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 2)) = true := by
  decide +kernel
#print axioms coreFlatten258_2
#print axioms coreCheck258_2
end Erdos883Verified
