import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_35 :
    (List.ofFn coreChunks258_35).flatten =
      (coreData258.take (coreResources258 35).q).drop 75 := by
  decide +kernel

theorem coreCheck258_35 :
    ∀ c : Fin 1, (coreChunks258_35 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 35)) = true := by
  decide +kernel
#print axioms coreFlatten258_35
#print axioms coreCheck258_35
end Erdos883Verified
