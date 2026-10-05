import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_21 :
    (List.ofFn coreChunks258_21).flatten =
      (coreData258.take (coreResources258 21).q).drop 49 := by
  decide +kernel

theorem coreCheck258_21 :
    ∀ c : Fin 1, (coreChunks258_21 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 21)) = true := by
  decide +kernel
#print axioms coreFlatten258_21
#print axioms coreCheck258_21
end Erdos883Verified
