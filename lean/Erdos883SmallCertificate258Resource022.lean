import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_22 :
    (List.ofFn coreChunks258_22).flatten =
      (coreData258.take (coreResources258 22).q).drop 50 := by
  decide +kernel

theorem coreCheck258_22 :
    ∀ c : Fin 1, (coreChunks258_22 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 22)) = true := by
  decide +kernel
#print axioms coreFlatten258_22
#print axioms coreCheck258_22
end Erdos883Verified
