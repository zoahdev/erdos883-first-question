import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_8 :
    (List.ofFn coreChunks258_8).flatten =
      (coreData258.take (coreResources258 8).q).drop 61 := by
  decide +kernel

theorem coreCheck258_8 :
    ∀ c : Fin 1, (coreChunks258_8 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 8)) = true := by
  decide +kernel
#print axioms coreFlatten258_8
#print axioms coreCheck258_8
end Erdos883Verified
