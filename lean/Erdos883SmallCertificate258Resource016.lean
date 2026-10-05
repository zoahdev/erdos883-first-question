import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_16 :
    (List.ofFn coreChunks258_16).flatten =
      (coreData258.take (coreResources258 16).q).drop 44 := by
  decide +kernel

theorem coreCheck258_16 :
    ∀ c : Fin 1, (coreChunks258_16 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 16)) = true := by
  decide +kernel
#print axioms coreFlatten258_16
#print axioms coreCheck258_16
end Erdos883Verified
