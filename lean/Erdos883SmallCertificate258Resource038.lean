import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_38 :
    (List.ofFn coreChunks258_38).flatten =
      (coreData258.take (coreResources258 38).q).drop 81 := by
  decide +kernel

theorem coreCheck258_38 :
    ∀ c : Fin 1, (coreChunks258_38 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 38)) = true := by
  decide +kernel
#print axioms coreFlatten258_38
#print axioms coreCheck258_38
end Erdos883Verified
