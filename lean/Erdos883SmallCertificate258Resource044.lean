import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_44 :
    (List.ofFn coreChunks258_44).flatten =
      (coreData258.take (coreResources258 44).q).drop 124 := by
  decide +kernel

theorem coreCheck258_44 :
    ∀ c : Fin 1, (coreChunks258_44 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 44)) = true := by
  decide +kernel
#print axioms coreFlatten258_44
#print axioms coreCheck258_44
end Erdos883Verified
