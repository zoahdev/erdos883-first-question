import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_19 :
    (List.ofFn coreChunks258_19).flatten =
      (coreData258.take (coreResources258 19).q).drop 47 := by
  decide +kernel

theorem coreCheck258_19 :
    ∀ c : Fin 1, (coreChunks258_19 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 19)) = true := by
  decide +kernel
#print axioms coreFlatten258_19
#print axioms coreCheck258_19
end Erdos883Verified
