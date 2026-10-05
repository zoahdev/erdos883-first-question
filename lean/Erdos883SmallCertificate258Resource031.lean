import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_31 :
    (List.ofFn coreChunks258_31).flatten =
      (coreData258.take (coreResources258 31).q).drop 65 := by
  decide +kernel

theorem coreCheck258_31 :
    ∀ c : Fin 1, (coreChunks258_31 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 31)) = true := by
  decide +kernel
#print axioms coreFlatten258_31
#print axioms coreCheck258_31
end Erdos883Verified
