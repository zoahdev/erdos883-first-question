import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_47 :
    (List.ofFn coreChunks258_47).flatten =
      (coreData258.take (coreResources258 47).q).drop 83 := by
  decide +kernel

theorem coreCheck258_47 :
    ∀ c : Fin 1, (coreChunks258_47 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 47)) = true := by
  decide +kernel
#print axioms coreFlatten258_47
#print axioms coreCheck258_47
end Erdos883Verified
