import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_27 :
    (List.ofFn coreChunks258_27).flatten =
      (coreData258.take (coreResources258 27).q).drop 61 := by
  decide +kernel

theorem coreCheck258_27 :
    ∀ c : Fin 1, (coreChunks258_27 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 27)) = true := by
  decide +kernel
#print axioms coreFlatten258_27
#print axioms coreCheck258_27
end Erdos883Verified
