import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_36 :
    (List.ofFn coreChunks258_36).flatten =
      (coreData258.take (coreResources258 36).q).drop 77 := by
  decide +kernel

theorem coreCheck258_36 :
    ∀ c : Fin 1, (coreChunks258_36 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 36)) = true := by
  decide +kernel
#print axioms coreFlatten258_36
#print axioms coreCheck258_36
end Erdos883Verified
