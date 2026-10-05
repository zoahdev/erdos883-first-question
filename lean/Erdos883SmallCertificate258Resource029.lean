import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_29 :
    (List.ofFn coreChunks258_29).flatten =
      (coreData258.take (coreResources258 29).q).drop 63 := by
  decide +kernel

theorem coreCheck258_29 :
    ∀ c : Fin 1, (coreChunks258_29 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 29)) = true := by
  decide +kernel
#print axioms coreFlatten258_29
#print axioms coreCheck258_29
end Erdos883Verified
