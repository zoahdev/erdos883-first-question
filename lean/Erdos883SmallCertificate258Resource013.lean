import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_13 :
    (List.ofFn coreChunks258_13).flatten =
      (coreData258.take (coreResources258 13).q).drop 0 := by
  decide +kernel

theorem coreCheck258_13 :
    ∀ c : Fin 3, (coreChunks258_13 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 13)) = true := by
  decide +kernel
#print axioms coreFlatten258_13
#print axioms coreCheck258_13
end Erdos883Verified
