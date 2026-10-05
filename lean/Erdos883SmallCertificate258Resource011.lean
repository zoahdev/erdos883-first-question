import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_11 :
    (List.ofFn coreChunks258_11).flatten =
      (coreData258.take (coreResources258 11).q).drop 64 := by
  decide +kernel

theorem coreCheck258_11 :
    ∀ c : Fin 1, (coreChunks258_11 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 11)) = true := by
  decide +kernel
#print axioms coreFlatten258_11
#print axioms coreCheck258_11
end Erdos883Verified
