import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_30 :
    (List.ofFn coreChunks258_30).flatten =
      (coreData258.take (coreResources258 30).q).drop 64 := by
  decide +kernel

theorem coreCheck258_30 :
    ∀ c : Fin 1, (coreChunks258_30 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 30)) = true := by
  decide +kernel
#print axioms coreFlatten258_30
#print axioms coreCheck258_30
end Erdos883Verified
