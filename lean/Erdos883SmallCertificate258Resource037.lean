import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_37 :
    (List.ofFn coreChunks258_37).flatten =
      (coreData258.take (coreResources258 37).q).drop 79 := by
  decide +kernel

theorem coreCheck258_37 :
    ∀ c : Fin 1, (coreChunks258_37 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 37)) = true := by
  decide +kernel
#print axioms coreFlatten258_37
#print axioms coreCheck258_37
end Erdos883Verified
