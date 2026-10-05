import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_46 :
    (List.ofFn coreChunks258_46).flatten =
      (coreData258.take (coreResources258 46).q).drop 0 := by
  decide +kernel

theorem coreCheck258_46 :
    ∀ c : Fin 6, (coreChunks258_46 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 46)) = true := by
  decide +kernel
#print axioms coreFlatten258_46
#print axioms coreCheck258_46
end Erdos883Verified
