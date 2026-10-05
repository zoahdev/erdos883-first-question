import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_6 :
    (List.ofFn coreChunks258_6).flatten =
      (coreData258.take (coreResources258 6).q).drop 58 := by
  decide +kernel

theorem coreCheck258_6 :
    ∀ c : Fin 1, (coreChunks258_6 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 6)) = true := by
  decide +kernel
#print axioms coreFlatten258_6
#print axioms coreCheck258_6
end Erdos883Verified
