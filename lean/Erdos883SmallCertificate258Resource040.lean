import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_40 :
    (List.ofFn coreChunks258_40).flatten =
      (coreData258.take (coreResources258 40).q).drop 91 := by
  decide +kernel

theorem coreCheck258_40 :
    ∀ c : Fin 1, (coreChunks258_40 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 40)) = true := by
  decide +kernel
#print axioms coreFlatten258_40
#print axioms coreCheck258_40
end Erdos883Verified
