import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_32 :
    (List.ofFn coreChunks258_32).flatten =
      (coreData258.take (coreResources258 32).q).drop 67 := by
  decide +kernel

theorem coreCheck258_32 :
    ∀ c : Fin 1, (coreChunks258_32 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 32)) = true := by
  decide +kernel
#print axioms coreFlatten258_32
#print axioms coreCheck258_32
end Erdos883Verified
