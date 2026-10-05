import Erdos883SmallCertificate258Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten258_45 :
    (List.ofFn coreChunks258_45).flatten =
      (coreData258.take (coreResources258 45).q).drop 0 := by
  decide +kernel

theorem coreCheck258_45 :
    ∀ c : Fin 7, (coreChunks258_45 c).all
      (coreResourceRowCheck 235 coreData258 (coreResources258 45)) = true := by
  decide +kernel
#print axioms coreFlatten258_45
#print axioms coreCheck258_45
end Erdos883Verified
