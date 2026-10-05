import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_54 :
    (List.ofFn coreChunks462_54).flatten =
      (coreData462.take (coreResources462 54).q).drop 102 := by
  decide +kernel

theorem coreCheck462_54 :
    ∀ c : Fin 1, (coreChunks462_54 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 54)) = true := by
  decide +kernel
#print axioms coreFlatten462_54
#print axioms coreCheck462_54
end Erdos883Verified
