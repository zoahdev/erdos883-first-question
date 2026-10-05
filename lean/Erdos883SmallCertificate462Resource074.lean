import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_74 :
    (List.ofFn coreChunks462_74).flatten =
      (coreData462.take (coreResources462 74).q).drop 143 := by
  decide +kernel

theorem coreCheck462_74 :
    ∀ c : Fin 1, (coreChunks462_74 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 74)) = true := by
  decide +kernel
#print axioms coreFlatten462_74
#print axioms coreCheck462_74
end Erdos883Verified
