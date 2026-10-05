import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_75 :
    (List.ofFn coreChunks462_75).flatten =
      (coreData462.take (coreResources462 75).q).drop 145 := by
  decide +kernel

theorem coreCheck462_75 :
    ∀ c : Fin 1, (coreChunks462_75 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 75)) = true := by
  decide +kernel
#print axioms coreFlatten462_75
#print axioms coreCheck462_75
end Erdos883Verified
