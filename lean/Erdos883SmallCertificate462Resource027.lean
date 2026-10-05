import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_27 :
    (List.ofFn coreChunks462_27).flatten =
      (coreData462.take (coreResources462 27).q).drop 116 := by
  decide +kernel

theorem coreCheck462_27 :
    ∀ c : Fin 1, (coreChunks462_27 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 27)) = true := by
  decide +kernel
#print axioms coreFlatten462_27
#print axioms coreCheck462_27
end Erdos883Verified
