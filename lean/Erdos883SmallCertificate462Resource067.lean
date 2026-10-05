import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_67 :
    (List.ofFn coreChunks462_67).flatten =
      (coreData462.take (coreResources462 67).q).drop 124 := by
  decide +kernel

theorem coreCheck462_67 :
    ∀ c : Fin 1, (coreChunks462_67 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 67)) = true := by
  decide +kernel
#print axioms coreFlatten462_67
#print axioms coreCheck462_67
end Erdos883Verified
