import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_55 :
    (List.ofFn coreChunks462_55).flatten =
      (coreData462.take (coreResources462 55).q).drop 103 := by
  decide +kernel

theorem coreCheck462_55 :
    ∀ c : Fin 1, (coreChunks462_55 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 55)) = true := by
  decide +kernel
#print axioms coreFlatten462_55
#print axioms coreCheck462_55
end Erdos883Verified
