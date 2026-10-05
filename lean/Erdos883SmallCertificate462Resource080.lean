import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_80 :
    (List.ofFn coreChunks462_80).flatten =
      (coreData462.take (coreResources462 80).q).drop 190 := by
  decide +kernel

theorem coreCheck462_80 :
    ∀ c : Fin 1, (coreChunks462_80 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 80)) = true := by
  decide +kernel
#print axioms coreFlatten462_80
#print axioms coreCheck462_80
end Erdos883Verified
