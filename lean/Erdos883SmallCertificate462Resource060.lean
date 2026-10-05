import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_60 :
    (List.ofFn coreChunks462_60).flatten =
      (coreData462.take (coreResources462 60).q).drop 112 := by
  decide +kernel

theorem coreCheck462_60 :
    ∀ c : Fin 1, (coreChunks462_60 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 60)) = true := by
  decide +kernel
#print axioms coreFlatten462_60
#print axioms coreCheck462_60
end Erdos883Verified
