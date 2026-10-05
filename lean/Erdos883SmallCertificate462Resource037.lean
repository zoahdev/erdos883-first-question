import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_37 :
    (List.ofFn coreChunks462_37).flatten =
      (coreData462.take (coreResources462 37).q).drop 79 := by
  decide +kernel

theorem coreCheck462_37 :
    ∀ c : Fin 1, (coreChunks462_37 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 37)) = true := by
  decide +kernel
#print axioms coreFlatten462_37
#print axioms coreCheck462_37
end Erdos883Verified
