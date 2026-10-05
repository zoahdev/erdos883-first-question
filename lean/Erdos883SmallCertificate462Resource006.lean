import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_6 :
    (List.ofFn coreChunks462_6).flatten =
      (coreData462.take (coreResources462 6).q).drop 87 := by
  decide +kernel

theorem coreCheck462_6 :
    ∀ c : Fin 1, (coreChunks462_6 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 6)) = true := by
  decide +kernel
#print axioms coreFlatten462_6
#print axioms coreCheck462_6
end Erdos883Verified
