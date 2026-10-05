import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_82 :
    (List.ofFn coreChunks462_82).flatten =
      (coreData462.take (coreResources462 82).q).drop 193 := by
  decide +kernel

theorem coreCheck462_82 :
    ∀ c : Fin 1, (coreChunks462_82 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 82)) = true := by
  decide +kernel
#print axioms coreFlatten462_82
#print axioms coreCheck462_82
end Erdos883Verified
