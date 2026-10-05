import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_30 :
    (List.ofFn coreChunks462_30).flatten =
      (coreData462.take (coreResources462 30).q).drop 64 := by
  decide +kernel

theorem coreCheck462_30 :
    ∀ c : Fin 1, (coreChunks462_30 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 30)) = true := by
  decide +kernel
#print axioms coreFlatten462_30
#print axioms coreCheck462_30
end Erdos883Verified
