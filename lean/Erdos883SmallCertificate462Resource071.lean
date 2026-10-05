import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_71 :
    (List.ofFn coreChunks462_71).flatten =
      (coreData462.take (coreResources462 71).q).drop 137 := by
  decide +kernel

theorem coreCheck462_71 :
    ∀ c : Fin 1, (coreChunks462_71 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 71)) = true := by
  decide +kernel
#print axioms coreFlatten462_71
#print axioms coreCheck462_71
end Erdos883Verified
