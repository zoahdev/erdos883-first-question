import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_83 :
    (List.ofFn coreChunks462_83).flatten =
      (coreData462.take (coreResources462 83).q).drop 198 := by
  decide +kernel

theorem coreCheck462_83 :
    ∀ c : Fin 1, (coreChunks462_83 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 83)) = true := by
  decide +kernel
#print axioms coreFlatten462_83
#print axioms coreCheck462_83
end Erdos883Verified
